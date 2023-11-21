#!/usr/bin/python3

import inspect
import io
import os
import re
import sys
import traceback
import multiprocessing
import numpy as np
try: import z3
except ModuleNotFoundError: pass
import argparse

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.join(currentdir, "utils"))
from parse import Parser, parse, Node, NodeType, NodeState
from node import mod_red, popcount
from simplify import simplify_linear_mba, compute_bitwise_complexity

# Verify that the original expression and the simplified one are equivalent
# using Z3.
def verify_using_z3(orig, simpl, bitCount, timeout=None):
    if simpl == orig: return True

    if "**" in orig or "**" in simpl:
        print("*** Z3 verification not possible due to occuring powers!")
        return False

    tOrig = parse(orig, bitCount, True, False, False)
    tSimpl = parse(simpl, bitCount, True, False, False)
    if tOrig == None or tSimpl == None:
        sys.exit("Error at parsing in verify_using_z3()!")

    # Collect all variables at once in order to ensure consistent numbering.
    variables = []
    tOrig.collect_variables(variables)
    tSimpl.collect_variables(variables)

    # Enumerate them.
    tOrig.enumerate_variables(variables)
    tSimpl.enumerate_variables(variables)

    tmpVars = ["Y[" + str(i) + "]" for i in range(len(variables))]
    # The expressions with their variables replaced by temporary ones.
    orig = tOrig.to_string(False, -1, tmpVars)
    simpl = tSimpl.to_string(False, -1, tmpVars)

    Y = [z3.BitVec(v, bitCount) for v in tmpVars]

    modulus = 2**bitCount
    exprEval = eval("(" + orig + ") % " + str(modulus))
    simplEval = eval("(" + simpl + ") % " + str(modulus))

    solver = z3.Solver()
    if timeout != None: solver.set("timeout", timeout)
    solver.add(exprEval != simplEval)

    print("*** ... start Z3 verification ...")
    result = solver.check()
    print("*** ... Z3 verification result: " + str(result))

    return str(result) == "unsat"


# The main simplification class which stores relevant parameters such as the
# number of bits.
class GeneralSimplifier():
    def __init__(self, bitCount, modRed=False, verifBitCount=None):
        self.__bitCount = bitCount
        self.__modulus = 2**bitCount
        self.__modRed = modRed
        self.__verifBitCount = verifBitCount
        self.__vnumber = 0
        self.__variables = []
        self.__MAX_IT = 100
        self.__VNAME_PREFIX = "Y["
        self.__VNAME_SUFFIX = "]"

    # Get the internal name of the variable with given index.
    def __get_vname(self, i):
        return self.__VNAME_PREFIX + str(i) + self.__VNAME_SUFFIX

    # Reduces the given number modulo modulus.
    def __mod_red(self, n):
        return mod_red(n, self.__modulus)

    # Find all variables occuring in the given tree, store them in a list and
    # enumerate the tree's variable nodes accordingly.
    def __collect_and_enumerate_variables(self, tree):
        self.__variables = []
        # Get a list of unique variables.
        tree.collect_and_enumerate_variables(self.__variables)
        self.__vnumber = len(self.__variables)

    # Get the vector storing results of expression evaluation for all truth
    # value combinations, i.e., [e(0,0,...), e(1,0,...), e(0,1,...), e(1,1,...)].
    def __get_result_vector(self, node):
        def f(X): return node.eval(X)

        resultVector = []
        for i in range(2**self.__vnumber):
            n = i
            par = []
            for j in range(self.__vnumber):
                par.append(n & 1)
                n = n >> 1
            resultVector.append(f(par))

        return resultVector

    # Get the group sizes of the various variables, i.e., their numbers of
    # subsequent occurences in the truth table.
    def __get_groupsizes(self):
        groupsizes = [1]
        for i in range(1, self.__vnumber):
            groupsizes.append(2 * groupsizes[-1])

        return groupsizes

    # Returns all sublists of the list [0,...,vnumber-1] ordered by their
    # sizes, whereas each sublist is sorted in increasing order.
    def __get_variable_combinations(self):
        comb = [[v] for v in range(self.__vnumber)]
        new = self.__vnumber

        for count in range(1, self.__vnumber):
            size = len(comb)
            nnew = 0
            for e in comb[size-new:size]:
                for v in range(e[-1] + 1, self.__vnumber):
                    comb.append(e + [v])
                    nnew += 1

            new = nnew

        return comb

    # Get the idx-th base expressions of the space of expressions with vnumber
    # variables.
    def __get_basis_expression(self, idx):
        if idx == 0: return "1"

        res = ""
        for v in range(self.__vnumber):
            if (idx & 1) == 1: res += self.__variables[v] + "&"
            idx >>= 1

        res = res[:-1]
        if res.find('&') != -1: res = "(" + res + ")"
        return res

    # Returns true iff the given variables hold in the result vector's entry
    # with given index.
    def __are_variables_true(self, n, variables):
        prev = 0
        for v in variables:
            n >>= (v - prev)
            prev = v
            if (n & 1) == 0: return False

        return True

    # Subtract the given coefficient from all elements of the result vector
    # which correspond to the same conjunction.
    def __subtract_coefficient(self, resultVector, coeff, firstStart, variables, groupsize):
        period = 2 * groupsize
        for start in range(firstStart, len(resultVector), period):
            for i in range(start, start + groupsize):
                # The first variable is true by design of the for loops.
                if i != firstStart and (len(variables) == 1 or self.__are_variables_true(i, variables[1:])):
                    resultVector[i] -= coeff

    # For the given node, get the coefficients of its linear combination of the
    # base expressions.
    def __get_linear_combination(self, node):
        resultVector = self.__get_result_vector(node)
        l = len(resultVector)

        # The constant term.
        constant = self.__mod_red(resultVector[0])
        for i in range(1, l): resultVector[i] -= constant

        # Determine all conjunctions of variables (including trivial
        # conjunctions of single variables).
        combinations = self.__get_variable_combinations()
        groupsizes = self.__get_groupsizes()
        for comb in combinations:
            index = sum([groupsizes[v] for v in comb])
            coeff = self.__mod_red(resultVector[index])

            if coeff == 0: continue

            self.__subtract_coefficient(resultVector, coeff, index, comb, groupsizes[comb[0]])

        return resultVector

    # Get the given product node's linear combination of basis expressions.
    def __get_product_linear_combination(self, node):
        assert(len(node.children) == 2 or (len(node.children) == 3 and node.children[0].type == NodeType.CONSTANT))

        linCombs = []
        for child in node.children[-2:]:
            linCombs.append(self.__get_linear_combination(child))

        res = np.zeros(2**(2*self.__vnumber-1) + 2**(self.__vnumber-1), dtype=np.uint64)
        baselen = 2**self.__vnumber

        if len(node.children) == 3 and node.children[0].type == NodeType.CONSTANT:
            for i in range(len(linCombs[0])): linCombs[0][i] *= node.children[0].constant

        idx = 0
        for b in range(baselen):
            res[idx] = self.__mod_red(linCombs[0][b] * linCombs[1][b])
            idx += 1

            for a in range(b+1, baselen):
                res[idx] = self.__mod_red(linCombs[0][b] * linCombs[1][a] + linCombs[0][a] * linCombs[1][b])
                idx += 1
        assert(idx == res.size)

        return res

    # Get the given power node's linear combination of basis expressions.
    def __get_power_linear_combination(self, node):
        assert(len(node.children) == 2 or node.type == NodeType.PRODUCT)

        base = node.children[0]
        coeff = 1
        if node.type == NodeType.PRODUCT:
            assert(node.children[0].type == NodeType.CONSTANT)
            assert(node.children[1].type == NodeType.POWER)
            assert(node.children[1].children[1].type == NodeType.CONSTANT)
            assert(node.children[1].children[1].constant == 2)
            base = node.children[1].children[0]
            coeff = node.children[0].constant
        else: assert(node.children[1].constant == 2)

        linComb = self.__get_linear_combination(base)

        res = np.zeros(2**(2*self.__vnumber-1) + 2**(self.__vnumber-1), dtype=np.uint64)
        baselen = 2**self.__vnumber

        idx = 0
        for b in range(baselen):
            res[idx] = self.__mod_red(linComb[b]**2)
            idx += 1

            for a in range(b+1, baselen):
                res[idx] = self.__mod_red(2 * linComb[b] * linComb[a])
                idx += 1
        assert(idx == res.size)

        if coeff != 1:
            for i in range(res.size): res[i] = self.__mod_red(int(res[i]) * coeff)

        return res

    # Find all variables occuring in the given node.
    def __get_occurring_variable_indices(self, node):
        variables = []
        node.collect_variable_indices(variables)
        return variables

    # Try to simplify the given sum node if it has product nodes as children.
    def __try_simplify_sum_nonlinear_part(self, node):
        indices = self.__get_indices_of_simple_nonlinear_products_in_sum(node)
        if len(indices) == 0 or len(indices) == 1: return False

        self.__collect_and_enumerate_variables(node)

        res = np.zeros(2**(2*self.__vnumber-1) + 2**(self.__vnumber-1), dtype=np.uint64)
        for i in indices:
            child = node.children[i]
            if child.type == NodeType.PRODUCT and not child.has_nonlinear_child():
                res += self.__get_product_linear_combination(child)
            else:
                res += self.__get_power_linear_combination(child)
        for i in range(res.size):
            res[i] = self.__mod_red(res[i])

        # TODO: Neglect result if not enough zeros.

        baselen = 2**self.__vnumber

        # Build result
        # TODO: Perform that in node representation.
        simpl = ""
        idx = 0
        for b in range(baselen):
            if res[idx] != 0:
                if res[idx] != 1: simpl += str(res[idx]) + "*"
                simpl += self.__get_basis_expression(b) + "**2+"
            idx += 1

            for a in range(b+1, baselen):
                if res[idx] != 0:
                    if res[idx] != 1: simpl += str(res[idx]) + "*"
                    simpl += self.__get_basis_expression(b) + "*" + self.__get_basis_expression(a) + "+"
                idx += 1
        assert(idx == res.size)

        # Remove '+' at the end.
        if simpl != "": simpl = simpl[:-1]

        for i in sorted(indices[1:], reverse=True): del node.children[i]
        if simpl != "": node.children[indices[0]] = parse(simpl, self.__bitCount, self.__modRed, True, True)
        else: del node.children[indices[0]]

        if len(node.children) == 1: node.copy(node.children[0])
        elif len(node.children) == 0: node.copy(parse("0", self.__bitCount, self.__modRed, True, True))

        return True

    # Returns true iff the given node can be part of a sum that can be
    # simplified.
    def __is_candidate_for_simplification_in_sum(self, node):
        if node.type != NodeType.PRODUCT and node.type != NodeType.POWER: return False
        if node.state != NodeState.NONLINEAR: return False

        if len(node.children) > 2:
            if len(node.children) > 3 or node.children[0].type != NodeType.CONSTANT: return False

        if node.type == NodeType.POWER:
            # TODO: Handle higher exponents.
            if node.children[1].type != NodeType.CONSTANT or node.children[1].constant != 2:
                return False
            if node.children[0].state == NodeState.NONLINEAR or node.children[0].state == NodeState.MIXED:
                return False
        else:
            if node.children[0].type == NodeType.CONSTANT and node.children[1].type == NodeType.POWER:
                if len(node.children) > 2: return False
                return self.__is_candidate_for_simplification_in_sum(node.children[1])
            if node.has_nonlinear_child(): return False

        return True

    # For the given sum node, get the indices of all its children which are
    # product nodes with a suitably small amount of children.
    def __get_indices_of_simple_nonlinear_products_in_sum(self, node):
        assert(node.type == NodeType.SUM)

        if node.linearEnd >= len(node.children) - 1: return []

        indices = []
        for i in range(len(node.children)):
            if self.__is_candidate_for_simplification_in_sum(node.children[i]):
                indices.append(i)

        return indices

    # Simplify the linear part of a nonlinear subexpression corresponding to
    # the given node.
    def __simplify_nonlinear_subexpression_linear_part(self, node):
        subexpr = node.part_to_string(node.linearEnd)
        simpl = simplify_linear_mba(subexpr, self.__bitCount, False, False, self.__modRed)

        if simpl == subexpr: return False

        child = parse(simpl, self.__bitCount, self.__modRed, True, True)

        if child.type == node.type:
            del node.children[:node.linearEnd]
            node.children = child.children + node.children
            node.linearEnd = len(child.children)
        elif simpl == "0":
            assert(node.type != NodeType.POWER)
            # The linear part vanishes.
            if node.type in [NodeType.SUM, NodeType.INCL_DISJUNCTION, NodeType.EXCL_DISJUNCTION]:
                del node.children[:node.linearEnd]
                node.linearEnd = 0
                if len(node.children) == 1: node.copy(node.children[0])
            else:
                assert(node.type in [NodeType.PRODUCT, NodeType.CONJUNCTION])
                # The whole expression is zero.
                node.copy(parse("0", self.__bitCount, self.__modRed, True, True))
        else:
            del node.children[1:node.linearEnd]
            node.children[0] = child
            node.linearEnd = 1

        return True

    # Try to rearrange the given node by expanding products and powers,
    # collecting terms and factorizing.
    def __refactor(self, node):
        orig = str(node)

        node.expand(True)
        node.mark_linear()
        node.factorize_sums(True)
        node.mark_linear()

        return str(node) != orig

    # One step of simplification of the nonlinear subexpression corresponding
    # to the given node.
    def __simplify_nonlinear_subexpression_step(self, node, parent, noRefactor, noSubst):
        assert(not node.is_linear())
        changed = False

        # Simplify the linear part.
        if node.linearEnd > 0:
            ch = self.__simplify_nonlinear_subexpression_linear_part(node)
            if ch: changed = True

        if not noRefactor:
            ch = self.__refactor(node)
            if ch:
                #changed = True
                for child in node.children: self.__simplify_subexpression(child, node)
                node.refine()
                node.mark_linear()

        if not noSubst and node.type != NodeType.NEGATION:
            if self.__simplify_via_substitution(node): changed = True

        return changed

    # Simplify the nonlinear subexpression corresponding to the given node.
    def __simplify_nonlinear_subexpression(self, node, parent, noRefactor=False, noSubst=False):
        prev = {str(node)}
        changed = False

        # If the node is a sum, start simplifying the nonlinear part. This is
        # only done once since the result would always be the same.
        if node.type == NodeType.SUM and self.__try_simplify_sum_nonlinear_part(node):
            node.refine()
            node.mark_linear()
            # If the node became linear, we can use a short cut.
            if node.is_linear():
                self.__simplify_linear_subexpression(node)
                return True
            changed = True
            # Otherwise simplify the children again.
            for child in node.children: self.__simplify_subexpression(child, node)

        # For robustness use a maximum number of iterations.
        for i in range(self.__MAX_IT):
            ch = self.__simplify_nonlinear_subexpression_step(node, parent, noRefactor, noSubst)
            if ch: changed = True

            # If the node became linear due to some simplification, we can use
            # a short cut.
            if node.is_linear():
                self.__simplify_linear_subexpression(node)
                return True

            if not ch: break

            s = str(node)
            if s in prev: break
            prev.add(s)

        return changed

    # Simplify the linear subexpression corresponding to the given node.
    def __simplify_linear_subexpression(self, node):
        subexpr = node.to_string()
        simpl = simplify_linear_mba(subexpr, self.__bitCount, False, False, self.__modRed)
        changed = simpl != subexpr

        if changed: node.copy(parse(simpl, self.__bitCount, self.__modRed, True, True))
        return changed

    # Get a list of nodes whose substitution by variables might make
    # simplification easier.
    def __collect_nodes_for_substitution(self, root):
        nodes = []

        while True:
            node = root.get_node_for_substitution(nodes)

            # No additional node found.
            if node == None: break

            nodes.append(node)

        return nodes

    # Try to simplify the expression further by substituting subexpressions
    # equal to the given node by a variable.
    def __get_simpl_via_substitution_of_nodes(self, node, nodes, onlyFullMatch):
        r = node.get_copy()

        # Avoid using a temporary variable that is already used in the node.
        n = node.get_max_vname(self.__VNAME_PREFIX, self.__VNAME_SUFFIX)
        start = 0 if n == None else n + 1

        for i in range(len(nodes)):
            vname = self.__get_vname(start + i)
            found = r.substitute_all_occurences(nodes[i], vname, onlyFullMatch)
            # If no occurence has been substituted, no need to proceed since we
            # handle the corresponding subset separately.
            if not found: return None

        # Reidentify bitwise, linear... subexpressions.
        r.refine()
        r.mark_linear()

        # Redetermine variables.
        self.__collect_and_enumerate_variables(r)

        self.__simplify_subexpression(r, None, True, True)

        for i in range(len(nodes)):
            vname = self.__get_vname(start + i)
            r.replace_variable(vname, nodes[i])

        r.refine()
        return r

    # Returns true iff the first given linear expression is not more complex
    # than the second one.
    def __is_second_more_or_equally_complex(self, first, second):
        c1 = first.compute_alternation()
        c2 = second.compute_alternation()

        if c1 != c2: return c1 < c2
        return compute_bitwise_complexity(first) <= compute_bitwise_complexity(second)

    # Try to simplify the expression further by substituting subexpressions
    # equal to the given node by a variable.
    def __simplify_via_substitution_of_nodes(self, node, nodes, onlyFullMatch):
        r = self.__get_simpl_via_substitution_of_nodes(node, nodes, onlyFullMatch)

        # We keep the original node.
        if r == None or not self.__is_second_more_or_equally_complex(r, node):
            return False

        node.copy(r)

        # Apply additional refinement which may be necessary after
        # substitution. If anything is changed there, repeat the general
        # refinement.
        if node.refine_after_substitution(): node.refine()

        # Reidentify bitwise, linear... subexpressions again.
        node.mark_linear()

        return True

    # Try to simplify the expression further by substituting suitable
    # subexpressions from the given list according to the given index by
    # variables.
    def __simplify_via_substitution_for_index(self, node, nodes, index):
        n = index
        sel = []
        for j in range(len(nodes)):
            if (n & 1) == 1: sel.append(nodes[j])
            n = n >> 1

        changed = False
        if self.__simplify_via_substitution_of_nodes(node, sel, False): changed = True
        if self.__simplify_via_substitution_of_nodes(node, sel, True):  changed = True

        return changed

    # Try to simplify the expression further by substituting suitable
    # subexpressions by variables.
    def __simplify_via_substitution(self, node):
        nodes = self.__collect_nodes_for_substitution(node)
        if len(nodes) == 0: return False

        changed = False

        # Try substitution of all possible combinations of nodes to substitute.
        for i in range(1, 2**len(nodes)):
            # Save runtime by restricting to subsets of up to 3 nodes.
            if len(nodes) > 5 and popcount(i) > 3: continue
            if len(nodes) > 9 and popcount(i) > 2: continue

            if self.__simplify_via_substitution_for_index(node, nodes, i): changed = True

        return changed


    # Simplify the subexpression corresponding to the given node.
    def __simplify_subexpression(self, node, parent, noRefactor=False, noSubst=False):
        if node.is_linear():
            ch = self.__simplify_linear_subexpression(node)
            return ch

        changed = False
        for c in node.children:
            ch = self.__simplify_subexpression(c, node, noRefactor, noSubst)
            if ch: changed = True

        before = str(node)
        node.refine(parent, True)
        node.mark_linear(True)

        if not changed: changed = str(node) != before

        if node.type == NodeType.CONSTANT:
            assert(changed)
            return changed

        if node.is_linear():
            self.__simplify_linear_subexpression(node)
            return True

        if self.__simplify_nonlinear_subexpression(node, parent, noRefactor, noSubst):
            changed = True

        return changed


    # Verify that the original expression and the simplified one are equivalent
    # using Z3.
    def __verify_using_z3(self, orig, simpl):
        # Use 1 min as a timeout.
        return verify_using_z3(orig, simpl, self.__bitCount, 60000)

    # Returns the number of variables occuring in the given expression.
    def get_variable_count(self, expr):
        root = parse(expr, self.__bitCount, True, False, False)
        if root == None:
            sys.exit("Error at parsing in get_variable_count()!")

        self.__collect_and_enumerate_variables(root)
        return self.__vnumber


    # Verify the given solution via evaluation.
    def __check_verify(self, orig, simplTree):
        if self.__verifBitCount == None: return True

        origTree = parse(orig, self.__bitCount, self.__modRed, False, False)
        return simplTree.check_verify(origTree, self.__verifBitCount)


    # Simplify the given MBA.
    # Note: only one underscore, for MacOS support, see https://github.com/DenuvoSoftwareSolutions/GAMBA/issues/1
    def _simplify(self, expr, returnDict):
        root = parse(expr, self.__bitCount, self.__modRed, True, True)
        if root == None: sys.exit("Error: Could not parse expression!")

        self.__simplify_subexpression(root, None)

        root.polish()
        returnDict[0] = root

    # Simplify the given MBA and check the result if required.
    def simplify(self, expr, useZ3=False):
        manager = multiprocessing.Manager()
        returnDict = manager.dict()
        p = multiprocessing.Process(target=self._simplify, args=(expr, returnDict))
        p.start()
        # Wait for 30 seconds or until process finishes
        p.join(30)

        # If thread is still active
        if p.is_alive():
            print("timed out... kill process...")

            # Terminate - may not work if process is stuck for good
            #p.terminate()
            # OR Kill - will work for sure, no chance for process to finish nicely however
            p.kill()

            p.join()
            return ""

        if len(returnDict.values()) == 0: sys.exit("No simplification result!")

        root = returnDict.values()[0]
        simpl = root.to_string()

        if useZ3 and not self.__verify_using_z3(expr, simpl):
            sys.exit("Error in simplification! Simplified expression is not proved equivalent to original one!")

        return simpl if self.__check_verify(expr, root) else ""


# Simplify the given expression with given number of variables.
def simplify_mba(expr, bitCount, useZ3=False, modRed=False, verifBitCount=None):
    simplifier = GeneralSimplifier(bitCount, modRed, verifBitCount)
    simpl = simplifier.simplify(expr, useZ3)
    return simpl


# Print options.
def print_usage():
    print("Usage: python3 simplify.py")
    print("Command line input not preceded by option indicators below are considered expressions to be simplified.")
    print("Command line options:")
    print("    -h:    print usage")
    print("    -b:    specify the bit number of variables (default is 64)")
    print("    -z:    enable a check for valid simplification using Z3")
    print("    -m:    enable a reduction of all constants modulo 2**b where b is the bit count")
    print("    -v:    specify a bit count for verification for nonlinear input (default: no verification)")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(prog='GAMBA', description='Simplification of General Mixed Boolean-Arithmetic Expressions', epilog='Each command line input not preceded by option indicators is considered an expression to be simplified. Expressions are read from standard input if none are given on command line.')
    parser.add_argument("-b", default=64, dest="bitCount", help="Specify the bit number of variables", type=int)
    parser.add_argument("-z", default=False, dest="useZ3", help="Enable a check for valid simplification using Z3", type=bool)
    parser.add_argument("-m", default=False, dest="modRed", help="Enable a reduction of all constants modulo 2**b where b is the bit count", type=bool)
    parser.add_argument("-v", default=None, dest="verifyBitCount", help="Specify a bit count for verification for nonlinear input", type=int)
    parser.add_argument('exprs', nargs='*', type=str)
    args = parser.parse_args()

    if len(args.exprs) == 0:
        args.exprs.extend(sys.stdin.read().splitlines())

    for expr in args.exprs:
        print("*** Expression " + expr)
        simpl = simplify_mba(expr, args.bitCount, args.useZ3, args.modRed, args.verifyBitCount)
        print("*** ... simplified to " + simpl)

    sys.exit(0)
