#!/usr/bin/python3

from enum import Enum
import random
import sys

from batch import Batch, IndexWithMultitude

usingGmpy = True
try: import gmpy2
except ModuleNotFoundError: usingGmpy = False

def popcount(x):
    if usingGmpy: return gmpy2.popcount(x)
    try: return x.bit_count()
    except AttributeError: return bin(x).count("1")

def trailing_zeros(x):
    return (x&-x).bit_length() - 1

def power(x, e, m):
    if x == 1: return 1

    r = 1
    for i in range(e):
        r = (r * x) % m
        if r == 0: return 0
    return r


# Some bounds to control performance.
MAX_CHILDREN_SUMMED_UP = 3
MAX_CHILDREN_TO_TRANSFORM_BITW = 5
MAX_EXPONENT_TO_EXPAND = 2

NICE_RANDOM_NUMBER_BOUND = 32
SPLIT_FREQ_BITWISE = 1
SPLIT_FREQ_OTHERS = 4

# The type of a node representing a subexpression.
class NodeType(Enum):
    CONSTANT = 0
    VARIABLE = 1
    POWER = 2
    NEGATION = 3
    PRODUCT = 4
    SUM = 5
    CONJUNCTION = 6
    EXCL_DISJUNCTION = 7
    INCL_DISJUNCTION = 8

    # Function for comparing types.
    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented

# Additional information on a node.
class NodeState(Enum):
    UNKNOWN = 0,
    BITWISE = 1,
    LINEAR = 2,
    NONLINEAR = 3,
    MIXED = 4

# Reduces the given number modulo given modulus.
def mod_red(n, modulus):
    n = int(n)
    return n % modulus

# Returns true iff the given lists of children match.
def do_children_match(l1, l2):
    if len(l1) != len(l2): return False
    return are_all_children_contained(l1, l2)

# Returns true iff all children contained in l1 are also contained in l2.
def are_all_children_contained(l1, l2):
    oIndices = list(range(len(l2)))
    for child in l1:
        found = False
        for i in oIndices:
            if child.equals(l2[i]):
                oIndices.remove(i)
                found = True

        if not found: return False

    return True

# A node representing a subexpression.
class Node():
    # Initialize internals
    def __init__(self, nodeType, modulus, modRed=False):
        self.type = nodeType
        self.children = []
        self.vname = ""
        self.__vidx = -1
        self.constant = 0
        self.state = NodeState.UNKNOWN
        self.__modulus = modulus
        self.__modRed = modRed
        self.linearEnd = 0
        self.__MAX_IT = 10

    # Print the node.
    def __str__(self):
        return self.to_string()

    # Get the node's string representation. Print parentheses around iff
    # withParentheses is True. For commutative binary operators, print children
    # until the end-th one. If varNames is not None, its entries are used as
    # variable names.
    def to_string(self, withParentheses=False, end=-1, varNames=None):
        if end == -1: end = len(self.children)
        else: assert(end <= len(self.children))

        if self.type == NodeType.CONSTANT: return str(self.constant)
        if self.type == NodeType.VARIABLE:
            return self.vname if varNames == None else varNames[self.__vidx]

        if self.type == NodeType.POWER:
            assert(len(self.children) == 2)
            child1 = self.children[0]
            child2 = self.children[1]
            ret = child1.to_string(child1.type > NodeType.VARIABLE, -1, varNames) + "**" + \
                  child2.to_string(child2.type > NodeType.VARIABLE, -1, varNames)
            if withParentheses: ret = "(" + ret + ")"
            return ret

        if self.type == NodeType.NEGATION:
            assert(len(self.children) == 1)
            child = self.children[0]
            ret = "~" + child.to_string(child.type > NodeType.NEGATION, -1, varNames)
            if withParentheses: ret = "(" + ret + ")"
            return ret

        if self.type == NodeType.PRODUCT:
            assert(len(self.children) > 0)
            child1 = self.children[0]
            ret1 = child1.to_string(child1.type > NodeType.PRODUCT, -1, varNames)
            ret = ret1
            for child in self.children[1:end]:
                ret += "*" + child.to_string(child.type > NodeType.PRODUCT, -1, varNames)
            # Rather than multiplying by -1, only use the minus and get rid
            # of '1*'.
            if ret1 == "-1" and len(self.children) > 1 and end > 1:
                ret = "-" + ret[3:]
            if withParentheses: ret = "(" + ret + ")"
            return ret

        if self.type == NodeType.SUM:
            assert(len(self.children) > 0)
            child1 = self.children[0]
            ret = child1.to_string(child1.type > NodeType.SUM, -1, varNames)
            for child in self.children[1:end]:
                s = child.to_string(child.type > NodeType.SUM, -1, varNames)
                if s[0] != '-': ret += "+"
                ret += s
            if withParentheses: ret = "(" + ret + ")"
            return ret

        if self.type == NodeType.CONJUNCTION:
            assert(len(self.children) > 0)
            child1 = self.children[0]
            ret = child1.to_string(child1.type > NodeType.CONJUNCTION, -1, varNames)
            for child in self.children[1:end]:
                ret += "&" + child.to_string(child.type > NodeType.CONJUNCTION, -1, varNames)
            if withParentheses:
                ret = "(" + ret + ")"
            return ret

        elif self.type == NodeType.EXCL_DISJUNCTION:
            assert(len(self.children) > 0)
            child1 = self.children[0]
            ret = child1.to_string(child1.type > NodeType.EXCL_DISJUNCTION, -1, varNames)
            for child in self.children[1:end]:
                ret += "^" + child.to_string(child.type > NodeType.EXCL_DISJUNCTION, -1, varNames)
            if withParentheses: ret = "(" + ret + ")"
            return ret

        if self.type == NodeType.INCL_DISJUNCTION:
            assert(len(self.children) > 0)
            child1 = self.children[0]
            ret = child1.to_string(child1.type > NodeType.INCL_DISJUNCTION, -1, varNames)
            for child in self.children[1:end]:
                ret += "|" + child.to_string(child.type > NodeType.INCL_DISJUNCTION, -1, varNames)
            if withParentheses: ret = "(" + ret + ")"
            return ret

        assert(False) # pragma: no cover

    # Get the node's string representation considering the first end children.
    def part_to_string(self, end):
        return self.to_string(False, end)

    # Returns the power of given base to given exponent, modulo modulus.
    def __power(self, b, e):
        return power(b, e, self.__modulus)

    # Reduce the given constant modulo modulus and subtract modulus iff modRed
    # is False and the number is larger than half modulus, in order to have a
    # minimal absolute value in this case.
    def __get_reduced_constant(self, c):
        if self.__modRed: return mod_red(c, self.__modulus)
        return self.__get_reduced_constant_closer_to_zero(c)

    # Reduce the given constant modulo modulus and subtract modulus iff the
    # number is larger than half modulus, in order to have a minimal absolute
    # value in this case.
    def __get_reduced_constant_closer_to_zero(self, c):
        c = mod_red(c, self.__modulus)
        if 2 * c > self.__modulus: c -= self.__modulus
        return c

    # Reduce the node's constant modulo modulus and subtract modulus iff modRed
    # is False and the number is larger than half modulus, in order to have a
    # minimal absolute value in this case. Requires that the node is of type
    # CONSTANT.
    def __reduce_constant(self):
        self.constant = self.__get_reduced_constant(self.constant)

    # Set the node's constant and reduce it modulo modulus. Requires that the
    # node is of type CONSTANT.
    def __set_and_reduce_constant(self, c):
        self.constant = self.__get_reduced_constant(c)

    # Initialize the member vidx (index of a variable) for all nodes
    # representing variables and store the variables in the given list in the
    # corresponding order.
    def collect_and_enumerate_variables(self, variables):
        self.collect_variables(variables)
        variables.sort(key = lambda v: (len(v), v))
        self.enumerate_variables(variables)

    # Collect all variable names occuring in the expression corresponding to
    # this node.
    def collect_variables(self, variables):
        if self.type == NodeType.VARIABLE:
            # The variable is not ready known yet.
            if not self.vname in variables: variables.append(self.vname)
        else:
            for child in self.children: child.collect_variables(variables)

    # Initialize the member vidx (index of a variable) for all nodes
    # representing variables corresponding to the given list of variables.
    def enumerate_variables(self, variables):
        if self.type == NodeType.VARIABLE:
            assert(self.vname in variables)
            self.__vidx = variables.index(self.vname)
        else:
            for child in self.children: child.enumerate_variables(variables)

    # Returns the maximum integer for which this node has a variable name
    # according to the given start and end of variable names. Returns None if
    # there is no such variable name.
    def get_max_vname(self, start, end):
        if self.type == NodeType.VARIABLE:
            if self.vname[:len(start)] != start: return None
            if self.vname[-len(end):] != end: return None
            n = self.vname[len(start):-len(end)]
            if not n.isnumeric(): return None
            return int(n)
        else:
            maxn = None
            for child in self.children:
                n = child.get_max_vname(start, end)
                if n != None and (maxn == None or n > maxn): maxn = n
            return maxn

    # Evaluate the expression whose root this node is for the given vector of
    # arguments.
    def eval(self, X):
        if self.type == NodeType.CONSTANT: return self.constant % self.__modulus

        if self.type == NodeType.VARIABLE:
            if self.__vidx < 0: sys.exit("ERROR: Variable index not set prior to evaluation!")
            return X[self.__vidx] % self.__modulus

        assert(len(self.children) > 0)
        if self.type == NodeType.NEGATION: return (~self.children[0].eval(X)) % self.__modulus

        val = self.children[0].eval(X)

        for i in range(1, len(self.children)):
            val = self.__apply_binop(val, self.children[i].eval(X)) % self.__modulus

        return val

    # Apply the node's binary operation to the given values.
    def __apply_binop(self, x, y):
        if self.type == NodeType.POWER: return self.__power(x, y)
        if self.type == NodeType.PRODUCT: return x*y
        if self.type == NodeType.SUM: return x + y
        return self.__apply_bitwise_binop(x, y)

    # Apply the node's binary operation to the given values. Requires that this
    # node is a conjunction, an inclusive or an exclusive disjunction.
    def __apply_bitwise_binop(self, x, y):
        if self.type == NodeType.CONJUNCTION: return x&y
        if self.type == NodeType.EXCL_DISJUNCTION: return x^y
        if self.type == NodeType.INCL_DISJUNCTION: return x|y
        assert(False) # pragma: no cover
        return 0


    # Returns true iff the node has at least one nonlinear child.
    def has_nonlinear_child(self):
        for child in self.children:
            if child.state == NodeState.NONLINEAR or child.state == NodeState.MIXED:
                return True
        return False


    # Returns true iff this node's children are all contained in the
    # given one's children.
    def __are_all_children_contained(self, other):
        assert(other.type == self.type)
        return are_all_children_contained(self.children, other.children)

    # Returns true iff this node is equivalent to the given one.
    def equals(self, other):
        if self.type != other.type: return self.__equals_rewriting_bitwise(other)
        if self.type == NodeType.CONSTANT: return self.constant == other.constant
        if self.type == NodeType.VARIABLE: return self.vname == other.vname
        if len(self.children) != len(other.children): return False
        return self.__are_all_children_contained(other)

    # Returns true iff this node is equivalent to the given one after negation.
    def equals_negated(self, other):
        if self.type == NodeType.NEGATION and self.children[0].equals(other): return True
        if other.type == NodeType.NEGATION and other.children[0].equals(self): return True
        return False

    # Returns true iff this node is a (negative) bitwise negations and the
    # given one is a corresponding arithmetic (negative) negation, or vice
    # versa.
    def __equals_rewriting_bitwise(self, other):
        return self.__equals_rewriting_bitwise_asymm(other) or other.__equals_rewriting_bitwise_asymm(self)

    # Returns true iff this node is a (negative) bitwise negations and the
    # given one is a corresponding arithmetic (negative) negation.
    def __equals_rewriting_bitwise_asymm(self, other):
        # Check for '~x'.
        if self.type == NodeType.NEGATION:
            node = other.__get_opt_transformed_negated()
            return node != None and node.equals(self.children[0])

        # Check for '-~x'.
        if self.type == NodeType.PRODUCT:
            if len(self.children) != 2: return False
            if not self.children[0].__is_constant(-1): return False
            if self.children[1].type != NodeType.NEGATION: return False

            node = other.__get_opt_negative_transformed_negated()
            return node != None and node.equals(self.children[1].children[0])

        return False

    # If this node has the form "x + 1", returns x. Otherwise returns None.
    def __get_opt_negative_transformed_negated(self):
        if self.type != NodeType.SUM: return None

        # Should not happen, but be sure.
        if len(self.children) < 2: return None

        # First check for term 1.
        if not self.children[0].__is_constant(1): return None

        # A node to store the result in case we have more terms.
        res = self.__new_node(NodeType.SUM)

        # Now collect the remaining terms.
        for i in range(1, len(self.children)):
            res.children.append(self.children[i].get_copy())

        assert(len(res.children) > 0)
        if len(res.children) == 1: return res.children[0]
        return res

    # Remove all children which the given one has.
    def __remove_children_of_node(self, other):
        for ochild in other.children:
            for i in range(len(self.children)):
                if self.children[i].equals(ochild):
                    del self.children[i]
                    break


    # Returns a node with given type.
    def __new_node(self, t):
        return Node(t, self.__modulus, self.__modRed)

    # Returns a node with type CONSTANT and given constant value.
    def __new_constant_node(self, constant):
        node = self.__new_node(NodeType.CONSTANT)
        node.constant = constant
        node.__reduce_constant()
        return node

    # Returns a node with type VARIABLE and given variable name.
    def __new_variable_node(self, vname):
        node = self.__new_node(NodeType.VARIABLE)
        node.vname = vname
        return node

    # Returns a node with given type and given children.
    def __new_node_with_children(self, t, children):
        node = self.__new_node(t)
        node.children = children
        return node


    # Substitute all nodes for the given variable name with the given constant.
    def replace_variable_by_constant(self, vname, constant):
        self.replace_variable(vname, self.__new_constant_node(constant))

    # Substitute all nodes for the given variable name with the given node.
    def replace_variable(self, vname, node):
        if self.type == NodeType.VARIABLE:
            if self.vname == vname: self.__copy_all(node)
            return

        for child in self.children: child.replace_variable(vname, node)


    # Refine the expression whose top-level node is this one.
    def refine(self, parent=None, restrictedScope=False):
        # Perform the refinement iteratively until nothing changes any more.
        for i in range(self.__MAX_IT):
            self.__refine_step_1(restrictedScope)
            if not self.__refine_step_2(parent, restrictedScope): return

    # Perform step 1 of the refinement for the expression whose top-level node
    # is this one. That is, merge constants whenever possible and rearrange
    # them such that the constant child, if existent, is always the first one,
    # try to flatten the tree hierarchy and sort the variables in commutative
    # binary expressions.
    def __refine_step_1(self, restrictedScope=False):
        if not restrictedScope:
            for c in self.children: c.__refine_step_1()

        self.__inspect_constants()
        self.__flatten()
        self.__check_duplicate_children()
        self.__resolve_inverse_nodes()
        self.__remove_trivial_nodes()


    # Inspect the constants of the expression whose top-level node is this one.
    # That is, merge constants whenever possible and rearrange them such that
    # the constant child, if existent, is always the first one.
    def __inspect_constants(self):
        if self.type == NodeType.INCL_DISJUNCTION:
            self.__inspect_constants_incl_disjunction()

        elif self.type == NodeType.EXCL_DISJUNCTION:
            self.__inspect_constants_excl_disjunction()

        elif self.type == NodeType.CONJUNCTION:
            self.__inspect_constants_conjunction()

        elif self.type == NodeType.SUM:
            self.__inspect_constants_sum()

        elif self.type == NodeType.PRODUCT:
            self.__inspect_constants_product()

        elif self.type == NodeType.NEGATION:
            self.__inspect_constants_negation()

        elif self.type == NodeType.POWER:
            self.__inspect_constants_power()

        elif self.type == NodeType.CONSTANT:
            self.__inspect_constants_constant()

    # Inspect the constants of the inclusive disjunction whose top-level node
    # is this one. That is, get rid of zero constant children and make sure
    # that there is at most one constant child and that is, if existent, the
    # first one. If there is a constant child with zeros everywhere, cancel the
    # whole conjunction.
    def __inspect_constants_incl_disjunction(self):
        first = self.children[0]
        isMinusOne = first.__is_constant(-1)
        toRemove = []

        if not isMinusOne:
            for child in self.children[1:]:
                if child.type == NodeType.CONSTANT:
                    if child.constant == 0:
                        toRemove.append(child)
                        continue

                    if child.__is_constant(-1):
                        isMinusOne = True
                        break

                    first = self.children[0]
                    if first.type == NodeType.CONSTANT:
                        first.__set_and_reduce_constant(first.constant | child.constant)
                        toRemove.append(child)
                    else:
                        self.children.remove(child)
                        self.children.insert(0, child)

        if isMinusOne:
            self.children = []
            self.type = NodeType.CONSTANT
            self.__set_and_reduce_constant(-1)
            return

        for child in toRemove: self.children.remove(child)

        first = self.children[0]
        if len(self.children) > 1 and first.__is_constant(0): self.children.pop(0)
        if len(self.children) == 1: self.copy(self.children[0])

    # Returns true iff this node is a constant with given value.
    def __is_constant(self, value):
        return self.type == NodeType.CONSTANT and mod_red(self.constant - value, self.__modulus) == 0

    # Inspect the constants of the exclusive disjunction whose top-level node
    # is this one. That is, get rid of zero constant children and make sure that
    # there is at most one constant child and that is, if existent, the first one.
    def __inspect_constants_excl_disjunction(self):
        toRemove = []

        for child in self.children[1:]:
            if child.type == NodeType.CONSTANT:
                if child.constant == 0:
                    toRemove.append(child)
                    continue

                first = self.children[0]
                if first.type == NodeType.CONSTANT:
                    first.__set_and_reduce_constant(first.constant ^ child.constant)
                    toRemove.append(child)
                else:
                    self.children.remove(child)
                    self.children.insert(0, child)

        for child in toRemove: self.children.remove(child)

        first = self.children[0]
        if len(self.children) > 1 and first.__is_constant(0): self.children.pop(0)
        if len(self.children) == 1: self.copy(self.children[0])

    # Inspect the constants of the conjunction whose top-level node is this one.
    # That is, get rid of constant children which have ones everywhere and make
    # sure that there is at most one constant child and that is, if existent,
    # the first one. If there is a constant zero child, cancel the whole
    # conjunction.
    def __inspect_constants_conjunction(self):
        first = self.children[0]
        isZero = first.__is_constant(0)
        toRemove = []

        if not isZero:
            for child in self.children[1:]:
                if child.type == NodeType.CONSTANT:
                    if child.__is_constant(-1):
                        toRemove.append(child)
                        continue

                    if child.constant == 0:
                        isZero = True
                        break

                    first = self.children[0]
                    if first.type == NodeType.CONSTANT:
                        first.__set_and_reduce_constant(first.constant & child.constant)
                        toRemove.append(child)
                    else:
                        self.children.remove(child)
                        self.children.insert(0, child)

        if isZero:
            self.children = []
            self.type = NodeType.CONSTANT
            self.constant = 0
            return

        for child in toRemove: self.children.remove(child)

        first = self.children[0]
        if len(self.children) > 1 and first.__is_constant(-1): self.children.pop(0)
        if len(self.children) == 1: self.copy(self.children[0])

    # Inspect the constants of the sum whose top-level node is this one. That
    # is, get rid of zero summands and make sure that there is at most one
    # constant summand and that is, if existent, the first one.
    def __inspect_constants_sum(self):
        first = self.children[0]
        toRemove = []

        for child in self.children[1:]:
            if child.type == NodeType.CONSTANT:
                if child.constant == 0:
                    toRemove.append(child)
                    continue

                first = self.children[0]
                if first.type == NodeType.CONSTANT:
                    first.__set_and_reduce_constant(first.constant + child.constant)
                    toRemove.append(child)
                else:
                    self.children.remove(child)
                    self.children.insert(0, child)

        for child in toRemove: self.children.remove(child)

        first = self.children[0]
        if len(self.children) > 1 and first.__is_constant(0): self.children.pop(0)
        if len(self.children) == 1: self.copy(self.children[0])

    # Inspect the constants of the product whose top-level node is this one.
    # That is, get rid of factors which are equal to 1 and make sure that there
    # is at most one constant factor and that is, if existent, the first one.
    def __inspect_constants_product(self):
        first = self.children[0]
        isZero = first.__is_constant(0)
        toRemove = []

        if not isZero:
            for child in self.children[1:]:
                if child.type == NodeType.CONSTANT:
                    if child.constant == 1:
                        toRemove.append(child)
                        continue

                    if child.constant == 0:
                        isZero = True
                        break

                    first = self.children[0]
                    if first.type == NodeType.CONSTANT:
                        first.__set_and_reduce_constant(first.constant * child.constant)
                        toRemove.append(child)
                    else:
                        self.children.remove(child)
                        self.children.insert(0, child)

        if isZero:
            self.children = []
            self.type = NodeType.CONSTANT
            self.constant = 0
            return

        for child in toRemove: self.children.remove(child)

        first = self.children[0]
        if len(self.children) > 1 and first.__is_constant(1): self.children.pop(0)
        if len(self.children) == 1: self.copy(self.children[0])

    # Inspect the constants of the bitwise negation whose top-level node is
    # this one. That is, get rid of double negations.
    def __inspect_constants_negation(self):
        assert(len(self.children) == 1)
        child = self.children[0]

        # Double negation is no negation.
        if child.type == NodeType.NEGATION: self.copy(child.children[0])
        elif child.type == NodeType.CONSTANT:
            child.__set_and_reduce_constant(-child.constant - 1)
            self.copy(child)

    # Inspect the constants of the power whose top-level node is this one. That
    # is, get rid of exponents which are zero or one.
    def __inspect_constants_power(self):
        assert(len(self.children) == 2)
        base = self.children[0]
        exp = self.children[1]

        if base.type == NodeType.CONSTANT and exp.type == NodeType.CONSTANT:
            base.__set_and_reduce_constant(self.__power(base.constant, exp.constant))
            self.copy(base)
            return

        if exp.type == NodeType.CONSTANT:
            if exp.constant == 0:
                self.type = NodeType.CONSTANT
                self.constant = 1
                self.children = []
            elif exp.constant == 1: self.copy(base)

    # Modulo-reduce the constant by stored modulus.
    def __inspect_constants_constant(self):
        self.__reduce_constant()

    # Copy the given node's content to this node.
    def copy(self, node):
        self.type = node.type
        self.state = node.state
        self.children = node.children
        self.vname = node.vname
        self.__vidx = node.__vidx
        self.constant = node.constant

    # Copy the given node's content to this node and make sure that all
    # children and their children etc., if existent, are copied too.
    def __copy_all(self, node):
        self.type = node.type
        self.state = node.state
        self.children = []
        self.vname = node.vname
        self.__vidx = node.__vidx
        self.constant = node.constant

        for child in node.children: self.children.append(child.get_copy())

    # Replace all children and their children etc., if existent, by copies.
    def __copy_children(self):
        for i in range(len(self.children)):
            self.children[i] = self.children[i].get_copy()
            self.children[i].__copy_children()

    # Copy this node's content to a new node.
    def get_copy(self):
        n = self.__new_node(self.type)
        n.state = self.state
        n.children = []
        n.vname = self.vname
        n.__vidx = self.__vidx
        n.constant = self.constant

        for child in self.children: n.children.append(child.get_copy())
        return n

    # Copy this node's content to a new node.
    def __get_shallow_copy(self):
        n = self.__new_node(self.type)
        n.state = self.state
        n.children = []
        n.vname = self.vname
        n.__vidx = self.__vidx
        n.constant = self.constant
        n.children = list(self.children)

        return n


    # Flatten the node's hierarchy by merging, if possible, binary operator
    # nodes with children that have the same operators.
    def __flatten(self):
        # Note that negations are already flattened in inspect_constants in
        # order not to miss the opportunity due to negating constants.

        if self.type == NodeType.INCL_DISJUNCTION: self.__flatten_binary_generic()
        elif self.type == NodeType.EXCL_DISJUNCTION: self.__flatten_binary_generic()
        elif self.type == NodeType.CONJUNCTION: self.__flatten_binary_generic()
        elif self.type == NodeType.SUM: self.__flatten_binary_generic()
        elif self.type == NodeType.PRODUCT: self.__flatten_product()

    # Flatten the binary operator node's hierarchy by merging it, if possible,
    # with children that have the same operators.
    def __flatten_binary_generic(self):
        changed = False

        for i in range(len(self.children)-1, -1, -1):
            child = self.children[i]
            if child.type != self.type: continue

            del self.children[i]
            self.children.extend(child.children)
            changed = True

        if changed: self.__inspect_constants()

    # Flatten the product node's hierarchy by merging it, if possible, with
    # children that have the same operators.
    def __flatten_product(self):
        changed = False
        i = 0

        while i < len(self.children):
            child = self.children[i]
            if child.type != self.type:
                i += 1
                continue

            changed = True
            del self.children[i]
            if child.children[0].type == NodeType.CONSTANT:
                if i > 0 and self.children[0].type == NodeType.CONSTANT:
                    prod = self.children[0].constant * child.children[0].constant
                    self.children[0].__set_and_reduce_constant(prod)
                else:
                    self.children.insert(0, child.children[0])
                    i += 1
                del child.children[0]

            self.children[i:i] = child.children
            i += len(child.children)


        # Finally, if the node's children have been changed, check whether the
        # constant exists and is now 1 and hence can be removed.
        if not changed: return

        # We do not expect to only have one child, but be sure.
        if len(self.children) > 1:
            first = self.children[0]
            if first.type != NodeType.CONSTANT: return
            if not first.__is_constant(1): return

            # The constant exists and is 1.
            del self.children[0]

        # If there is only one child left, the product vanishes.
        if len(self.children) == 1: self.copy(self.children[0])


    # For this node, search for duplicate children of the same node and remove
    # either one or both of them, depending on the operation.
    def __check_duplicate_children(self):
        if self.type == NodeType.INCL_DISJUNCTION: self.__remove_duplicate_children()
        elif self.type == NodeType.EXCL_DISJUNCTION: self.__remove_pairs_of_children()
        elif self.type == NodeType.CONJUNCTION: self.__remove_duplicate_children()
        elif self.type == NodeType.SUM: self.__merge_similar_nodes_sum()

    # For this node, which is assumed to be a conjunction or an inclusive
    # disjunction, remove duplicate children.
    def __remove_duplicate_children(self):
        i = 0
        while i < len(self.children):
            for j in range(len(self.children)-1, i, -1):
                if self.children[i].equals(self.children[j]):
                    del self.children[j]
            i += 1

    # For this node, which is assumed to be an exclusive disjunction, remove
    # all occuring pairs of coincident children.
    def __remove_pairs_of_children(self):
        i = 0
        while i < len(self.children):
            for j in range(len(self.children)-1, i, -1):
                if self.children[i].equals(self.children[j]):
                    del self.children[j]
                    del self.children[i]
                    i -= 1
                    break
            i += 1

        if len(self.children) == 0: self.children = [self.__new_constant_node(0)]

    # Merge terms of a sum which are coincident up to a constant factor.
    def __merge_similar_nodes_sum(self):
        assert(self.type == NodeType.SUM)

        i = 0
        while i < len(self.children) - 1:
            j = i + 1
            while j < len(self.children):
                # Children i and j could be merged. We have no use for child j
                # any more.
                if self.__try_merge_sum_children(i, j): del self.children[j]
                else: j += 1

            # If child i is now zero, remove it.
            if self.children[i].__is_zero_product(): del self.children[i]
            # If child i has a factor of 1, remove that.
            else:
                if self.children[i].__has_factor_one():
                    self.children[i].children.pop(0)
                    if len(self.children[i].children) == 1:
                        self.children[i] = self.children[i].children[0]
                i += 1

        # A sum remains nontrivial if it continues to have more than
        # one child.
        if len(self.children) > 1: return

        # The sum only has one summand and hence is trivial.
        if len(self.children) == 1:
            self.copy(self.children[0])
            return

        # The sum fully vanishes.
        self.type = NodeType.CONSTANT
        self.children = []
        self.constant = 0

    # Returns true iff this node is a product that resolves to zero.
    def __is_zero_product(self):
        return self.type == NodeType.PRODUCT and self.children[0].__is_constant(0)

    # Returns true iff this node is a product with factor 1.
    def __has_factor_one(self):
        return self.type == NodeType.PRODUCT and self.children[0].__is_constant(1)

    # Returns the node's constant factor if it has one, or None otherwise.
    def __get_opt_const_factor(self):
        if self.type == NodeType.PRODUCT and self.children[0].type == NodeType.CONSTANT:
            return self.children[0].constant
        return None

    # Try to merge the given nodes, both terms of the same sum and children of
    # this node. They are merged if they coincide up to a constant factor.
    # Returns true iff they are merged.
    def __try_merge_sum_children(self, i, j):
        child1 = self.children[i]
        const1 = child1.__get_opt_const_factor()

        child2 = self.children[j]
        const2 = child2.__get_opt_const_factor()

        # The nodes cannot be merged.
        if not child1.__equals_neglecting_constants(child2, const1 != None, const2 != None):
            return False

        if const2 == None: const2 = 1

        if const1 == None:
            if child1.type == NodeType.PRODUCT:
                child1.children.insert(0, self.__new_constant_node(1 + const2))
            else:
                c = self.__new_constant_node(1 + const2)
                self.children[i] = self.__new_node_with_children(NodeType.PRODUCT, [c, child1])
        else:
            child1.children[0].constant += const2
            child1.children[0].__reduce_constant()

        return True

    # Returns true iff this node is equivalent to the given one, neglecting the
    # nodes constants if they have any and are products.
    def __equals_neglecting_constants(self, other, hasConst, hasConstOther):
        assert(not hasConst or self.type == NodeType.PRODUCT)
        assert(not hasConstOther or other.type == NodeType.PRODUCT)
        assert(not hasConst or self.children[0].type == NodeType.CONSTANT)
        assert(not hasConstOther or other.children[0].type == NodeType.CONSTANT)

        if hasConst:
            if hasConstOther:
                return self.__equals_neglecting_constants_both_const(other)
            return other.__equals_neglecting_constants_other_const(self)
  
        if hasConstOther:
            return self.__equals_neglecting_constants_other_const(other)
        return self.equals(other)

    # Returns true iff this node is equivalent to the given one, neglecting the
    # nodes constants if they have any and are products. Requires that the
    # other node has a constant factor and this node doesn't.
    def __equals_neglecting_constants_other_const(self, other):
        assert(other.type == NodeType.PRODUCT)
        assert(other.children[0].type == NodeType.CONSTANT)
        assert(self.type != NodeType.PRODUCT or self.children[0].type != NodeType.CONSTANT)

        if len(other.children) == 2: return self.equals(other.children[1])
        if self.type != NodeType.PRODUCT: return False
        if len(self.children) != len(other.children) - 1: return False

        # Try to find each of this nodes children among the other node's ones.
        oIndices = list(range(1, len(other.children)))
        for child in self.children:
            found = False
            for i in oIndices:
                if child.equals(other.children[i]):
                    oIndices.remove(i)
                    found = True

            if not found: return False

        return True

    # Returns true iff this node is equivalent to the given one, neglecting the
    # nodes constants if they have any and are products. Requires that this
    # node as well as the other one have a constant factor.
    def __equals_neglecting_constants_both_const(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(self.children[0].type == NodeType.CONSTANT)
        assert(other.type == NodeType.PRODUCT)
        assert(other.children[0].type == NodeType.CONSTANT)

        if len(self.children) != len(other.children): return False
        if len(self.children) == 2: return self.children[1].equals(other.children[1])

        # Try to find each of this nodes children but the constant among the
        # other node's ones.
        oIndices = list(range(1, len(other.children)))
        for child in self.children[1:]:
            found = False
            for i in oIndices:
                if child.equals(other.children[i]):
                    oIndices.remove(i)
                    found = True

            if not found: return False

        return True


    # Resolve operations of elements which are inverse to each other.
    def __resolve_inverse_nodes(self):
        if self.type in [NodeType.INCL_DISJUNCTION, NodeType.EXCL_DISJUNCTION, NodeType.CONJUNCTION]:
            self.__resolve_inverse_nodes_bitwise()

        # Note that we have already merged similar terms in sums, including
        # those that are inverse to each other.

    # Resolve a bitwise operation of elements which are inverse to each other.
    def __resolve_inverse_nodes_bitwise(self):
        i = 0
        while True:
            if i >= len(self.children): break

            child1 = self.children[i]
            neg1 = child1.type == NodeType.NEGATION

            for j in range(i + 1, len(self.children)):
                child2 = self.children[j]

                # The nodes are not bitwise inverse.
                if not child1.__is_bitwise_inverse(child2): continue

                # A conjunction or inclusive disjunction resolves to a trivial
                # constant. Same for an exclusive disjunction with 2 operands.
                if self.type != NodeType.EXCL_DISJUNCTION or len(self.children) == 2:
                    self.copy(self.__new_constant_node(0 if self.type == NodeType.CONJUNCTION else -1))
                    return

                # An exclusive disjunction remains nontrivial if it continues
                # to have more than one child.
                del self.children[j]
                del self.children[i]

                if self.children[0].type == NodeType.CONSTANT:
                    self.children[0].__set_and_reduce_constant(-1^self.children[0].constant)

                    # Decrement i since it will be incremented at the loop's
                    # end.
                    i -= 1

                else: self.children.insert(0, self.__new_constant_node(-1))

                # The exclusive disjunction is now trivial.
                if len(self.children) == 1:
                    self.copy(self.children[0])
                    return

                break

            i += 1

    # Returns True iff this node is bitwise inverse to the given node.
    def __is_bitwise_inverse(self, other):
        if self.type == NodeType.NEGATION:
            if other.type == NodeType.NEGATION:
                return self.children[0].__is_bitwise_inverse(other.children[0])
            return self.children[0].equals(other)

        if other.type == NodeType.NEGATION: return self.equals(other.children[0])

        # If we are here, we have no negation. Check whether we have sums that
        # are inverse to each other.

        node = self.get_copy()
        if node.type == NodeType.PRODUCT and len(node.children) == 2 and node.children[0].type == NodeType.CONSTANT:
            if node.children[1].type == NodeType.SUM:
                for n in node.children[1].children: n.__multiply(node.children[0].constant)
                node.copy(node.children[1])

        onode = other.get_copy()
        if onode.type == NodeType.PRODUCT and len(onode.children) == 2 and onode.children[0].type == NodeType.CONSTANT:
            if onode.children[1].type == NodeType.SUM:
                for n in onode.children[1].children: n.__multiply(onode.children[0].constant)
                onode.copy(onode.children[1])

        if node.type == NodeType.SUM:
            if onode.type != NodeType.SUM:
                if len(node.children) > 2 or not node.children[0].__is_constant(-1): return False

                node.children[1].__multiply_by_minus_one()
                return node.children[1].equals(onode)

            for child in node.children: child.__multiply_by_minus_one()
            if node.children[0].type == NodeType.CONSTANT:
                node.children[0].constant -= 1
                node.children[0].__reduce_constant()

                if node.children[0].__is_constant(0):
                    del node.children[0]

                    # If there is only one term left, we do not need the sum.
                    # But then the nodes cannot be equal since the other one is
                    # a sum.
                    assert(len(node.children) >= 1)
                    if len(self.children) == 1: return False

            else: node.children.insert(0, self.__new_constant_node(-1))

            return node.equals(onode)

        # The nodes cannot be inverse if none is a sum.
        if onode.type != NodeType.SUM: return False

        if len(onode.children) > 2 or not onode.children[0].__is_constant(-1): return False

        onode.children[1].__multiply_by_minus_one()
        return onode.children[1].equals(node)


    # Replace binary operator notes with only one child node by this node.
    def __remove_trivial_nodes(self):
        if self.type < NodeType.PRODUCT: return
        if len(self.children) == 1: self.copy(self.children[0])


    # Perform step 2 of the refinement for the expression whose top-level node
    # is this one. That is, check whether bitwise negations should be
    # transformed.
    def __refine_step_2(self, parent=None, restrictedScope=False):
        changed = False
        if not restrictedScope:
            for c in self.children:
                if c.__refine_step_2(self): changed = True

        if self.__eliminate_nested_negations_advanced():          changed = True
        if self.__check_bitwise_negations(parent):                changed = True
        if self.__check_bitwise_powers_of_two():                  changed = True
        if self.__check_beautify_constants_in_products():         changed = True
        if self.__check_move_in_bitwise_negations():              changed = True
        if self.__check_bitwise_negations_in_excl_disjunctions(): changed = True
        if self.__check_rewrite_powers(parent):                   changed = True
        if self.__check_resolve_product_of_powers():              changed = True
        if self.__check_resolve_product_of_constant_and_sum():    changed = True
        if self.__check_factor_out_of_sum():                      changed = True
        if self.__check_resolve_inverse_negations_in_sum():       changed = True
        if self.__insert_fixed_in_conj():                         changed = True
        if self.__insert_fixed_in_disj():                         changed = True
        if self.__check_trivial_xor():                            changed = True
        if self.__check_xor_same_mult_by_minus_one():             changed = True
        if self.__check_conj_zero_rule():                         changed = True
        if self.__check_conj_neg_xor_zero_rule():                 changed = True
        if self.__check_conj_neg_xor_minus_one_rule():            changed = True
        if self.__check_conj_negated_xor_zero_rule():             changed = True
        if self.__check_conj_xor_identity_rule():                 changed = True
        if self.__check_disj_xor_identity_rule():                 changed = True
        if self.__check_conj_neg_conj_identity_rule():            changed = True
        if self.__check_disj_disj_identity_rule():                changed = True
        if self.__check_conj_conj_identity_rule():                changed = True
        if self.__check_disj_conj_identity_rule():                changed = True
        if self.__check_disj_conj_identity_rule_2():              changed = True
        if self.__check_conj_disj_identity_rule():                changed = True
        if self.__check_disj_neg_disj_identity_rule():            changed = True
        if self.__check_disj_sub_disj_identity_rule():            changed = True
        if self.__check_disj_sub_conj_identity_rule():            changed = True
        if self.__check_conj_add_conj_identity_rule():            changed = True
        if self.__check_disj_disj_conj_rule():                    changed = True
        if self.__check_conj_conj_disj_rule():                    changed = True
        if self.__check_disj_disj_conj_rule_2():                  changed = True

        return changed


    # If this node is a negation and its child is one too, eliminates this pair
    # of negations. Here a negation is either a node explicitely marked as a
    # bitwise negation or a negation "~x" written as either "-x - 1" or
    # "-(x + 1)".
    def __eliminate_nested_negations_advanced(self):
        if self.type == NodeType.NEGATION:
            child = self.children[0]
            if child.type == NodeType.NEGATION:
                self.copy(child.children[0])
                return True

            node = child.__get_opt_transformed_negated()
            if node != None:
                self.copy(node)
                return True

            # If we have a sum starting with '-1', manipulate the remaining
            # terms to fit.
            if child.type == NodeType.SUM and child.children[0].__is_constant(-1):
                self.type = NodeType.SUM
                self.children = child.children[1:]

                for child in self.children: child.__multiply_by_minus_one()

                # If there is only one term left, we do not need the sum.
                assert(len(self.children) >= 1)
                if len(self.children) == 1: self.copy(self.children[0])

                return True

            return False

        child = self.__get_opt_transformed_negated()
        if child == None: return False

        if child.type == NodeType.NEGATION:
            self.copy(child.children[0])
            return True

        node = child.__get_opt_transformed_negated()
        if node != None:
            self.copy(node)
            return True

        return False

    # Multiply this node by the given factor.
    def __multiply(self, factor):
        if (factor - 1) % self.__modulus == 0: return

        if self.type == NodeType.CONSTANT:
            self.__set_and_reduce_constant(self.constant * factor)
            return

        if self.type == NodeType.SUM:
            for child in self.children: child.__multiply(factor)
            return

        if self.type == NodeType.PRODUCT:
            # Flatten a bit if necessary. If the first child is a product, it
            # might contain a constant factor.
            if self.children[0].type == NodeType.PRODUCT:
                self.children[1:1] = self.children[0].children[1:]
                self.children[0] = self.children[0].children[0]

            if self.children[0].type == NodeType.CONSTANT:
                self.children[0].__multiply(factor)
                if self.children[0].__is_constant(1):
                    del self.children[0]
                    if len(self.children) == 1: self.copy(self.children[0])
                elif self.children[0].__is_constant(0):
                    self.copy(self.children[0])
                return

            self.children.insert(0, self.__new_constant_node(factor))
            return

        # We need a new node for the multiplication.
        fac = self.__new_constant_node(factor)
        node = self.__new_node(NodeType.CONSTANT)
        node.copy(self)
        prod = self.__new_node_with_children(NodeType.PRODUCT, [fac, node])
        self.copy(prod)

    # Multiply this node by -1.
    def __multiply_by_minus_one(self):
        self.__multiply(-1)

    # If this node has the form "-x - 1" or "-(x + 1)", returns x. Otherwise
    # returns None.
    def __get_opt_transformed_negated(self):
        if self.type == NodeType.SUM: return self.__get_opt_transformed_negated_sum()
        if self.type == NodeType.PRODUCT: return self.__get_opt_transformed_negated_product()
        return None

    # If this node has the form "-x - 1", returns x. Otherwise returns None.
    # Requires that this node is a sum.
    def __get_opt_transformed_negated_sum(self):
        assert(self.type == NodeType.SUM)

        # Should not happen, but be sure.
        if len(self.children) < 2: return None

        # In fact we are checking for the form "-1 + (-1)*x". First check for
        # term -1.
        # TODO: Allow other constants/missing constant and respect the
        # remainder in the returned node?
        if not self.children[0].__is_constant(-1): return None

        # A node to store the result in case we have more terms.
        res = self.__new_node(NodeType.SUM)

        # Now check for the remaining terms.
        for i in range(1, len(self.children)):
            child = self.children[i]
            # Check for the factor '-1' in the product. If there is none, we
            # can add one.
            hasMinusOne = child.type == NodeType.PRODUCT and child.children[0].__is_constant(-1)

            if hasMinusOne:
                # This term is already multiplied by -1. If we only have one
                # additional factor, store that.
                assert(len(child.children) > 1)
                if len(child.children) == 2:
                    res.children.append(child.children[1])
                    continue

                # Otherwise create a new node for the product of the remaining
                # factors.
                res.children.append(self.__new_node_with_children(NodeType.PRODUCT, child.children[1:]))

            else:
                # In this case we have to multiply the term by -1.
                node = child.get_copy()
                node.__multiply_by_minus_one()
                res.children.append(node)

        assert(len(res.children) > 0)
        if len(res.children) == 1: return res.children[0]
        return res

    # If this node has the form "-(x + 1)", returns x. Otherwise returns None.
    # Requires that this node is a product.
    def __get_opt_transformed_negated_product(self):
        assert(self.type == NodeType.PRODUCT)

        # We need exactly two factors.
        if len(self.children) != 2: return None

        # In fact we are checking for the form "(-1)*(1 + x)". First check for
        # factor -1.
        if not self.children[0].__is_constant(-1): return None

        # Now check for the second factor.
        child1 = self.children[1]
        if child1.type != NodeType.SUM: return None

        # Check for the term '1' in the sum.
        # TODO: Allow other constants/missing constant and add the remainder to
        # the returned node?
        if not child1.children[0].__is_constant(1): return None

        # Should not happen, but be sure.
        if len(child1.children) < 2: return None

        # We have a transformed negation. If we only have one additional term,
        # return that.
        if len(child1.children) == 2: return child1.children[1]

        # Otherwise create a new node for the sum of the remaining terms.
        return self.__new_node_with_children(NodeType.SUM, child1.children[1:])


    # If this node is a bitwise negation and its parent is an arithmetic
    # operation, replace this node using either the formula ~x = -x - 1 or the
    # very similar formula ~x = -(x + 1). The other way round, if this node is
    # a negation written arithmetically and its parent is a bitwise operation,
    # transform it into a bitwise negation.
    def __check_bitwise_negations(self, parent):
        if self.type == NodeType.NEGATION:
            # If the parent is bitwise, we keep the bitwise negation.
            if parent != None and parent.__is_bitwise_op(): return False

            # Transform the bitwise negation if the child is a product or a
            # sum.
            # TODO: What about a power?

            if self.children[0].type == NodeType.PRODUCT:
                self.__substitute_bitwise_negation_product()
                return True

            if self.children[0].type == NodeType.SUM:
                self.__substitute_bitwise_negation_sum()
                return True

            return self.__substitute_bitwise_negation_generic(parent)

        # If the parent is arithmetic, we keep the transformed negation if we
        # have any.
        if parent == None or not parent.__is_bitwise_op(): return False

        child = self.__get_opt_transformed_negated()
        # This node is no transformed negation.
        if child == None: return False

        self.type = NodeType.NEGATION
        self.children = [child]

        return True

    # Returns true iff this node is a bitwise operation.
    def __is_bitwise_op(self):
        return self.type == NodeType.NEGATION or self.__is_bitwise_binop()

    # Returns true iff this node is a bitwise operation, but no negation.
    def __is_bitwise_binop(self):
        return self.type in [NodeType.CONJUNCTION, NodeType.EXCL_DISJUNCTION, NodeType.INCL_DISJUNCTION]

    # Returns true iff this node is an arithmetic operation.
    def __is_arithm_op(self):
        return self.type in [NodeType.SUM, NodeType.PRODUCT, NodeType.POWER]

    # Assuming that this node is a bitwise negation and its child is a product,
    # replace this node using the formula ~x = -x - 1.
    def __substitute_bitwise_negation_product(self):
        # Prepare the subtraction of 1.
        self.type = NodeType.SUM
        self.children.insert(0, self.__new_constant_node(-1))

        # Now multiply the product by -1.
        child = self.children[1]
        if child.children[0].type == NodeType.CONSTANT:
            child.children[0].__set_and_reduce_constant(-child.children[0].constant)
        else:
            child.children.insert(0, self.__new_constant_node(-1))

    # Assuming that this node is a bitwise negation and its child is a sum,
    # replace this node using the formula ~x = -(x + 1).
    def __substitute_bitwise_negation_sum(self):
        # Prepare the multiplication by -1.
        self.type = NodeType.PRODUCT
        self.children.insert(0, self.__new_constant_node(-1))

        # Now add 1 to the sum.
        child = self.children[1]
        if child.children[0].type == NodeType.CONSTANT:
            child.children[0].__set_and_reduce_constant(child.children[0].constant + 1)
        else:
            child.children.insert(0, self.__new_constant_node(1))

    # Assuming that this node is a bitwise negation, consider replacing this
    # node using the formula ~x = -x - 1.
    def __substitute_bitwise_negation_generic(self, parent):
        assert(self.type == NodeType.NEGATION)

        if parent == None: return False
        if parent.type != NodeType.SUM and parent.type != NodeType.PRODUCT: return False

        if parent.type == NodeType.PRODUCT:
            if len(parent.children) > 2 or parent.children[0].type != NodeType.CONSTANT:
                return False

        # -1*x.
        prod = self.__new_node_with_children(NodeType.PRODUCT, [self.__new_constant_node(-1), self.children[0]])

        # -1 + (-1*x).
        self.type = NodeType.SUM
        self.children = [self.__new_constant_node(-1), prod]

        return True


    # If this node is a conjunction, an exclusive or an inclusive disjunction,
    # check whether a power of 2 can be factored out of its children.
    # Note that, e.g., 2*x&2*y == 2*(x&y). But we additionally have the
    # following due to additional knowledge about oddness:
    #
    #     (a&2*x) -> (a/2&x), capping the constant a if necessary
    #     (a|2*x) -> (a/2|x) + 1 capping the constant a if necessary
    #     (a^2*x) -> (a/2^x) + 1 capping the constant a if necessary
    def __check_bitwise_powers_of_two(self):
        if not self.__is_bitwise_binop(): return False

        e = self.__get_max_factor_power_of_two_in_children()
        if e <= 0: return False

        c = None
        if self.children[0].type == NodeType.CONSTANT: c = self.children[0].constant

        # Divide the children and handle the remainders.
        add = None
        for child in self.children:
            rem = child.__divide_by_power_of_two(e)
            if add == None: add = rem
            else:
                if self.type == NodeType.CONJUNCTION: add &= rem
                elif self.type == NodeType.INCL_DISJUNCTION: add |= rem
                else: add ^= rem

        prod = self.__new_node(NodeType.PRODUCT)
        prod.children = [self.__new_constant_node(2**e), self.__get_shallow_copy()]
        self.copy(prod)

        # We may have to add  something if we have factored out (intendedly)
        # too much.
        if add % self.__modulus != 0:
            constNode = self.__new_constant_node(add)
            sumNode = self.__new_node_with_children(NodeType.SUM, [constNode, self.__get_shallow_copy()])
            self.copy(sumNode)

        return True

    # Returns the maximum exponent of a power of two that can be factored out
    # of each of this node's children. Requires that this node is a binary
    # bitwise operation. Additionally returns a constant that has to be added
    # due to a modification.
    def __get_max_factor_power_of_two_in_children(self, allowRem=True):
        assert(len(self.children) > 1)
        assert(self.__is_bitwise_binop() or self.type == NodeType.SUM)

        # In conjunctions we can factor out from negations since, e.g., ~(2*x)
        # is equivalent to -2*x - 1, which is an odd number, and hence we can
        # subtract 1 to get -2*x - 2 = 2*~x. Similarly for higher powers.
        withNeg = allowRem and self.__is_bitwise_binop()
        maxe = self.children[0].__get_max_factor_power_of_two(withNeg)

        if allowRem and self.children[0].type == NodeType.CONSTANT:
            # In conjunctions we can factor out anything from constants as long
            # as the remaining operands have zeros in the corresponding bits.
            # Similarly for disjunctions (inclusive or exclusive), but here we
            # have to add a constant later on.
            maxe = -1

        if maxe == 0: return 0

        for child in self.children[1:]:
            e = child.__get_max_factor_power_of_two(withNeg)
            if e == 0: return 0

            # Any number can be factored out of this child.
            if e == -1: continue

            maxe = e if maxe == -1 else min(maxe, e)

        return maxe

    # Returns the maximum exponent of a power of two that can be factored out
    # of this node. Returns -1 is any number can be factored out. If withNeg is
    # True, negations are considered too. Note that we can factor out powers of
    # 2 from negations if they appear in conjunctions with another operand that
    # is clearly divisible by this factor, since thereby we subtract a 1 from
    # an odd number which is conjuncted with an even number. Additionally
    # returns True iff a 1 is subtracted in this course.
    def __get_max_factor_power_of_two(self, allowRem):
        # NOTE: trailing_zeros() returns -1 for input 0. We use that to
        # indicate that we can factor out any arbitrary number in that case.
        if self.type == NodeType.CONSTANT: return trailing_zeros(self.constant)

        # TODO: Respect powers too.
        if self.type == NodeType.PRODUCT:
            return self.children[0].__get_max_factor_power_of_two(False)

        if self.type == NodeType.SUM:
            return self.__get_max_factor_power_of_two_in_children(allowRem)

        if allowRem and self.type == NodeType.NEGATION:
            return self.children[0].__get_max_factor_power_of_two(False)

        return 0

    # Divide this node by a power of two with given exponent.
    def __divide_by_power_of_two(self, e):
        if self.type == NodeType.CONSTANT:
            orig = self.constant
            self.constant >>= e
            return orig - (self.constant << e)

        if self.type == NodeType.PRODUCT:
            rem = self.children[0].__divide_by_power_of_two(e)
            assert(rem == 0)

            if self.children[0].__is_constant(1):
                del self.children[0]
                if len(self.children) == 1: self.copy(self.children[0])
            return 0

        if self.type == NodeType.SUM:
            add = 0
            for child in self.children:
                rem = child.__divide_by_power_of_two(e)
                if rem != 0:
                    assert(add == 0)
                    add = rem
            if self.children[0].__is_constant(0):
                del self.children[0]
                if len(self.children) == 1: self.copy(self.children[0])
            return add

        assert(self.type == NodeType.NEGATION)
        # ATTENTION: This is actually no correct division. It is only permitted
        # to be applied if the error in the division is taken into account in
        # the caller!
        rem = self.children[0].__divide_by_power_of_two(e)
        assert(rem == 0)
        return (1 << e) - 1


    # If this node is a product with a constant factor, check whether constants
    # in other factors can be made nicer since some largest may may have no
    # influence.
    def __check_beautify_constants_in_products(self):
        if self.type != NodeType.PRODUCT: return False
        if self.children[0].type != NodeType.CONSTANT: return False

        e = trailing_zeros(self.children[0].constant)
        if e <= 0: return False

        changed = False
        for child in self.children[1:]:
            ch = child.__check_beautify_constants(e)
            if ch: changed = True

        return changed

    # Knowing that the largest e bits have no influence for this node, figure
    # out whether to either set or unset all these irrelevant bits.
    def __check_beautify_constants(self, e):
        # TODO: Cover powers too.
        if self.__is_bitwise_op() or self.type in [NodeType.SUM, NodeType.PRODUCT]:
            changed = False
            for child in self.children:
                ch = child.__check_beautify_constants(e)
                if ch: changed = True

            return changed

        if self.type != NodeType.CONSTANT: return False

        orig = self.constant

        mask = (-1 % self.__modulus) >> e
        b = self.constant & (self.__modulus >> (e + 1))

        # Initially unset the irrelevant bits.
        self.constant &= mask

        # The largest relevant bit is set.
        if b > 0:
            # If the largest relevant bit is the only 1, we decide for the
            # positive number. Otherwise we set the irrelevant bits. As an
            # exception, we decide for -1 rather than 1 in order not to miss
            # negations.
            if popcount(self.constant) > 1 or b == 1: self.constant |= ~mask

        self.__reduce_constant()
        return self.constant != orig


    # If this node is a bitwise negation of a bitwise operation and at least
    # one of its operands is negated, move the negation in.
    def __check_move_in_bitwise_negations(self):
        if self.type != NodeType.NEGATION: return False

        childType = self.children[0].type
        if childType == NodeType.EXCL_DISJUNCTION:
            return self.__check_move_in_bitwise_negation_excl_disj()
        if childType in [NodeType.CONJUNCTION, NodeType.INCL_DISJUNCTION]:
            return self.__check_move_in_bitwise_negation_conj_or_incl_disj()

        return False

    # Requiring that this node is a bitwise negation of an inclusive
    # disjunction or a conjunction, move the negation in if at least one of its
    # operands is recursively negated.
    def __check_move_in_bitwise_negation_conj_or_incl_disj(self):
        assert(self.type == NodeType.NEGATION)

        child = self.children[0]
        if not child.__is_any_child_negated(): return False

        child.__negate_all_children()
        child.type = NodeType.INCL_DISJUNCTION if child.type == NodeType.CONJUNCTION else NodeType.CONJUNCTION
        self.copy(child)

        return True

    # Returns true iff one of this node's children is negated.
    def __is_any_child_negated(self):
        for child in self.children:
            if child.type == NodeType.NEGATION: return True

            node = child.__get_opt_transformed_negated()
            if node != None: return True

        return False

    # Apply bitwise negation to all children.
    def __negate_all_children(self):
        for child in self.children: child.__negate()

    # Apply bitwise negation to this node.
    def __negate(self):
        if self.type == NodeType.NEGATION:
            self.copy(self.children[0])
            return

        node = self.__get_opt_transformed_negated()
        if node != None:
            self.copy(node)
            return

        node = self.__new_node_with_children(NodeType.NEGATION, [self.get_copy()])
        self.copy(node)

    # Requiring that this node is a bitwise negation of an exclusive
    # disjunction, move the negation in if at least one of its operands is
    # recursively negated.
    def __check_move_in_bitwise_negation_excl_disj(self):
        assert(self.type == NodeType.NEGATION)

        child = self.children[0]
        n, _ = child.__get_recursively_negated_child()
        if n == None: return False

        n.__negate()
        self.copy(child)

        return True

    # Returns a recursively negated child with minimal negation depth, together
    # with the depth or None if there is none.
    def __get_recursively_negated_child(self, maxDepth=None):
        if self.type == NodeType.NEGATION: return self, 0

        node = self.__get_opt_transformed_negated()
        if node != None: return self, 0

        if maxDepth != None and maxDepth == 0: return None
        if not self.__is_bitwise_binop(): return None, None

        opt = None
        candidate = None
        nextMax = None if maxDepth == None else maxDepth - 1
        for child in self.children:
            _, d = child.__get_recursively_negated_child(nextMax)
            if d == None: continue

            # We are interested in recursively negated children of any depth.
            if maxDepth == None: return child, d + 1

            assert(opt == None or d < opt)
            opt = d
            candidate = child
            nextMax = opt - 1

        return candidate, opt


    # If this node is an exclusive disjunction involving at least two
    # negations, flip negations in pairs, since, e.g., "~x^~y^z" is equivalent
    # to "x^y^z".
    def __check_bitwise_negations_in_excl_disjunctions(self):
        if self.type != NodeType.EXCL_DISJUNCTION: return False

        neg = None
        changed = False

        for child in self.children:
            if not child.__is_negated(): continue

            if neg == None:
                neg = child
                continue

            neg.__negate()
            child.__negate()
            neg = None
            changed = True

        return changed

    # Returns true iff this node is negated, i.e., it is a bitwise negation or
    # an arithmetically written negation.
    def __is_negated(self):
        if self.type == NodeType.NEGATION: return True
        node = self.__get_opt_transformed_negated()
        return node != None


    # If this node is a power, check whether we can extract a constant factor
    # out of it.
    def __check_rewrite_powers(self, parent):
        if self.type != NodeType.POWER: return False

        exp = self.children[1]
        if exp.type != NodeType.CONSTANT: return False

        base = self.children[0]
        if base.type != NodeType.PRODUCT: return False
        if base.children[0].type != NodeType.CONSTANT: return False

        const = self.__power(base.children[0].constant, exp.constant)
        del base.children[0]
        if len(base.children) == 1: base.copy(base.children[0])

        if const == 1: return True

        if parent != None and parent.type == NodeType.PRODUCT:
            if parent.children[0].type == NodeType.PRODUCT:
                parent.children[0].__set_and_reduce_constant(parent.children[0].constant * const)
            else: parent.children.insert(0, self.__new_constant_node(const))
        else:
            prod = self.__new_node(NodeType.PRODUCT)
            prod.children.append(self.__new_constant_node(const))
            prod.children.append(self.__get_shallow_copy())
            self.copy(prod)

        return True


    # If this node is a product involving powers with coincident bases, merge
    # these powers into one. Moreover merge factors that occur multiple times.
    def __check_resolve_product_of_powers(self):
        if self.type != NodeType.PRODUCT: return False

        changed = False
        start = int(self.children[0].type == NodeType.CONSTANT)

        for i in range(len(self.children) -1, start, -1):
            child = self.children[i]

            merged = False
            for j in range(start, i):
                child2 = self.children[j]

                if child2.type == NodeType.POWER:
                    base2 = child2.children[0]
                    exp2 = child2.children[1]

                    if base2.equals(child):
                        exp2.__add_constant(1)
                        del self.children[i]
                        changed = True
                        break

                    if child.type == NodeType.POWER and base2.equals(child.children[0]):
                        exp2.__add(child.children[1])
                        del self.children[i]
                        changed = True
                        break

                # NOTE: We intentionally repeat the combination power-power,
                # since we may have powers of powers.

                if child.type == NodeType.POWER:
                    base = child.children[0]
                    exp = child.children[1]

                    if base.equals(child2):
                        exp.__add_constant(1)
                        self.children[j] = self.children[i]
                        del self.children[i]
                        changed = True

                    break

                if child.equals(child2):
                    self.children[j] = self.__new_node_with_children(NodeType.POWER, [child, self.__new_constant_node(2)])
                    del self.children[i]
                    changed = True
                    break

        if len(self.children) == 1: self.copy(self.children[0])

        return changed

    # Adds the given node to this node.
    def __add(self, other):
        if self.type == NodeType.CONSTANT:
            constant = self.constant
            self.copy(other.get_copy())
            self.__add_constant(constant)
            return

        if other.type == NodeType.CONSTANT:
            self.__add_constant(other.constant)
            return

        if self.type == NodeType.SUM:
            self.__add_to_sum(other)
            return

        if other.type == NodeType.SUM:
            node = other.get_copy()
            node.__add_to_sum(self)
            self.copy(node)
            return

        node = self.__new_node_with_children(NodeType.SUM, [self.get_copy(), other.get_copy()])
        self.copy(node)
        self.__merge_similar_nodes_sum()

    # Add the given constant to this node.
    def __add_constant(self, constant):
        if self.type == NodeType.CONSTANT:
            self.__set_and_reduce_constant(self.constant + constant)
            return

        if self.type == NodeType.SUM:
            # May happen in intermediate states, e.g., factorize_sums(), that
            # there is no child yet.
            if len(self.children) > 0 and self.children[0].type == NodeType.CONSTANT:
                self.children[0].__add_constant(constant)
                return

            self.children.insert(0, self.__new_constant_node(constant))
            return

        node = self.__new_node_with_children(NodeType.SUM, [self.__new_constant_node(constant), self.get_copy()])
        self.copy(node)

    # Add the given node to this node, which is assumed to be a sum. The given
    # node is required not to be a constant.
    def __add_to_sum(self, other):
        assert(self.type == NodeType.SUM)
        assert(other.type != NodeType.CONSTANT)

        if other.type == NodeType.SUM:
            for ochild in other.children:
                if ochild.type == NodeType.CONSTANT: self.__add_constant(ochild.constant)
                else: self.children.append(ochild.get_copy())

        # NOTE: We do not check whether node can be merged with a term,
        # since __merge_similar_nodes_sum() will be called afterwards.
        else: self.children.append(other.get_copy())

        self.__merge_similar_nodes_sum()


    # If this node is a product of a constant and a sum, move the
    # multiplication with the constant into the sum.
    def __check_resolve_product_of_constant_and_sum(self):
        if self.type != NodeType.PRODUCT: return False

        # Should not happen, but be sure.
        if len(self.children) < 2: return False

        child0 = self.children[0]
        # The first factor is no constant.
        if child0.type != NodeType.CONSTANT: return False

        child1 = self.children[1]
        # The second factor is no sum.
        if child1.type != NodeType.SUM: return False

        # We have a product of a constant and a sum. Resolve it.

        constant = child0.constant
        sumNode = self
        if len(self.children) == 2: self.copy(child1)
        else:
            del self.children[0]
            sumNode = self.children[0]

        for i in range(len(sumNode.children)):
            if sumNode.children[i].type == NodeType.CONSTANT:
                sumNode.children[i].__set_and_reduce_constant(sumNode.children[i].constant * constant)

            elif sumNode.children[i].type == NodeType.PRODUCT:
                first = sumNode.children[i].children[0]
                if first.type == NodeType.CONSTANT:
                    first.__set_and_reduce_constant(first.constant * constant)
                else:
                    sumNode.children[i].children.insert(0, sumNode.__new_constant_node(constant))

            else:
                factors = [sumNode.__new_constant_node(constant), sumNode.children[i]]
                sumNode.children[i] = sumNode.__new_node_with_children(NodeType.PRODUCT, factors)

        return True


    # If this node is a sum, check whether we can factor out common
    # (non-constant) factors of its terms.
    def __check_factor_out_of_sum(self):
        # This is not a sum.
        if self.type != NodeType.SUM or len(self.children) <= 1: return False

        factors = []
        while True:
            factor = self.__try_factor_out_of_sum()
            if factor == None: break
            factors.append(factor)

        if len(factors) == 0: return False

        prod = self.__new_node_with_children(NodeType.PRODUCT, factors + [self.get_copy()])
        self.copy(prod)
        return True

    # For this node which is a sum, check whether we can factor out a common
    # (non-constant) factor of its terms.
    def __try_factor_out_of_sum(self):
        assert(self.type == NodeType.SUM)
        assert(len(self.children) > 1)

        factor = self.__get_common_factor_in_sum()
        if factor == None: return None

        for child in self.children: child.__eliminate_factor(factor)

        return factor

    # Returns a factor, if existent, which appears in all children and hence
    # can be factored out.
    def __get_common_factor_in_sum(self):
        assert(self.type == NodeType.SUM)

        # It is enough to consider the first child and check for all of its
        # factors whether they appear in the other terms too.

        first = self.children[0]

        if first.type == NodeType.PRODUCT:
            for child in first.children:
                if child.type == NodeType.CONSTANT: continue
                if self.__has_factor_in_remaining_children(child):
                    return child.get_copy()

                if child.type == NodeType.POWER:
                    # Only factor out from a power if the exponent is a
                    # (nonzero) integer in order to avoid disambiguous
                    # behaviour in a case where a power can actually be
                    # simplified to 0**0.
                    exp = child.children[1]
                    if exp.type == NodeType.CONSTANT and not exp.__is_constant(0):
                        base = child.children[0]
                        if self.__has_factor_in_remaining_children(base):
                            return base.get_copy()
            return None

        if first.type == NodeType.POWER:
            # Again, only factor out from a power if the exponent is a
            # (nonzero) integer.
            exp = first.children[1]
            if exp.type == NodeType.CONSTANT and not exp.__is_constant(0):
                base = first.children[0]
                if base.type != NodeType.CONSTANT and self.__has_factor_in_remaining_children(base):
                    return base.get_copy()
            return None

        if first.type != NodeType.CONSTANT and self.__has_factor_in_remaining_children(first):
            return first.get_copy()

        return None

    # Returns true iff the given node can be factored out from all children but
    # the first one.
    def __has_factor_in_remaining_children(self, factor):
        assert(self.type == NodeType.SUM)

        for child in self.children[1:]:
            if not child.__has_factor(factor): return False

        return True

    # Returns true iff the given node can be factored out from this node.
    def __has_factor(self, factor):
        if self.type == NodeType.PRODUCT: return self.__has_factor_product(factor)

        if self.type == NodeType.POWER:
            # Again, only factor out from a power if the exponent is a
            # (nonzero) integer.
            exp = self.children[1]
            if exp.type == NodeType.CONSTANT and not exp.__is_constant(0):
                # TODO: In fact we can check whether factor is a factor of the
                # base, then we might have to split the power.
                return self.children[0].equals(factor)

        return self.equals(factor)

    # Returns true iff the given node can be factored out from this node, which
    # is required to be a product.
    def __has_factor_product(self, factor):
        assert(self.type == NodeType.PRODUCT)

        for child in self.children:
            if child.equals(factor): return True
            if child.type == NodeType.POWER:
                # Again, only factor out from a power if the exponent is a
                # (nonzero) integer.
                exp = child.children[1]
                if exp.type == NodeType.CONSTANT and not exp.__is_constant(0):
                    if child.children[0].equals(factor): return True

        return False

    # Returns true iff this node has a child equal to the given node.
    def __has_child(self, node):
        return self.__get_index_of_child(node) != None

    # If this node has a child equal to the given node, returns its index.
    # Otherwise returns None.
    def __get_index_of_child(self, node):
        for i in range(len(self.children)):
            if self.children[i].equals(node): return i
        return None

    # If this node has a child equal to the negation of the given node, returns
    # its index. Otherwise returns None.
    def __get_index_of_child_negated(self, node):
        for i in range(len(self.children)):
            if self.children[i].equals_negated(node): return i
        return None

    # Factor out the given node from this node.
    def __eliminate_factor(self, factor):
        if self.type == NodeType.PRODUCT:
            self.__eliminate_factor_product(factor)
            return

        if self.type == NodeType.POWER:
            self.__eliminate_factor_power(factor)
            return

        assert(self.equals(factor))
        c = self.__new_constant_node(1)
        self.copy(c)

    # Factor out the given node from this product node.
    def __eliminate_factor_product(self, factor):
        assert(self.type == NodeType.PRODUCT)

        for i in range(len(self.children)):
            child = self.children[i]

            if child.equals(factor):
                del self.children[i]
                if len(self.children) == 1: self.copy(self.children[0])
                return

            if child.type == NodeType.POWER and child.children[0].equals(factor):
                child.__decrement_exponent()
                return

        assert(False) # pragma: no cover

    # Factor out the given node from this power node.
    def __eliminate_factor_power(self, factor):
        assert(self.type == NodeType.POWER)

        if self.equals(factor):
            self.copy(self.__new_constant_node(1))
            return

        assert(self.children[0].equals(factor))
        self.__decrement_exponent()

    # Decrement the exponent of this power node.
    def __decrement_exponent(self):
        assert(self.type == NodeType.POWER)
        assert(len(self.children) == 2)

        self.children[1].__decrement()

        # If the exponent is now 1, we can get rid of the power node.
        if self.children[1].__is_constant(1): self.copy(self.children[0])

        # If the exponent is now 0 (and hence we actually already had a trivial
        # power before, which is to avoid), the whole power resolves to 1.
        elif self.children[1].__is_constant(0):
            self.copy(self.__new_constant_node(1))

    # Decrement the expression corresponding to this node by 1.
    def __decrement(self):
        self.__add_constant(-1)


    # If this node is a sum, check whether there are terms which eliminate each
    # other due to bitwise negations. Apply the following rules:
    #
    #     ~x + x -> -1
    #     a*~x + a*x -> -a
    def __check_resolve_inverse_negations_in_sum(self):
        if self.type != NodeType.SUM: return False

        changed = False
        const = 0

        i = len(self.children)
        while i > 1:
            i -= 1
            first = self.children[i]

            for j in range(i):
                second = self.children[j]

                if first.equals_negated(second):
                    del self.children[i]
                    del self.children[j]
                    # Decrement i since child j < i has been removed.
                    i -= 1
                    const -= 1
                    changed = True
                    break

                if first.type != NodeType.PRODUCT: continue
                if second.type != NodeType.PRODUCT: continue

                indices = first.__get_only_differing_child_indices(second)
                if indices == None: continue

                firstIdx, secIdx = indices
                if first.children[firstIdx].equals_negated(second.children[secIdx]):
                    del self.children[i]
                    del second.children[secIdx]
                    if len(second.children) == 1: second.copy(second.children[0])
                    second.__multiply_by_minus_one()
                    changed = True
                    break

        # Adapt the constant.
        if len(self.children) > 0 and self.children[0].type == NodeType.CONSTANT:
            self.children[0].__set_and_reduce_constant(self.children[0].constant + const)
        else: self.children.insert(0, self.__new_constant_node(const))
        if len(self.children) > 1 and self.children[0].__is_constant(0): del self.children[0]

        if len(self.children) == 1: self.copy(self.children[0])
        elif len(self.children) == 0: self.copy(self.__new_constant_node(0))

        return changed


    # Expand all nodes that are products of sums or powers of sums with small
    # enough exponents by multiplying their factors or multiplying their bases
    # the corresponding numbers of times, resp. If restrictedScope is True,
    # stop at nodes that are no sums, products or powers, i.e., we want one
    # single resulting sum.
    def expand(self, restrictedScope=False):
        if restrictedScope and self.type not in [NodeType.SUM, NodeType.PRODUCT, NodeType.POWER]:
            return False

        changed = False
        if restrictedScope and self.type == NodeType.POWER:
            changed = self.children[0].expand(restrictedScope)
        else:
            for c in self.children:
                if c.expand(restrictedScope): changed = True

        if changed:
            # If any child has changed, inspect the constants since it might be
            # that any child has been reduced to a constant, maybe even zero.
            self.__inspect_constants()
            # Additionally, if this node is a sum, check whether the hierarchy
            # can be flattened due to children being expanded to sums.
            if self.type == NodeType.SUM: self.__flatten_binary_generic()

        if self.__check_expand(): changed = True
        if changed and self.type == NodeType.SUM: self.__merge_similar_nodes_sum()

        return changed

    # If this node is a product involving a sum or a power of a sum with small
    # enough exponent, expand it by multiplying its factors or multiplying its
    # base the corresponding number of times, resp.
    def __check_expand(self):
        if self.type == NodeType.PRODUCT: return self.__check_expand_product()
        if self.type == NodeType.POWER: return self.__check_expand_power()

        return False

    # If this product node involves a sum, expand it by multiplying its
    # factors.
    def __check_expand_product(self):
        assert(self.type == NodeType.PRODUCT)

        assert(len(self.children) > 0)
        # There is only one factor. Should not happen.
        if len(self.children) == 1: return False

        # There is no factor which is a sum.
        if not self.__has_sum_child(): return False

        self.__expand_product()
        return True

    # Returns true iff this node has a child with the given type.
    def __has_sum_child(self):
        return self.__get_first_sum_index() != None

    # Returns the index of the first child that is a sum, or None if there is
    # none.
    def __get_first_sum_index(self):
        for i in range(len(self.children)):
            if self.children[i].type == NodeType.SUM: return i
        return None

    # Expand this node, which is assumed to be a product involving a sum, by
    # multiplying its factors.
    def __expand_product(self):
        while True:
            sumIdx = self.__get_first_sum_index()
            if sumIdx == None: break

            node = self.children[sumIdx].get_copy()
            assert(node.type == NodeType.SUM)

            repeat = False
            for i in range(len(self.children)):
                if i == sumIdx: continue
                node.__multiply_sum(self.children[i])

                if node.__is_constant(0): break

                # In some corner cases it can happen that everything is merged
                # into, e.g., a constant.
                if node.type != NodeType.SUM:
                    self.children[sumIdx] = node
                    for j in range(i, -1, -1):
                        if j == sumIdx: continue
                        del self.children[j]
                    repeat = True
                    break

            if not repeat: break

        if len(node.children) == 1: self.copy(node.children[0])
        else: self.copy(node)

    # Multiply this node, which is assumed to be a sum, with the given node.
    def __multiply_sum(self, other):
        assert(self.type == NodeType.SUM)

        if other.type == NodeType.SUM:
            self.__multiply_sum_with_sum(other, True)
            return

        constant = 0

        for i in range(len(self.children) - 1, -1, -1):
            child = self.children[i]
            child.__multiply_with_node_no_sum(other)

            # If the product is a constant, add it to const and drop the child.
            if child.type == NodeType.CONSTANT:
                constant = self.__get_reduced_constant(constant + child.constant)
                if i > 0: del self.children[i]
                continue

        if self.children[0].type == NodeType.CONSTANT:
            if constant == 0: del self.children[0]
            else: self.children[0].constant = constant
        elif constant != 0: self.children.insert(0, self.__new_constant_node(constant))

        self.__merge_similar_nodes_sum()
		
        # NOTE: The type may have changed at the call to merge_similar_nodes().
        if self.type == NodeType.SUM and len(self.children) == 0: self.copy(self.__new_constant_node(0))

    # Multiply this node, which is assumed to be a sum, with the given sum
    # node.
    def __multiply_sum_with_sum(self, other, keepSum=False):
        assert(self.type == NodeType.SUM)
        assert(other.type == NodeType.SUM)

        children = list(self.children)
        self.children = []

        for child in children:
            for ochild in other.children:
                prod = child.__get_product_with_node(ochild)

                # If the product is a constant, check whether we already have a
                # constant term. If the product is zero, neglect it.
                if prod.type == NodeType.CONSTANT:
                    if prod.__is_constant(0): continue

                    if len(self.children) > 0 and self.children[0].type == NodeType.CONSTANT:
                        self.children[0].__set_and_reduce_constant(self.children[0].constant + prod.constant)
                        continue

                    self.children.insert(0, prod)
                    continue

                self.children.append(prod)

        self.__merge_similar_nodes_sum()

        if len(self.children) == 1:
            if not keepSum: self.copy(self.children[0])
        elif len(self.children) == 0: self.copy(self.__new_constant_node(0))

    # Multiply this node by the given factor.
    def __get_product_with_node(self, other):
        if self.type == NodeType.CONSTANT:
            return self.__get_product_of_constant_and_node(other)

        if other.type == NodeType.CONSTANT:
            return other.__get_product_of_constant_and_node(self)

        if self.type == NodeType.PRODUCT:
            if other.type == NodeType.PRODUCT: return self.__get_product_of_products(other)
            if other.type == NodeType.POWER: return self.__get_product_of_product_and_power(other)
            return self.__get_product_of_product_and_other(other)

        if self.type == NodeType.POWER:
            if other.type == NodeType.POWER: return self.__get_product_of_powers(other)
            if other.type == NodeType.PRODUCT: return other.__get_product_of_product_and_power(self)
            return self.__get_product_of_power_and_other(other)

        if other.type == NodeType.PRODUCT: return other.__get_product_of_product_and_other(self)
        if other.type == NodeType.POWER: return other.__get_product_of_power_and_other(self)
        return self.__get_product_generic(other)

    # Returns the product of this constant node and the given node.
    def __get_product_of_constant_and_node(self, other):
        assert(self.type == NodeType.CONSTANT)

        node = other.get_copy()
        node.__multiply(self.constant)
        return node

    # Returns the product of this and the given node which are both assumed to
    # be products.
    def __get_product_of_products(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type == NodeType.PRODUCT)

        node = self.get_copy()
        for ochild in other.children:
            # We have a constant; should be the first child.
            if ochild.type == NodeType.CONSTANT:
                # If we already have a constant, merge it into that.
                if node.children[0].type == NodeType.CONSTANT:
                    node.children[0].__set_and_reduce_constant(node.children[0].constant * ochild.constant)

                    # If the constant is now zero, everything is zero.
                    if node.children[0].__is_constant(0): return node.children[0]

                else: node.children.insert(0, ochild.get_copy())
                continue

            # We have a power. Check whether we have a child with same base.
            if ochild.type == NodeType.POWER:
                node.__merge_power_into_product(ochild)
                continue

            # Check whether the factor coincides with a factor of this node.
            merged = False
            for i in range(len(node.children)):
                child = node.children[i]
                if child.equals(ochild):
                    node.children[i] = self.__new_node_with_children(NodeType.POWER, [child, self.__new_constant_node(2)])
                    merged = True
                    break

            if merged: continue

            # We could not merge the other child into any child. Add it as a
            # factor. Note that we do not expect ochild to be a product.
            node.children.append(ochild.get_copy())

        # Remove trivial factor, if existent.
        if node.children[0].__is_constant(1): del node.children[0]

        # At merging, it can have happened that children vanished due to
        # powers' exponents resolving to zero. Check for that.
        if len(node.children) == 1: return node.children[0]
        if len(node.children) == 0: return self.__new_constant_node(1)
        return node

    # Merge the given power node into this node, which is assumed to be a
    # product.
    def __merge_power_into_product(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type == NodeType.POWER)

        base = other.children[0]

        for i in range(len(self.children)):
            child = self.children[i]

            if child.equals(base):
                self.children[i] = other.get_copy()
                # Increment exponent by 1.
                self.children[i].children[1].__add_constant(1)

                # If the exponent is now zero, the power resolves to 1.
                if self.children[i].children[1].__is_constant(0): del self.children[i]
                return

            if child.type == NodeType.POWER and child.children[0].equals(base):
                # Sum up exponents.
                child.children[1].__add(other.children[1])

                # If the exponent is now zero, the power resolves to 1.
                if child.children[1].__is_constant(0): del self.children[i]
                return

        # We could not merge the power into any child. Add it as a
        # factor.
        self.children.append(other.get_copy())

    # Returns the product of this and the given node which are both assumed to
    # be powers.
    def __get_product_of_powers(self, other):
        assert(self.type == NodeType.POWER)
        assert(other.type == NodeType.POWER)

        if self.children[0].equals(other.children[0]):
            node = self.get_copy()
            # Sum up exponents.
            node.children[1].__add(other.children[1])

            # If the exponent is now zero, the power resolves to 1.
            if node.children[1].__is_constant(0): return self.__new_constant_node(1)

            # If the exponent is now one, the power resolves to its base.
            if node.children[1].__is_constant(1): return node.children[0]

            return node

        return self.__new_node_with_children(NodeType.PRODUCT, [self.get_copy(), other.get_copy()])

    # Returns the product of this node, which is assumed to be a product, and
    # the given node, which is assumed to be a power.
    def __get_product_of_product_and_power(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type == NodeType.POWER)

        node = self.get_copy()
        node.__merge_power_into_product(other)

        # At merging, it can have happened that children vanished due to
        # powers' exponents resolving to zero. Check for that.
        if len(node.children) == 1: return node.children[0]
        # NOTE: Should not happen, but be sure.
        if len(node.children) == 0: return self.__new_constant_node(1)
        return node

    # Returns the product of this node, which is assumed to be a product, and
    # the given node, which is assumed to neither a constant nor a product nor
    # a power.
    def __get_product_of_product_and_other(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])

        node = self.get_copy()

        # Check whether any factor equals the other node.
        for i in range(len(node.children)):
            child = node.children[i]

            # If the child coincides with the other node, we now have a power
            # with exponent 2.
            if child.equals(other):
                node.children[i] = self.__new_node_with_children(NodeType.POWER, [child.get_copy(), self.__new_constant_node(2)])
                return node

            if child.type == NodeType.POWER and child.children[0].equals(other):
                # Increment exponent.
                child.children[1].__add_constant(1)

                # If the exponent is now zero, the power resolves to 1.
                if child.children[1].__is_constant(0):
                    del node.children[i]
                    if len(node.children) == 1: node = self.children[0]
                return node

        # We could not merge the node into any child. Add it as a
        # factor.
        node.children.append(other.get_copy())
        return node

    # Returns the product of this node, which is assumed to be a power, and
    # the given node, which is assumed to neither a constant nor a product nor
    # a power.
    def __get_product_of_power_and_other(self, other):
        assert(self.type == NodeType.POWER)
        assert(other.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])

        # Check whether the power's base coincides with the given node.
        if self.children[0].equals(other):
            node = self.get_copy()
            # Increment exponent.
            node.children[1].__add_constant(1)

            # If the exponent is now zero, the power resolves to 1.
            if node.children[1].__is_constant(0): return self.__new_constant_node(1)
            return node

        # We could not merge the given node into the base. Create a product
        # node.
        return  self.__new_node_with_children(NodeType.PRODUCT, [self.get_copy(), other.get_copy()])

    # Returns the product of this and the given node which are both neither
    # constants nor products nor powers.
    def __get_product_generic(self, other):
        assert(self.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])
        assert(other.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])

        if self.equals(other):
            return self.__new_node_with_children(NodeType.POWER, [self.get_copy(), self.__new_constant_node(2)])
        return self.__new_node_with_children(NodeType.PRODUCT, [self.get_copy(), other.get_copy()])

    # Multiply this node by the given factor, which is assumed to be no sum.
    def __multiply_with_node_no_sum(self, other):
        assert(other.type != NodeType.SUM)

        if self.type == NodeType.CONSTANT:
            self.copy(self.__get_product_of_constant_and_node(other))
            return

        if other.type == NodeType.CONSTANT:
            self.__multiply(other.constant)
            return

        if self.type == NodeType.PRODUCT:
            if other.type == NodeType.PRODUCT: self.__multiply_product_with_product(other)
            elif other.type == NodeType.POWER: self.__multiply_product_with_power(other)
            else: self.__multiply_product_with_other(other)
            return

        if self.type == NodeType.POWER:
            if other.type == NodeType.POWER: self.__multiply_power_with_power(other)
            elif other.type == NodeType.PRODUCT: self.copy(other.__get_product_of_product_and_power(self))
            else: self.__multiply_power_with_other(other)
            return

        if other.type == NodeType.PRODUCT: self.copy(other.__get_product_of_product_and_other(self))
        elif other.type == NodeType.POWER: self.copy(other.__get_product_of_power_and_other(self))
        else: self.__multiply_generic(other)

    # Multiply of this and the given node which are both assumed to be products.
    def __multiply_product_with_product(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type == NodeType.PRODUCT)

        for ochild in other.children:
            # We have a constant; should be the first child.
            if ochild.type == NodeType.CONSTANT:
                # If we already have a constant, merge it into that.
                if self.children[0].type == NodeType.CONSTANT:
                    self.children[0].__set_and_reduce_constant(self.children[0].constant * ochild.constant)

                    # If the constant is now zero, everything is zero.
                    if self.children[0].__is_constant(0):
                        self.copy(self.children[0])
                        return

                else: self.children.insert(0, ochild.get_copy())
                continue

            # We have a power. Check whether we have a child with same base.
            if ochild.type == NodeType.POWER:
                self.__merge_power_into_product(ochild)
                continue

            # Check whether the factor coincides with a factor of this node.
            merged = False
            for i in range(len(self.children)):
                child = self.children[i]
                if child.equals(ochild):
                    self.children[i] = self.__new_node_with_children(NodeType.POWER, [child, self.__new_constant_node(2)])
                    merged = True
                    break

            if merged: continue

            # We could not merge the other child into any child. Add it as a
            # factor. Note that we do not expect ochild to be a product.
            self.children.append(ochild.get_copy())

        # At merging, it can have happened that children vanished due to
        # powers' exponents resolving to zero. Check for that.
        if len(self.children) == 1: self.copy(self.children[0])
        elif len(self.children) == 0: self.copy(self.__new_constant_node(1))

    # Multiply this and the given node which are both assumed to be powers.
    def __multiply_power_with_power(self, other):
        assert(self.type == NodeType.POWER)
        assert(other.type == NodeType.POWER)

        if self.children[0].equals(other.children[0]):
            # Sum up exponents.
            self.children[1].__add(other.children[1])

            # If the exponent is now zero, the power resolves to 1.
            if self.children[1].__is_constant(0): self.copy(self.__new_constant_node(1))

            # If the exponent is now one, the power resolves to its base.
            elif self.children[1].__is_constant(1): self.copy(self.children[0])

        else:
            self.copy(self.__new_node_with_children(NodeType.PRODUCT, [self.__get_shallow_copy(), other.get_copy()]))

    # Multiply this node, which is assumed to be a product, and the given node,
    # which is assumed to be a power.
    def __multiply_product_with_power(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type == NodeType.POWER)

        self.__merge_power_into_product(other)

        # At merging, it can have happened that children vanished due to
        # powers' exponents resolving to zero. Check for that.
        if len(self.children) == 1: self.copy(self.children[0])
        # NOTE: Should not happen, but be sure.
        elif len(self.children) == 0: return self.copy(self.__new_constant_node(1))

    # Multiply this node, which is assumed to be a product, and the given node,
    # which is assumed to neither a constant nor a product nor a power.
    def __multiply_product_with_other(self, other):
        assert(self.type == NodeType.PRODUCT)
        assert(other.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])

        # Check whether any factor equals the other node.
        for i in range(len(self.children)):
            child = self.children[i]

            # If the child coincides with the other node, we now have a power
            # with exponent 2.
            if child.equals(other):
                self.children[i] = self.__new_node_with_children(NodeType.POWER, [child.__get_shallow_copy(), self.__new_constant_node(2)])
                return

            if child.type == NodeType.POWER and child.children[0].equals(other):
                # Increment exponent.
                child.children[1].__add_constant(1)

                # If the exponent is now zero, the power resolves to 1.
                if child.children[1].__is_constant(0):
                    del self.children[i]
                    if len(self.children) == 1: self.copy(self.children[0])
                return

        # We could not merge the node into any child. Add it as a
        # factor.
        self.children.append(other.get_copy())

    # Multiply this node, which is assumed to be a power, and the given node,
    # which is assumed to neither a constant nor a product nor a power.
    def __multiply_power_with_other(self, other):
        assert(self.type == NodeType.POWER)
        assert(other.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])

        # Check whether the power's base coincides with the given node.
        if self.children[0].equals(other):
            # Increment exponent.
            self.children[1].__add_constant(1)

            # If the exponent is now zero, the power resolves to 1.
            if self.children[1].__is_constant(0): self.copy(self.__new_constant_node(1))
            return

        # We could not merge the given node into the base. Create a product.
        # node.
        self.copy(self.__new_node_with_children(NodeType.PRODUCT, [self.__get_shallow_copy(), other.get_copy()]))

    # Multiply this with the given node which are both neither constants nor
    # products nor powers.
    def __multiply_generic(self, other):
        assert(self.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])
        assert(other.type not in [NodeType.CONSTANT, NodeType.PRODUCT, NodeType.POWER])

        if self.equals(other):
            self.copy(self.__new_node_with_children(NodeType.POWER, [self.__get_shallow_copy(), self.__new_constant_node(2)]))
        else: self.copy(self.__new_node_with_children(NodeType.PRODUCT, [self.__get_shallow_copy(), other.get_copy()]))

    # If this power node is a power of a sum with small enough exponent, expand
    # it by multiplying its base the corresponding number of times.
    def __check_expand_power(self):
        assert(self.type == NodeType.POWER)

        # The base is not a sum.
        if self.children[0].type != NodeType.SUM: return False

        expNode = self.children[1]
        # The power's exponent is not constant.
        if expNode.type != NodeType.CONSTANT: return False

        # To be safe, make sure that the constant is positive and
        # modulo-reduced.
        exp = expNode.constant % self.__modulus
        # The power's exponent is too large.
        if exp > MAX_EXPONENT_TO_EXPAND: return False

        self.__expand_power(exp)
        return True

    # Expand this node, which is assumed to be a power of a sum with constant
    # exponent, by multiplying its base the corresponding number of times.
    def __expand_power(self, exp):
        base = self.children[0]
        node = base.get_copy()
        assert(node.type == NodeType.SUM)

        for i in range(1, exp):
            node.__multiply_sum_with_sum(base, True)

            if node.__is_constant(0): break

        if len(node.children) == 1: self.copy(node.children[0])
        else: self.copy(node)


    # For all sum nodes, check whether we can factor out common nodes. Returns
    # true iff anything has changed. If restrictedScope is True, only this node
    # is considered.
    def factorize_sums(self, restrictedScope=False):
        if restrictedScope: return self.__check_factorize_sum()

        changed = False
        for c in self.children:
            if c.factorize_sums(): changed = True

        if self.__check_factorize_sum(): changed = True
        return changed

    # If this node is a sum, check whether we can factorize it such that we
    # obtain linear sums as factors.
    def __check_factorize_sum(self):
        # This is not a sum.
        if self.type != NodeType.SUM or len(self.children) <= 1: return False

        # Linear parts can fully be simplified using the linear simplifier.
        if self.is_linear(): return False

        nodes, nodesToTerms, termsToNodes = self.__collect_all_factors_of_sum()
        nodesTriviality = self.__determine_nodes_triviality(nodes)
        nodesOrder = self.__determine_nodes_order(nodes)

        partition = Batch([], [], set(range(len(self.children))), nodesToTerms,
                          termsToNodes, nodesTriviality, nodesOrder)

        # Nothing to factor out.
        if partition.is_trivial(): return False

        self.copy(self.__node_from_batch(partition, nodes, termsToNodes))
        return True

    # Store the factors of this node in the given lists.
    def __collect_all_factors_of_sum(self):
        nodes = []
        nodesToTerms = []
        termsToNodes = []

        for i in range(len(self.children)):
            termsToNodes.append(set([]))
            term = self.children[i]
            term.__collect_factors(i, 1, nodes, nodesToTerms, termsToNodes)

        assert(len(nodes) == len(nodesToTerms))
        return nodes, nodesToTerms, termsToNodes

    # Store the factors of this node in the given lists.
    def __collect_factors(self, i, multitude, nodes, nodesToTerms, termsToNodes):
        if self.type == NodeType.PRODUCT:
            for factor in self.children:
                factor.__collect_factors(i, multitude, nodes, nodesToTerms, termsToNodes)

        elif self.type == NodeType.POWER:
            self.__collect_factors_of_power(i, multitude, nodes, nodesToTerms, termsToNodes)

        elif self.type != NodeType.CONSTANT:
            self.__check_store_factor(i, multitude, nodes, nodesToTerms, termsToNodes)

    # Store the factors of this power node in the given lists.
    def __collect_factors_of_power(self, i, multitude, nodes, nodesToTerms, termsToNodes):
        assert(self.type == NodeType.POWER)

        base = self.children[0]
        exp = self.children[1]

        # We only extract powers with constant exponents.
        if exp.type == NodeType.CONSTANT:
            base.__collect_factors(i, exp.constant * multitude % self.__modulus, nodes, nodesToTerms, termsToNodes)
            return

        # Try to split a constant exponent from the sum.
        if exp.type == NodeType.SUM:
            first = exp.children[0]
            if first.type == NodeType.CONSTANT:
                base.__collect_factors(i, first.constant * multitude % self.__modulus, nodes, nodesToTerms, termsToNodes)

                node = self.get_copy()
                del node.children[1].children[0]
                if len(node.children[1].children) == 1: node.children[1] = node.children[1].children[0]
                node.__check_store_factor(i, multitude, nodes, nodesToTerms, termsToNodes)
                return

        self.__check_store_factor(i, multitude, nodes, nodesToTerms, termsToNodes)

    # Store the factors of this node in the given lists.
    def __check_store_factor(self, i, multitude, nodes, nodesToTerms, termsToNodes):
        idx = self.__get_index_in_list(nodes)

        if idx == None:
            nodes.append(self.__get_shallow_copy())
            nodesToTerms.append([len(nodes) - 1, set([IndexWithMultitude(i, multitude)])])
            termsToNodes[i].add(IndexWithMultitude(len(nodes) - 1, multitude))
            return

        ntt = nodesToTerms[idx][1]
        # To be safe, check whether there is already a connection between node
        # and factor.
        res = [p for p in ntt if p.idx == i]
        assert(len(res) <= 1)
        if len(res) == 1: res[0].multitude += multitude
        else: ntt.add(IndexWithMultitude(i, multitude))

        ttn = termsToNodes[i]
        res2 = [p for p in ttn if p.idx == idx]
        assert(len(res2) <= 1)
        assert((len(res2) == 1) == (len(res) == 1))
        if len(res2) == 1: res2[0].multitude += multitude
        else: ttn.add(IndexWithMultitude(idx, multitude))

    # For the given list of nodes, returns a list of flags indicating whether
    # the corresponding nodes are considered trivial.
    def __determine_nodes_triviality(self, nodes):
        return [n.__is_trivial_in_factorization() for n in nodes]

    # For the given list of nodes, returns a permutation of their indices
    # corresponding to their sorted order.
    def __determine_nodes_order(self, nodes):
        enumNodes = list(enumerate(nodes))
        enumNodes.sort(key = lambda p: p[1])
        return [p[0] for p in enumNodes]

    # Returns true iff this node is considered trivial in factorization.
    def __is_trivial_in_factorization(self):
        return not self.__is_bitwise_binop()

    # Create a node from the given batch.
    def __node_from_batch(self, batch, nodes, termsToNodes):
        node = self.__new_node(NodeType.SUM)

        for c in batch.children: node.children.append(self.__node_from_batch(c, nodes, termsToNodes))

        for a in batch.atoms:
            self.__reduce_node_set(termsToNodes[a], batch.factorIndices, batch.prevFactorIndices)
            nodeIndices = termsToNodes[a]
            term = self.children[a]
            constant = term.__get_const_factor_respecting_powers()

            if len(nodeIndices) == 0:
                node.__add_constant(constant)
                continue

            if len(nodeIndices) == 1 and constant == 1:
                p = nodeIndices.pop()
                node.children.append(self.__create_node_for_factor(nodes, p))
                continue

            prod = self.__new_node(NodeType.PRODUCT)
            if constant != 1: prod.children.append(self.__new_constant_node(constant))
            for p in nodeIndices: prod.children.append(self.__create_node_for_factor(nodes, p))
            prod.__check_resolve_product_of_powers()
            node.children.append(prod)

        if len(node.children) == 1: node.copy(node.children[0])

        if len(batch.factorIndices) == 0: return node

        prod = self.__new_node(NodeType.PRODUCT)
        for p in batch.factorIndices: prod.children.append(self.__create_node_for_factor(nodes, p))
        # If the sum is just a constant, make sure that the constant is the
        # product's first factor.
        if len(node.children) == 1 and node.children[0].type == NodeType.CONSTANT:
            prod.children.append(node)
        else: prod.children.insert(0, node)
        prod.__check_resolve_product_of_powers()
        return prod

    # Reduces the given set of node indices, together with their multitudes, by
    # that contained in any of both other given lists.
    def __reduce_node_set(self, indicesWithMultitudes, l1, l2):
        for p in l1 + l2:
            m = [q for q in indicesWithMultitudes if q.idx == p.idx]
            assert(len(m) == 1)
            assert(m[0].multitude >= p.multitude)
            m[0].multitude -= p.multitude
            if m[0].multitude == 0: indicesWithMultitudes.remove(m[0])

    # Returns the node's constant factor if it has one, or None otherwise.
    def __get_const_factor_respecting_powers(self):
        if self.type == NodeType.CONSTANT: return self.constant

        if self.type == NodeType.PRODUCT:
            f = 1
            for child in self.children:
                f = self.__get_reduced_constant(f * child.__get_const_factor_respecting_powers())
            return f

        if self.type != NodeType.POWER: return 1

        base = self.children[0]
        if base.type != NodeType.PRODUCT: return 1
        if base.children[0].type != NodeType.CONSTANT: return 1

        const = base.children[0].constant
        exp = self.children[1]
        if exp.type == NodeType.CONSTANT: return self.__power(const, exp.constant)

        if exp.type != NodeType.SUM: return 1
        if exp.children[0].type != NodeType.CONSTANT: return 1

        return self.__power(const, exp.children[0].constant)

    # Returns a node which coincides width the given list's element with given
    # index and multitude.
    def __create_node_for_factor(self, nodes, indexWithMultitude):
        exp = indexWithMultitude.multitude
        assert(exp > 0)
        idx = indexWithMultitude.idx

        if exp == 1: return nodes[idx].get_copy()
        return self.__new_node_with_children(NodeType.POWER, [nodes[idx].get_copy(), self.__new_constant_node(exp)])


    # If this node is a conjunction, replace its children which appear as
    # children of other children by -1 there since the bits have to be set
    # anyway.
    # TODO: If an operand is an inclusive disjunction, the disjunction's
    # operands can also be replaced in the other children's children.
    def __insert_fixed_in_conj(self):
        if self.type != NodeType.CONJUNCTION: return False

        changed = False

        for i in range(len(self.children)):
            child1 = self.children[i]

            for j in range(len(self.children)):
                if i == j: continue
                if self.children[j].__check_insert_fixed_true(child1): changed = True

        return changed

    # If the given node appears as a child or child's child, replace it by -1.
    def __check_insert_fixed_true(self, node):
        if not self.__is_bitwise_op(): return False

        changed = False

        for child in self.children:
            if child.equals(node):
                child.copy(self.__new_constant_node(-1))
                changed = True
            elif child.__is_bitwise_op():
                if child.__check_insert_fixed_true(node): changed = True

        return changed


    # If this node is a disjunction, replace its children which appear as
    # children of other children by 0 there since if the bits are set, the
    # disjunction's bits are 1 anyway.
    def __insert_fixed_in_disj(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        for i in range(len(self.children)):
            child1 = self.children[i]

            for j in range(len(self.children)):
                if i == j: continue
                if self.children[j].__check_insert_fixed_false(child1): changed = True

        return changed

    # If the given node appears as a child or child's child, replace it by 0.
    def __check_insert_fixed_false(self, node):
        if not self.__is_bitwise_op(): return False

        changed = False

        for child in self.children:
            if child.equals(node):
                child.copy(self.__new_constant_node(0))
                changed = True
            elif child.__is_bitwise_op():
                if child.__check_insert_fixed_false(node): changed = True

        return changed


    # If this node is an exclusive disjunction with 2 operands, one of them
    # being -1 or 0, this operation can be resolved:
    #     -1^x -> ~x
    #     0^x  ->  x
    def __check_trivial_xor(self):
        if self.type != NodeType.EXCL_DISJUNCTION: return False

        c = self.children[0]
        if len(self.children) == 2:
            if c.__is_constant(-1):
                self.type = NodeType.NEGATION
                del self.children[0]
                return True

            if c.__is_constant(0):
                self.copy(self.children[1])
                return True

        else:
            assert(len(self.children) > 2)

            # TODO: Handle case for constant -1: Negate one of the other
            # operands.

            if c.__is_constant(0):
                del self.children[0]
                return True

        return False


    # If a child of this node is a conjunction or inclusive disjunction of two
    # children such that one equals the other one after multiplication by -1,
    # and if this node is a product with a constant divisible by 2, try to
    # apply the rules "2*(x|-x) == x^-x" and "-2*(x&-x) == x^-x".
    def __check_xor_same_mult_by_minus_one(self):
        # We need a product for the factor 2 (or multiple).
        if not self.type == NodeType.PRODUCT: return False

        first = self.children[0]
        # We do not have a factor to divide by 2.
        if not first.type == NodeType.CONSTANT: return False

        # We have a constant factor, but still not divisible by 2.
        if first.constant % 2 != 0: return False

        changed = False
        # Iterate over all children but the first one (which is a constant) and
        # search for factors of the form "(x|-x)" of "(x&-x)".
        for i in range(len(self.children) - 1, 0, -1):
            child = self.children[i]
            if child.type not in [NodeType.CONJUNCTION, NodeType.INCL_DISJUNCTION]: continue

            # We need to have exactly two operands.
            if len(child.children) != 2: continue

            node = child.children[0].get_copy()
            node.__multiply_by_minus_one()

            # The second operand is not the multiplicative inverse of the first
            # one.
            if not node.equals(child.children[1]): continue

            first.constant //= 2
            if child.type == NodeType.CONJUNCTION:
                first.__set_and_reduce_constant(-first.constant)

            child.type = NodeType.EXCL_DISJUNCTION
            changed = True
            if first.constant % 2 != 0: break

        return changed


    # If this node is a conjunction and contains a pattern x&-x&2*x, this whole
    # node is set to zero.
    def __check_conj_zero_rule(self):
        if self.type != NodeType.CONJUNCTION: return False
        if not self.__has_conj_zero_rule(): return False

        self.copy(self.__new_constant_node(0))
        return True

    # Returns True iff this node is a conjunction and contains a pattern
    # x&-x&2*x.
    def __has_conj_zero_rule(self):
        assert(self.type == NodeType.CONJUNCTION)

        for i in range(len(self.children) - 1):
            child1 = self.children[i]

            for j in range(i + 1, len(self.children)):
                child2 = self.children[j]
                neg2 = child2.get_copy()
                neg2.__multiply_by_minus_one()

                if not child1.equals(neg2): continue

                double1 = child1.get_copy()
                double1.__multiply(2)
                double2 = child2.get_copy()
                double2.__multiply(2)

                for k in range(len(self.children)):
                    if k in [i, j]: continue

                    child3 = self.children[k]
                    # We have a combination that resolves to zero.
                    if child3.equals(double1) or child3.equals(double2): return True

        return False


    # If this node is a conjunction and contains a pattern ~(2*x)&-(x^-x), this
    # whole node is set to zero.
    def __check_conj_neg_xor_zero_rule(self):
        if self.type != NodeType.CONJUNCTION: return False
        if not self.__has_conj_neg_xor_zero_rule(): return False

        self.copy(self.__new_constant_node(0))
        return True

    # Returns True iff this node is a conjunction and contains a pattern
    # ~(2*x)&-(x^-x).
    def __has_conj_neg_xor_zero_rule(self):
        assert(self.type == NodeType.CONJUNCTION)

        for i in range(len(self.children)):
            child1 = self.children[i]

            # Check for pattern -(x^-x).
            node = child1.__get_opt_arg_neg_xor_same_neg()
            if node == None: continue

            # Second possibility.
            node2 = node.get_copy()
            node2.__multiply_by_minus_one()

            for j in range(len(self.children)):
                if i == j: continue

                neg2 = self.children[j].get_copy()
                neg2.__negate()

                if neg2.__is_double(node) or neg2.__is_double(node2): return True

        return False

    # If this node has the pattern -(x^-x), returns x. Returns None otherwise.
    def __get_opt_arg_neg_xor_same_neg(self):
        # Check for factor -1.
        if self.type != NodeType.PRODUCT: return None
        if len(self.children) != 2: return None
        if not self.children[0].__is_constant(-1): return None

        xor = self.children[1]
        if xor.type != NodeType.EXCL_DISJUNCTION: return None
        if len(xor.children) != 2: return None

        node0 = xor.children[0].get_copy()
        node0.__multiply_by_minus_one()
        if node0.equals(xor.children[1]): return node0

        return None


    # If this node is a conjunction and contains a pattern 2*x|~-(x^-x), this
    # whole node is set to -1.
    def __check_conj_neg_xor_minus_one_rule(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False
        if not self.__has_disj_neg_xor_minus_one_rule(): return False

        self.copy(self.__new_constant_node(-1))
        return True

    # Returns True iff this node is a disjunction and contains a pattern
    # 2*x|~-(x^-x).
    def __has_disj_neg_xor_minus_one_rule(self):
        assert(self.type == NodeType.INCL_DISJUNCTION)

        for i in range(len(self.children)):
            child1 = self.children[i]

            # Check for pattern ~-(x^-x).
            if child1.type != NodeType.NEGATION: continue

            node = child1.children[0].__get_opt_arg_neg_xor_same_neg()
            if node == None: continue

            # Second possibility.
            node2 = node.get_copy()
            node2.__multiply_by_minus_one()

            for j in range(len(self.children)):
                if i == j: continue

                child2 = self.children[j]
                if child2.__is_double(node) or child2.__is_double(node2): return True

        return False


    # If this node is a conjunction and contains a pattern 2*x&~(x^-x), this
    # whole node is set to zero.
    def __check_conj_negated_xor_zero_rule(self):
        if self.type != NodeType.CONJUNCTION: return False
        if not self.__has_conj_negated_xor_zero_rule(): return False

        self.copy(self.__new_constant_node(0))
        return True

    # Returns True iff this node is a conjunction and contains a pattern
    # 2*x&~(x^-x).
    def __has_conj_negated_xor_zero_rule(self):
        assert(self.type == NodeType.CONJUNCTION)

        for i in range(len(self.children)):
            child1 = self.children[i]

            # Check for pattern ~(x^-x).
            node = child1.__get_opt_arg_negated_xor_same_neg()
            if node == None: continue

            # Second possibility.
            node2 = node.get_copy()
            node2.__multiply_by_minus_one()

            for j in range(len(self.children)):
                if i == j: continue

                child2 = self.children[j].get_copy()
                if child2.__is_double(node) or child2.__is_double(node2): return True

        return False

    # If this node has the pattern ~(x^-x), returns x. Returns None otherwise.
    def __get_opt_arg_negated_xor_same_neg(self):
        if self.type != NodeType.NEGATION: return None

        xor = self.children[0]
        if xor.type != NodeType.EXCL_DISJUNCTION: return None
        if len(xor.children) != 2: return None

        node0 = xor.children[0].get_copy()
        node0.__multiply_by_minus_one()
        if node0.equals(xor.children[1]): return node0

        return None


    # If this node is a conjunction, check for the pattern 2*x&(x^-x). Whenever
    # found, remove (x^-x) since it has no effect.
    def __check_conj_xor_identity_rule(self):
        if self.type != NodeType.CONJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            if not child1.__is_xor_same_neg(): continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]

                if child2.__is_double(child1.children[0]) or child2.__is_double(child1.children[1]):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will incremented at next iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # Returns True iff this node is an exclusive disjunction of the pattern
    # x^-x.
    def __is_xor_same_neg(self):
        if self.type != NodeType.EXCL_DISJUNCTION: return False
        if len(self.children) != 2: return False

        neg = self.children[1].get_copy()
        neg.__multiply_by_minus_one()

        return neg.equals(self.children[0])

    # Returns True iff this node is double the given node.
    def __is_double(self, node):
        cpy = node.get_copy()
        cpy.__multiply(2)
        return self.equals(cpy)


    # If this node is a conjunction, check for the pattern 2*x|-(x^-x). Whenever
    # found, remove -(x^-x) since it has no effect.
    def __check_disj_xor_identity_rule(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_xor_disj_xor_identity()
            # No pattern -(x^-x).
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]

                if child2.__is_double(node.children[0]) or child2.__is_double(node.children[1]):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will incremented at next iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern -(x^-x), returns x^-x. Returns None
    # otherwise.
    def __get_opt_xor_disj_xor_identity(self):
        # Check for the factor -1.
        if self.type != NodeType.PRODUCT: return None
        if len(self.children) != 2: return None
        if not self.children[0].__is_constant(-1): return None

        child = self.children[1]

        if child.type != NodeType.EXCL_DISJUNCTION: return None
        if len(child.children) != 2: return None

        neg = child.children[1].get_copy()
        neg.__multiply_by_minus_one()

        return child if neg.equals(child.children[0]) else None


    # If this node is a conjunction, check for the pattern -x&~(x&2*x) or
    # -x&~(x&-2*x).
    # Whenever found, remove ~(x&2*x) or ~(x&-2*x), resp., since it has no
    # effect. Similar for -x&(~x|~(2*x)) or -x&(~x|~(-2*x)).
    def __check_conj_neg_conj_identity_rule(self):
        if self.type != NodeType.CONJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_neg_conj_double()
            # No pattern ~(x&2*x) or ~x|~(2*x).
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]
                neg = child2.get_copy()
                neg.__multiply_by_minus_one()

                if neg.equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will be incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern ~(x&2*x) or ~x|~(2*x), returns x. Returns
    # None otherwise.
    def __get_opt_arg_neg_conj_double(self):
        node = self.__get_opt_arg_neg_conj_double_1()
        return node if node != None else self.__get_opt_arg_neg_conj_double_2()

    # If this node has the pattern ~(x&2*x) or ~(x&-2*x), returns x. Returns
    # None otherwise.
    def __get_opt_arg_neg_conj_double_1(self):
        if self.type != NodeType.NEGATION: return None

        child = self.children[0]
        if child.type != NodeType.CONJUNCTION: return None
        if len(child.children) != 2: return None

        if child.children[0].__is_double(child.children[1]): return child.children[1]
        if child.children[1].__is_double(child.children[0]): return child.children[0]

        node = child.children[0].get_copy()
        node.__multiply_by_minus_one()
        if node.__is_double(child.children[1]): return child.children[1]

        node = child.children[1].get_copy()
        node.__multiply_by_minus_one()
        if node.__is_double(child.children[0]): return child.children[0]

        return None

    # If this node has the pattern ~x|~(2*x) or ~x|~(-2*x), returns x. Returns
    # None otherwise.
    def __get_opt_arg_neg_conj_double_2(self):
        if self.type != NodeType.INCL_DISJUNCTION: return None
        if len(self.children) != 2: return None

        node0 = self.children[0].get_copy()
        node0.__negate()
        node1 = self.children[1].get_copy()
        node1.__negate()

        if node0.__is_double(node1): return node1
        if node1.__is_double(node0): return node0

        node = node0.get_copy()
        node.__multiply_by_minus_one()
        if node.__is_double(node1): return node1

        node1.__multiply_by_minus_one()
        if node1.__is_double(node0): return node0

        return None


    # If this node is a disjunction, check for the pattern x|-(x|-x).
    # Whenever found, remove -(x|-x) since it has no effect.
    def __check_disj_disj_identity_rule(self):
        return self.__check_nested_bitwise_identity_rule(NodeType.INCL_DISJUNCTION)

    # If this node is a disjunction, check for the pattern x&-(x&-x).
    # Whenever found, remove -(x&-x) since it has no effect.
    def __check_conj_conj_identity_rule(self):
        return self.__check_nested_bitwise_identity_rule(NodeType.CONJUNCTION)

    # If this node is a disjunction, check for the pattern x|-((x&y)|-x) if (t
    # is INCL_DISJUNCTION) or x&-((x|y)&-x) (if it is CONJUNCTION), where y can
    # vanish. Whenever found, remove -((x&y)|-x) or -((x|y)&-x), resp., since
    # it has no effect.
    def __check_nested_bitwise_identity_rule(self, t):
        if self.type != t: return False

        changed = False

        # TODO: Consider disjunctions of children as nodes too.

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            nodes = child1.__get_candidates_nested_bitwise_identity(t)
            assert(len(nodes) <= 2)

            # No pattern -((x&y)|-x) or -((x|y)&-x), resp.
            if len(nodes) == 0: continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]

                done = False
                for node in nodes:
                    if child2.equals(node):
                        del self.children[i]
                        changed = True
                        done = True

                        # Decrement i since it will br incremented at next
                        # iteration.
                        i -= 1
                        break

                if done: break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern -((x&y)|-x) if (t is INCL_DISJUNCTION) or
    # -((x|y)&-x) (if it is CONJUNCTION), returns [x, -x] (if y is not present)
    # or [x] (otherwise). Returns [] otherwise.
    def __get_candidates_nested_bitwise_identity(self, t):
        # Check for factor -1.
        if self.type != NodeType.PRODUCT: return []
        if len(self.children) != 2: return []
        if not self.children[0].__is_constant(-1): return []

        # Check for bitwise with type t.
        bitw = self.children[1]
        if bitw.type != t: return []
        if len(bitw.children) != 2: return []

        # Check whether the operands are multiplicative inverse.
        neg = bitw.children[1].get_copy()
        neg.__multiply_by_minus_one()

        if neg.equals(bitw.children[0]): return [bitw.children[0], bitw.children[1]]

        ot = NodeType.CONJUNCTION if t == NodeType.INCL_DISJUNCTION else NodeType.INCL_DISJUNCTION

        if bitw.children[0].type == ot:
            if bitw.children[0].__has_child(neg): return [neg]

        if bitw.children[1].type == ot:
            neg = bitw.children[0].get_copy()
            neg.__multiply_by_minus_one()

            if bitw.children[1].__has_child(neg): return [neg]

        return bitw if neg.equals(bitw.children[0]) else []


    # If this node is a disjunction, check for the pattern -x|(~x&2*x) or
    # -x|(~x&-2*x).
    # Whenever found, remove ~x&2*x or ~x&-2*x, resp., since it has no effect.
    # Similar for -x|~(x|~(2*x)) or -x|~(x|~(-2*x)).
    def __check_disj_conj_identity_rule(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_disj_conj_identity()
            # No pattern ~x&2*x or ~x&-2*x.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]
                neg = child2.get_copy()
                neg.__multiply_by_minus_one()

                if neg.equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern ~x&2*x or -x|~(x|~(2*x)), returns x. Returns
    # None otherwise.
    def __get_opt_arg_disj_conj_identity(self):
        node = self.__get_opt_arg_disj_conj_identity_1()
        return node if node != None else self.__get_opt_arg_disj_conj_identity_2()

    # If this node has the pattern ~x&2*x or ~x&-2*x, returns x. Returns None
    # otherwise.
    def __get_opt_arg_disj_conj_identity_1(self):
        if self.type != NodeType.CONJUNCTION: return None
        if len(self.children) != 2: return None

        for idx in [0, 1]:
            oIdx = 0 if idx == 1 else 1
            oDiv = self.children[oIdx].__divided(2)
            if oDiv == None: continue

            oDivNeg = oDiv.get_copy()
            oDivNeg.__multiply_by_minus_one()

            # Try all cases with explicit bitwise negations.

            node = self.children[idx]
            if node.type == NodeType.NEGATION:
                neg = node.children[0]
                if neg.equals(oDiv) or neg.equals(oDivNeg): return neg

            if oDiv.type == NodeType.NEGATION:
                neg = oDiv.children[0]
                if neg.equals(node): return oDiv

            if oDivNeg.type == NodeType.NEGATION:
                neg = oDivNeg.children[0]
                if neg.equals(node): return oDivNeg

            # Try the same with arithmetically written negations.

            neg = node.__get_opt_transformed_negated()
            if neg != None:
                if neg.equals(oDiv) or neg.equals(oDivNeg): return neg

            neg = oDiv.__get_opt_transformed_negated()
            if neg != None:
                if neg.equals(node): return oDiv

            neg = oDivNeg.__get_opt_transformed_negated()
            if neg != None:
                if neg.equals(node): return oDivNeg

        return None

    # If this node has the pattern ~(x|~(2*x)) or ~(x|~(-2*x)), returns x.
    # Returns None otherwise.
    def __get_opt_arg_disj_conj_identity_2(self):
        if self.type != NodeType.NEGATION: return None

        child = self.children[0]
        if child.type != NodeType.INCL_DISJUNCTION: return None
        if len(child.children) != 2: return None

        for negIdx in [0, 1]:
            ch = child.children[negIdx]

            # Check whether this operand is negated.
            node = None
            if ch.type == NodeType.NEGATION: node = ch.children[0]
            else: node = ch.__get_opt_transformed_negated()

            if node == None: continue

            # Now check whether the other operand is half this (optionally
            # negative) operand.

            oIdx = 0 if negIdx == 1 else 1
            other = child.children[oIdx]

            if node.__is_double(other): return other

            neg = node.get_copy()
            neg.__multiply_by_minus_one()
            if neg.__is_double(other): return other

        return None

    # Returns a node equal to the given one after division by the given
    # divisor. Returns None if division is not possible without remainder.
    def __divided(self, divisor):
        if self.type == NodeType.CONSTANT:
            if self.constant % divisor == 0: return self.__new_constant_node(self.constant // divisor)

        if self.type == NodeType.PRODUCT:
            for i in range(len(self.children)):
                node = self.children[i].__divided(divisor)
                if node == None: continue

                res = self.get_copy()
                res.children[i] = node

                if res.children[i].__is_constant(1):
                    del res.children[i]
                    if len(res.children) == 1: return res.children[0]

                return res

            return None

        if self.type == NodeType.SUM:
            res = self.__new_node(NodeType.SUM)

            for child in self.children:
                node = child.__divided(divisor)
                if node == None: return None

                res.children.append(node)

            return res

        # TODO: Handle powers.
        return None


    # If this node is a disjunction, check for the pattern x|(-~x&2*~x) or
    # x|(-~x&-2*~x).
    # Whenever found, remove -~x&2*~x or -~x&-2*~x, resp., since it has no
    # effect.
    def __check_disj_conj_identity_rule_2(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_disj_conj_identity_rule_2()
            # No pattern -~x&2*~x or -~x&-2*~x.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                if self.children[j].equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern -~x&2*~x or -~x&-2*~x, returns x. Returns
    # None otherwise.
    def __get_opt_arg_disj_conj_identity_rule_2(self):
        if self.type != NodeType.CONJUNCTION: return None
        if len(self.children) != 2: return None

        # Check for -~x&-2*~x.
        for idx in [0, 1]:
            oIdx = 0 if idx == 1 else 1
            if self.children[oIdx].__is_double(self.children[idx]):
                node = self.children[idx].get_copy()
                node.__multiply_by_minus_one()
                node.__negate()
                return node

        for idx in [0, 1]:
            oIdx = 0 if idx == 1 else 1

            node = self.children[idx].get_copy()
            node.__multiply_by_minus_one()

            if self.children[oIdx].__is_double(node):
                node.__negate()
                return node

        return None


    # If this node is a disjunction, check for the pattern x|-(-x|2*x) or
    # x|-(-x|-2*x).
    # Whenever found, remove -(-x|2*x) or -(-x|-2*x), resp., since it has no
    # effect.
    def __check_disj_neg_disj_identity_rule(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_disj_neg_disj_identity_rule()
            # No pattern -~x&2*~x or -~x&-2*~x.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                if self.children[j].equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern -(-x|2*x) or -(-x|-2*x), returns x. Returns
    # None otherwise.
    def __get_opt_arg_disj_neg_disj_identity_rule(self):
        if self.type != NodeType.PRODUCT: return None
        if len(self.children) != 2: return None
        if not self.children[0].__is_constant(-1): return None

        disj = self.children[1]
        if disj.type != NodeType.INCL_DISJUNCTION: return None
        if len(disj.children) != 2: return None

        # Check for -x|-2*x.
        for idx in [0, 1]:
            oIdx = 0 if idx == 1 else 1
            if disj.children[oIdx].__is_double(disj.children[idx]):
                node = disj.children[idx].get_copy()
                node.__multiply_by_minus_one()
                return node

        # Check for -x|2*x.
        for idx in [0, 1]:
            oIdx = 0 if idx == 1 else 1

            node = disj.children[idx].get_copy()
            node.__multiply_by_minus_one()

            if disj.children[oIdx].__is_double(node): return node

        return None


    # If this node is a conjunction, check for the pattern x&(-~(2*x)|-~x),
    # x&(~(2*x)|-~x) or x&(~(-2*~x)|-~x). Whenever found, remove -~(2*x)|-~x,
    # ~(2*~x)|-~x or ~(-2*~x)|-~x, resp., since it has no effect.
    def __check_conj_disj_identity_rule(self):
        if self.type != NodeType.CONJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_conj_disj_identity()
            # No pattern -~(2*x)|-~x.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]
                if child2.equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern -~(2*x)|-~x, ~(2*~x)|-~x or ~(-2*~x)|-~x,
    # returns x. Returns None otherwise.
    def __get_opt_arg_conj_disj_identity(self):
        if self.type != NodeType.INCL_DISJUNCTION: return None

        node = self.__get_opt_arg_conj_disj_identity_1()
        return node if node != None else self.__get_opt_arg_conj_disj_identity_2()

    # If this node has the pattern -~(2*x)|-~x, returns x. Returns None
    # otherwise.
    def __get_opt_arg_conj_disj_identity_1(self):
        assert (self.type == NodeType.INCL_DISJUNCTION)

        # TODO: Allow more children. Straightforward, but less efficient.
        if len(self.children) != 2: return None

        child0 = self.children[0].get_copy()
        child1 = self.children[1].get_copy()

        child0.__multiply_by_minus_one()
        child1.__multiply_by_minus_one()

        child0.__negate()
        child1.__negate()

        if child0.__is_double(child1): return child1
        if child1.__is_double(child0): return child0

        return None

    # If this node has the pattern ~(2*~x)|-~x or ~(-2*~x)|-~x, returns x.
    # Returns None otherwise.
    def __get_opt_arg_conj_disj_identity_2(self):
        assert (self.type == NodeType.INCL_DISJUNCTION)

        # TODO: Allow more children. Straightforward, but less efficient.
        if len(self.children) != 2: return None

        for idx in [0, 1]:
            neg = self.children[idx].get_copy()
            neg.__negate()

            oIdx = 0 if idx == 1 else 1
            other = self.children[oIdx]

            ok = neg.__is_double(other)
            if not ok:
                neg.__multiply_by_minus_one()
                ok = neg.__is_double(other)

            if not ok: continue
                
            node = other.get_copy()
            node.__multiply_by_minus_one()
            node.__negate()
            return node

        return None


    # If this node is a disjunction, check for the pattern x|(x|y)-y.
    # Whenever found, remove (x|y)-y since it has no effect.
    def __check_disj_sub_disj_identity_rule(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_disj_sub_disj_identity()
            # No pattern (x|y)-y.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                if self.children[j].equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern (x|y)-y, returns x. Returns None otherwise.
    def __get_opt_arg_disj_sub_disj_identity(self):
        if self.type != NodeType.SUM: return None
        if len(self.children) != 2: return None

        for idx in [0, 1]:
            child = self.children[idx]
            if child.type != NodeType.INCL_DISJUNCTION: continue
            # TODO: Allow multiple children and in this case consider all but
            # one to form y.
            if len(child.children) != 2: continue

            oidx = 0 if idx == 1 else 1
            neg = self.children[oidx].get_copy()
            neg.__multiply_by_minus_one()

            if neg.equals(child.children[0]): return child.children[1]
            if neg.equals(child.children[1]): return child.children[0]

        return None


    # If this node is a disjunction, check for the pattern x|x-(x&y).
    # Whenever found, remove x-(x&y) since it has no effect.
    def __check_disj_sub_conj_identity_rule(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_disj_sub_conj_identity()
            # No pattern (x|y)-y.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                if self.children[j].equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern x-(x&y), returns x. Returns None otherwise.
    def __get_opt_arg_disj_sub_conj_identity(self):
        if self.type != NodeType.SUM: return None
        # TODO: Allow x to be a sum.
        if len(self.children) != 2: return None

        for idx in [0, 1]:
            child = self.children[idx]
            if child.type != NodeType.PRODUCT: continue
            if len(child.children) != 2: continue
            if not child.children[0].__is_constant(-1): continue

            conj = child.children[1]
            if conj.type != NodeType.CONJUNCTION: continue

            # TODO: Allow multiple children in the conjunction form x.

            oidx = 0 if idx == 1 else 1
            other = self.children[oidx]

            for c in conj.children:
                if c.equals(other): return other

        return None


    # If this node is a conjunction, check for the pattern x&x+(~x&y).
    # Whenever found, remove x+(~x&y) since it has no effect.
    def __check_conj_add_conj_identity_rule(self):
        if self.type != NodeType.CONJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node = child1.__get_opt_arg_conj_add_conj_identity()
            # No pattern x+(~x&y).
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                if self.children[j].equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern x+(~x&y), returns x. Returns None otherwise.
    def __get_opt_arg_conj_add_conj_identity(self):
        if self.type != NodeType.SUM: return None
        # TODO: Allow x to be a sum.
        if len(self.children) != 2: return None

        for idx in [0, 1]:
            child = self.children[idx]
            if child.type != NodeType.CONJUNCTION: continue

            oidx = 0 if idx == 1 else 1
            oneg = self.children[oidx].get_copy()
            oneg.__negate()

            for c in child.children:
                if c.equals(oneg): return self.children[oidx]

        return None


    # If this node is a conjunction, check for the pattern x&-(-y&(x|y)).
    # Whenever found, resolve it to x&y.
    def __check_conj_conj_disj_rule(self):
        return self.__check_nested_bitwise_rule(NodeType.CONJUNCTION)

    # If this node is a conjunction, check for the pattern x|-(-y|(x&y)).
    # Whenever found, resolve it to x|y.
    def __check_disj_disj_conj_rule(self):
        return self.__check_nested_bitwise_rule(NodeType.INCL_DISJUNCTION)

    # If this node is a conjunction, check for the pattern x&-(-y&(x|y)).
    # If it is a disjunction, check for the pattern x|-(-y|(x&y)).
    # Whenever found, remove x+(~x&y) since it has no effect.
    def __check_nested_bitwise_rule(self, t):
        if self.type != t: return False
        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node1, node2 = child1.__get_opt_arg_nested_bitwise(t)
            assert((node1 == None) == (node2 == None))
            # Pattern not found.
            if node1 == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                if self.children[j].equals(node1):
                    self.children[i].copy(node2)
                    changed = True
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern x&-(-y&(x|y)) or x|-(-y|(x&y)), returns x,
    # y. Returns None, None otherwise.
    def __get_opt_arg_nested_bitwise(self, t):
        if self.type != NodeType.PRODUCT: return None, None
        if len(self.children) != 2: return None, None
        if not self.children[0].__is_constant(-1): return None, None

        child = self.children[1]
        if child.type != t: return None, None
        if len(child.children) != 2: return None, None

        for idx in [0, 1]:
            oidx = 0 if idx == 1 else 1

            c = child.children[idx]
            ot = NodeType.CONJUNCTION if t == NodeType.INCL_DISJUNCTION else NodeType.INCL_DISJUNCTION
            if c.type != ot: continue
            if len(c.children) != 2: return None, None

            oneg = child.children[oidx].get_copy()
            oneg.__multiply_by_minus_one()

            if c.children[0].equals(oneg): return c.children[1], c.children[0]
            if c.children[1].equals(oneg): return c.children[0], c.children[1]

        return None, None


    # If this node is a conjunction, check for the pattern -(-x|x&y&z)|x&y,
    # where y as well as z may be -1. Whenever found, resolve it to x.
    def __check_disj_disj_conj_rule_2(self):
        if self.type != NodeType.INCL_DISJUNCTION: return False

        changed = False

        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            child1 = self.children[i]
            node, conj = child1.__get_opt_pair_disj_disj_conj_2()
            assert((node == None) == (conj == None))
            # Pattern not found.
            if node == None: continue

            for j in range(len(self.children)):
                if j == i: continue

                child2 = self.children[j]

                # y is (virtually) -1.
                if child2.equals(node):
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

                if child2.type != NodeType.CONJUNCTION: continue
                if not child2.__has_child(node): continue

                if child2.__are_all_children_contained(conj):
                    self.children[j] = node.get_copy()
                    del self.children[i]
                    changed = True

                    # Decrement i since it will br incremented at next
                    # iteration.
                    i -= 1
                    break

        if len(self.children) == 1: self.copy(self.children[0])
        return changed

    # If this node has the pattern -(-x|x&y&z), returns x, x&y&z. Returns None,
    # None otherwise.
    def __get_opt_pair_disj_disj_conj_2(self):
        # Check for factor -1.
        if self.type != NodeType.PRODUCT: return None, None
        if len(self.children) != 2: return None, None
        if not self.children[0].__is_constant(-1): return None, None

        disj = self.children[1]
        if disj.type != NodeType.INCL_DISJUNCTION: return None, None
        # TODO: Be more flexible by allowing more children and considering all
        # but one as a node.
        if len(disj.children) != 2: return None, None

        for idx in [0, 1]:
            oIdx = 0 if idx == 1 else 1

            conj = disj.children[idx]
            if conj.type != NodeType.CONJUNCTION: continue

            neg = disj.children[oIdx].get_copy()
            neg.__multiply_by_minus_one()

            if conj.__has_child(neg): return neg, conj

        return None, None


    # Perform some refinement that may be necessary after simplification via
    # substitution. This consists of steps that are usually not necessary using
    # the linear simplifier, but this might miss some simplification because it
    # does not have full insights into the original expression.
    def refine_after_substitution(self):
        changed = False
        for c in self.children:
            if c.refine_after_substitution(): changed = True

        if self.__check_bitwise_in_sums_cancel_terms():   changed = True
        if self.__check_bitwise_in_sums_replace_terms():  changed = True
        if self.__check_disj_involving_xor_in_sums():     changed = True
        if self.__check_xor_involving_disj():             changed = True
        if self.__check_negative_bitw_inverse():          changed = True
        if self.__check_xor_pairs_with_constants():       changed = True
        if self.__check_bitw_pairs_with_constants():      changed = True
        if self.__check_diff_bitw_pairs_with_constants(): changed = True
        if self.__check_bitw_tuples_with_constants():     changed = True
        if self.__check_bitw_pairs_with_inverses():       changed = True
        if self.__check_diff_bitw_pairs_with_inverses():  changed = True
        if self.__check_bitw_and_op_in_sum():             changed = True
        if self.__check_insert_xor_in_sum():              changed = True
        return changed

    # Try to transform subexpressions of this sum node if the sum's complexity
    # decreases doing so. Apply, e.g., the following rules:
    #
    #   "(x&y) - x - y"   -> "-(x|y)"
    #   "(x|y) - x - y"   -> "-(x&y)"
    #   "2*(x&y) - x - y" -> "-(x^y)"
    #   "2*(x|y) - x - y" -> "x^y"
    #
    # NOTE: Actually the linear simplifier resolves these identities correctly,
    # but we might still encounter this after substitution, where the
    # identitity might be obscured.
    def __check_bitwise_in_sums_cancel_terms(self):
        if self.type != NodeType.SUM: return False
        # Save runtime in too large sums.
        if len(self.children) > MAX_CHILDREN_TO_TRANSFORM_BITW: return False

        changed = True
        i = 0
        while True:
            if i >= len(self.children): return changed

            child = self.children[i]
            factor = 1

            if child.type == NodeType.PRODUCT:
                if len(child.children) != 2 or child.children[0].type != NodeType.CONSTANT:
                    i += 1
                    continue

                factor = child.children[0].constant
                child = child.children[1]

            if child.type not in [NodeType.CONJUNCTION, NodeType.INCL_DISJUNCTION] or len(child.children) != 2:
                i += 1
                continue

            newIdx = self.__check_transform_bitwise_in_sum_cancel(i, child, factor)
            if newIdx == None:
                i += 1
                continue

            assert(self.children[newIdx] == child)

            # If the sum has only one child left, replace it by this child.
            if len(self.children) == 1:
                self.copy(self.children[0])
                return True

            # Otherwise adapt the iteration index.
            i = newIdx + 1

        return changed

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # inclusive disjunction (if it is a conjunction) or a conjunction (resp.)
    # or an exclusive disjunction. If a transformation has happened, returns
    # the new index of the bitwise. Otherwise returns None.
    def __check_transform_bitwise_in_sum_cancel(self, idx, bitw, factor):
        # For a transformation to Xor, we need a factor divisible by 2.
        withToXor = factor % 2 == 0

        newIdx = self.__check_transform_bitwise_in_sum_cancel_impl(False, idx, bitw, factor)
        if newIdx != None: return newIdx

        if withToXor:
            newIdx = self.__check_transform_bitwise_in_sum_cancel_impl(True, idx, bitw, factor // 2)
            if newIdx != None: return newIdx

        return None

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would cancel out sum terms of the sum.
    #
    # If toXor is False, apply, e.g., the following rules:
    #   "(x&y) - x - y"   -> "-(x|y)"
    #   "(x|y) - x - y"   -> "-(x&y)"
    # If it is True, apply, e.g., the following rules:
    #   "2*(x&y) - x - y" -> "-(x^y)"
    #   "2*(x|y) - x - y" -> "x^y"
    def __check_transform_bitwise_in_sum_cancel_impl(self, toXor, idx, bitw, factor):
        assert(self.type == NodeType.SUM)
        assert(idx < len(self.children))

        opSum = self.__new_node(NodeType.SUM)
        for op in bitw.children: opSum.children.append(op.get_copy())
        opSum.__multiply(factor)
        opSum.expand()
        opSum.refine()

        # Save runtime. It is not likely that we can sum up more children to a
        # node equal to opSum.
        maxc = min(len(opSum.children), MAX_CHILDREN_SUMMED_UP)

        # Iterate over all subsets of children and check whether the children
        # sum up to the sum of the bitwise operation's operands.
        for i in range(1, 2**(len(self.children) - 1)):
            # Save runtime, see above.
            if popcount(i) > maxc: continue

            newIdx = self.__check_transform_bitwise_for_comb(toXor, idx, bitw, factor, opSum, i)
            if newIdx != None: return newIdx

        return None

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would cancel out the sum terms corresponding to the
    # given combination index.
    def __check_transform_bitwise_for_comb(self, toXor, idx, bitw, factor, opSum, combIdx):
        n = combIdx

        diff = opSum.get_copy()
        indices = []

        for j in range(len(self.children)):
            if j == idx: continue

            if (n & 1) == 1:
                indices.append(j)
                diff.__add(self.children[j])
            n = n >> 1

        diff.expand()
        diff.refine()

        # Check whether we would get a better opportunity when adding a
        # modulo-multiple of the bitwise. This is in order not to miss
        # something due to a vanishing factor 2.
        if diff.type != NodeType.CONSTANT:
            assert(self.__modulus % 2 == 0)

            opSum = self.__new_node(NodeType.SUM)
            for op in bitw.children: opSum.children.append(op.get_copy())

            hmod = self.__modulus // 2
            opSum.__multiply(-hmod)

            diff2 = diff.get_copy()
            diff2.__add(opSum)
            diff2.expand()
            diff2.refine()

            if diff2.type == NodeType.CONSTANT:
                diff = diff2
                factor += hmod

        return self.__check_transform_bitwise_for_diff(toXor, idx, bitw, factor, diff, indices)

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would cancel out sum terms. Here the difference
    # between the sum of candidate terms and the sum of the bitwise
    # expression's operands is given, together with a list of the terms'
    # indices.
    def __check_transform_bitwise_for_diff(self, toXor, idx, bitw, factor, diff, indices):
        newIdx = self.__check_transform_bitwise_for_diff_full(toXor, idx, bitw, factor, diff, indices)
        if newIdx != None: return newIdx

        # If there is only one term considered, merging will not decrease
        # the number of terms.
        if len(indices) > 1:
            # If the operand sum and the children's sum do not cancel out,
            # check whether their difference can be merged into any of the
            # children.
            newIdx = self.__check_transform_bitwise_for_diff_merge(toXor, idx, bitw, factor, diff, indices)
            if newIdx != None: return newIdx

        return None

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would cancel out sum terms. Transform the expression
    # if the given difference is a constant.
    def __check_transform_bitwise_for_diff_full(self, toXor, idx, bitw, factor, diff, indices):
        if diff.type != NodeType.CONSTANT: return None

        # We found a match. Transform the bitwise expression.

        if not toXor or bitw.type == NodeType.CONJUNCTION: factor = -factor
        bitw.type = bitw.__get_transformed_bitwise_type(toXor)
        if (factor - 1) % self.__modulus != 0: bitw.__multiply(factor)
        self.children[idx] = bitw

        # Finally remove the children which we have merged into the bitwise
        # expression.
        for j in range(len(indices) - 1, -1, -1):
            del self.children[indices[j]]
            if indices[j] < idx: idx -= 1

        # If the difference is not exactly zero, but constant, add this
        # constant.
        if not diff.__is_constant(0):
            if self.children[0].type != NodeType.CONSTANT: idx += 1
            self.__add_constant(diff.constant)

            # Check whether the sum's constant is now zero.
            if self.children[0].__is_constant(0):
                del self.children[0]
                idx -= 1

        return idx

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would cancel out sum terms. Transform the expression
    # if the given difference can be merged into one of the terms.
    def __check_transform_bitwise_for_diff_merge(self, toXor, idx, bitw, factor, diff, indices):
        constN = diff.__get_opt_const_factor()
        for i in indices:
            child = self.children[i]
            constC = child.__get_opt_const_factor()
            if not diff.__equals_neglecting_constants(child, constN != None, constC != None): continue

            # We found a child matching the difference. Transform the bitwise
            # expression.

            if not toXor or bitw.type == NodeType.CONJUNCTION: factor = -factor
            bitw.type = bitw.__get_transformed_bitwise_type(toXor)
            if (factor - 1) % self.__modulus != 0: bitw.__multiply(factor)
            self.children[idx] = bitw

            # Adapt the child's factor.
            if constC != None:
                assert(child.type == NodeType.PRODUCT)
                assert(child.children[0].type == NodeType.CONSTANT)
                if constN != None: child.children[0].constant = constN
                else:
                    del child.children[0]
                    if len(child.children) == 1: child.copy(child.children[0])
            elif constN != None:
                child.__multiply(constN)

            # Finally remove the children which we have merged into the bitwise
            # expression.
            for j in range(len(indices) - 1, -1, -1):
                if indices[j] != i:
                    del self.children[indices[j]]
                    if indices[j] < idx: idx -= 1

            return idx

        return None

    # Returns the type this node would have after transformation. If toXor is
    # True, EXCL_DISJUNCTION is returned.
    def __get_transformed_bitwise_type(self, toXor):
        assert(self.type in [NodeType.CONJUNCTION, NodeType.INCL_DISJUNCTION])

        if toXor: return NodeType.EXCL_DISJUNCTION
        if self.type == NodeType.CONJUNCTION: return NodeType.INCL_DISJUNCTION
        return NodeType.CONJUNCTION

    # Try to transform bitwise expressions in this sum such that one term,
    # corresponding to an operand, is replaced by another one, corresponding to
    # the other operand. Apply, e.g., the following rules, if x is more complex
    # than y:
    #
    #   "(x&y) - x"   -> "y - (x|y)"
    #   "(x|y) - x"   -> "y - (x&y)"
    #   "2*(x&y) - x" -> "y - (x^y)"
    #   "2*(x|y) - x" -> "y + (x^y)"
    def __check_bitwise_in_sums_replace_terms(self):
        if self.type != NodeType.SUM: return False
        # Save runtime in too large sums.
        if len(self.children) > MAX_CHILDREN_TO_TRANSFORM_BITW: return False

        changed = True
        i = 0
        while True:
            if i >= len(self.children): return changed

            child = self.children[i]
            factor = 1

            if child.type == NodeType.PRODUCT:
                if len(child.children) != 2 or child.children[0].type != NodeType.CONSTANT:
                    i += 1
                    continue

                factor = child.children[0].constant
                child = child.children[1]

            if child.type not in [NodeType.CONJUNCTION, NodeType.INCL_DISJUNCTION] or len(child.children) != 2:
                i += 1
                continue

            newIdx = self.__check_transform_bitwise_in_sum_replace(i, child, factor)
            if newIdx == None:
                i += 1
                continue

            assert(self.children[newIdx] == child)
            assert(len(self.children) > 1)

            # Adapt the iteration index.
            i = newIdx + 1

        return False

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # inclusive disjunction (if it is a conjunction) or a conjunction (resp.)
    # or an exclusive disjunction such that a more complex term is replaced by
    # a less complex one. If a transformation has happened, returns the new
    # index of the bitwise. Otherwise returns None.
    def __check_transform_bitwise_in_sum_replace(self, idx, bitw, factor):
        # Only continue if one operand is more complex than the other one.
        # Here we measure complexity via linearity.
        cIdx = bitw.__get_index_of_more_complex_operand()
        if cIdx == None: return None

        # For a transformation to Xor, we need a factor divisible by 2.
        withToXor = factor % 2 == 0

        newIdx = self.__check_transform_bitwise_in_sum_replace_impl(False, idx, bitw, cIdx, factor)
        if newIdx != None: return newIdx

        if withToXor:
            newIdx = self.__check_transform_bitwise_in_sum_replace_impl(True, idx, bitw, cIdx, factor // 2)
            if newIdx != None: return newIdx

        return None

    # For this node which is required to be a conjunction, exclusive or
    # inclusive disjunction with 2 operands, returns the index of its more
    # complex operand.
    def __get_index_of_more_complex_operand(self):
        assert(self.__is_bitwise_binop())
        assert(len(self.children) == 2)

        c0, c1 = self.children[0], self.children[1]

        c0.mark_linear()
        c1.mark_linear()

        l0 = c0.is_linear()
        l1 = c1.is_linear()

        if l0 != l1: return 0 if l1 else 1

        b0 = c0.state == NodeState.BITWISE
        b1 = c1.state == NodeState.BITWISE

        if b0 != b1: return 0 if b1 else 1
        # TODO: Count variables?
        else: return None

        # TODO: Further refinement?
        return None

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would replace a more complex term by a more simple
    # one, both corresponding to operands of the bitwise.
    #
    # If toXor is False, apply, e.g., the following rules:
    #   "(x&y) - x"   -> "y - (x|y)"
    #   "(x|y) - x"   -> "y - (x&y)"
    # If it is True, apply, e.g., the following rules:
    #   "2*(x&y) - x" -> "y - (x^y)"
    #   "2*(x|y) - x" -> "y + (x^y)"
    def __check_transform_bitwise_in_sum_replace_impl(self, toXor, idx, bitw, cIdx, factor):
        assert(self.type == NodeType.SUM)
        assert(idx < len(self.children))

        cOp = bitw.children[cIdx].get_copy()
        cOp.__multiply(factor)

        # Save runtime. It is not likely that we can sum up more children to a
        # node equal to cOp.
        maxc = MAX_CHILDREN_SUMMED_UP

        # Iterate over all subsets of children and check whether the children
        # sum up to the bitwise operation's operand.
        for i in range(1, 2**(len(self.children) - 1)):
            # Save runtime, see above.
            if popcount(i) > maxc: continue

            newIdx = self.__check_transform_bitwise_replace_for_comb(toXor, idx, bitw, factor, cOp, cIdx, i)
            if newIdx != None: return newIdx

        return None

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would replace a more complex term by a more simple
    # one, both corresponding to operands of the bitwise.
    def __check_transform_bitwise_replace_for_comb(self, toXor, idx, bitw, factor, cOp, cIdx, combIdx):
        n = combIdx

        diff = cOp.get_copy()
        indices = []

        for j in range(len(self.children)):
            if j == idx: continue

            if (n & 1) == 1:
                indices.append(j)
                diff.__add(self.children[j])
            n = n >> 1

        diff.expand()
        diff.refine()

        return self.__check_transform_bitwise_replace_for_diff(toXor, idx, bitw, factor, diff, cIdx, indices)

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would replace a more complex term by a more simple
    # one, both corresponding to operands of the bitwise. Here the difference
    # between the sum of candidate terms and the bitwise expression's operand
    # is given, together with a list of the terms' indices.
    def __check_transform_bitwise_replace_for_diff(self, toXor, idx, bitw, factor, diff, cIdx, indices):
        return self.__check_transform_bitwise_replace_for_diff_full(toXor, idx, bitw, factor, diff, cIdx, indices)

    # Try to transform the given bitwise expression, which is either a
    # conjunction or an inclusive disjunction and constitutes this sum node's
    # idx-th child after multiplication with the given factor, into an
    # exclusive disjunction (if toXor is true) or its inverse operation
    # (otherwise) if this would replace a more complex term by a more simple
    # one, both corresponding to operands of the bitwise. Transform the
    # expression if the given difference is a constant.
    def __check_transform_bitwise_replace_for_diff_full(self, toXor, idx, bitw, factor, diff, cIdx, indices):
        if diff.type != NodeType.CONSTANT: return None

        # We found a match. First append the less complex operand as a term.
        op = bitw.children[0 if cIdx == 1 else 1].get_copy()
        op.__multiply(factor)
        self.children.append(op)

        # Transform the bitwise expression.
        if not toXor or bitw.type == NodeType.CONJUNCTION: factor = -factor
        bitw.type = bitw.__get_transformed_bitwise_type(toXor)
        if (factor - 1) % self.__modulus != 0: bitw.__multiply(factor)
        self.children[idx] = bitw

        # Remove the children which we have merged into the bitwise expression.
        for j in range(len(indices) - 1, -1, -1):
            del self.children[indices[j]]
            if indices[j] < idx: idx -= 1

        # If the difference is not exactly zero, but constant, add this
        # constant.
        if not diff.__is_constant(0):
            if self.children[0].type != NodeType.CONSTANT: idx += 1
            self.__add_constant(diff.constant)

            # Check whether the sum's constant is now zero.
            if self.children[0].__is_constant(0):
                del self.children[0]
                idx -= 1

        return idx


    # If this node is a sum, check whether any terms can be refined using the
    # following rules:
    #    x[&y]|x^y -> (x&y) + (x^y)
    #    z&x[&y]|x^y -> (z&x&y) + (x^y)
    def __check_disj_involving_xor_in_sums(self):
        if self.type != NodeType.SUM: return False

        changed = False

        for child in self.children:
            factor = 1
            node = child

            if node.type == NodeType.PRODUCT:
                if len(node.children) != 2: continue
                if node.children[0].type != NodeType.CONSTANT: continue

                factor = node.children[0].constant
                node = node.children[1]

            if node.type != NodeType.INCL_DISJUNCTION: continue
            if len(node.children) != 2: continue

            xorIdx = None
            if node.children[0].type == NodeType.EXCL_DISJUNCTION: xorIdx = 0
            if node.children[1].type == NodeType.EXCL_DISJUNCTION:
                if xorIdx != None: continue
                xorIdx = 1
            if xorIdx == None: continue

            oIdx = 1 if xorIdx == 0 else 0
            xor = node.children[xorIdx]
            o = node.children[oIdx]

            if len(xor.children) != 2: continue

            if o.equals(xor.children[0]):
                o = self.__new_node_with_children(NodeType.CONJUNCTION, [o.__get_shallow_copy(), xor.children[1].get_copy()])

            elif o.equals(xor.children[1]):
                o = self.__new_node_with_children(NodeType.CONJUNCTION, [o.__get_shallow_copy(), xor.children[0].get_copy()])

            elif o.type != NodeType.CONJUNCTION: continue

            else:
                found0 = False
                found1 = False

                for ch in o.children:
                    if ch.equals(xor.children[0]): found0 = True
                    elif ch.equals(xor.children[1]): found1 = True

                    if found0 and found1: break

                if found0:
                    if not found1: o.children.append(xor.children[1].get_copy())
                elif found1: o.children.append(xor.children[0].get_copy())
                else: continue

            # Make sure that constants are in first child.
            o.__inspect_constants()

            # If we are here, we know that we can transform the child.
            changed = True

            if factor == 1: self.children.append(xor.__get_shallow_copy())
            else:
                prod = self.__new_node_with_children(NodeType.PRODUCT, [self.__new_constant_node(factor), xor.__get_shallow_copy()])
                self.children.append(prod)
            node.copy(o)

        return changed


    # If this node is an exclusive disjunction, check whether it can be refined
    # using the following rule:
    #    x^(x|y) -> ~x&y
    def __check_xor_involving_disj(self):
        if self.type != NodeType.EXCL_DISJUNCTION: return False
        if len(self.children) != 2: return False

        for disjIdx in [0, 1]:
            disj = self.children[disjIdx]
            if disj.type != NodeType.INCL_DISJUNCTION: continue

            oIdx = 1 if disjIdx == 0 else 0
            other = self.children[oIdx]
            idx = disj.__get_index_of_child(other)
            # The disjunction does not contain the xor's other operand as
            # an operand.
            if idx == None: continue

            other.__negate()
            self.type = NodeType.CONJUNCTION

            del disj.children[idx]
            if len(disj.children) == 1: self.children[disjIdx] = disj.children[0]

            return True

        return False


    # If this node is an exclusive disjunction, check whether it can be refined
    # using the following rules:
    #    -(x&-x) -> x|-x
    #    -(x|-x) -> x&-x
    def __check_negative_bitw_inverse(self):
        if self.type != NodeType.PRODUCT: return False
        if len(self.children) != 2: return False
        if not self.children[0].__is_constant(-1): return False

        node = self.children[1]
        if node.type not in [NodeType.CONJUNCTION, NodeType.INCL_DISJUNCTION]: return False
        # TODO: We can consider all but one operand as a large single operand.
        if len(node.children) != 2: return False
        if node.children[0].type == NodeType.CONSTANT: return False

        inv = node.children[0].get_copy()
        inv.__multiply_by_minus_one()
        if not inv.equals(node.children[1]): return False

        if node.type == NodeType.CONJUNCTION: node.type = NodeType.INCL_DISJUNCTION
        else: node.type = NodeType.CONJUNCTION

        self.copy(node)
        return True


    # If this node is a sum, collect all terms which can be merged applying the
    # formula "(a^x) + (b^x) == 2*(~(a+b)&x) + a + b", where we require a and b
    # to be constant.
    def __check_xor_pairs_with_constants(self):
        if self.type != NodeType.SUM: return False

        l = self.__collect_indices_of_bitw_with_constants_in_sum(NodeType.EXCL_DISJUNCTION)
        if len(l) == 0: return False

        toRemove = []
        const = 0

        for pair in l:
            factor = pair[0]
            sublist = pair[1]
            done = [False for x in sublist]

            for i in range(len(sublist) - 1, 0, -1):
                if done[i]: continue

                for j in range(0, i):
                    if done[j]: continue

                    firstIdx = sublist[i]
                    first = self.children[firstIdx]
                    if first.type == NodeType.PRODUCT: first = first.children[1]
                    assert(first.type == NodeType.EXCL_DISJUNCTION)

                    secIdx = sublist[j]
                    second = self.children[secIdx]
                    if second.type == NodeType.PRODUCT: second = second.children[1]
                    assert(second.type == NodeType.EXCL_DISJUNCTION)

                    firstConst = first.children[0].constant % self.__modulus
                    secConst = second.children[0].constant % self.__modulus
                    # The set bits are not disjunct.
                    if (firstConst & secConst) != 0: continue

                    _, remove, add = self.__merge_bitwise_terms(firstIdx, secIdx, first, second, factor,
                                                first.children[0].constant, second.children[0].constant)
                    const += add

                    # Make sure that this node is not used any more since it is
                    # now a conjunction.
                    done[j] = True
                    assert(remove)
                    if remove: toRemove.append(secIdx)

        # Nothing has changed.
        if len(toRemove) == 0: return False

        # Remove all children that have been merged into others.
        toRemove.sort()
        for idx in reversed(toRemove): del self.children[idx]

        # Adapt the constant.
        if self.children[0].type == NodeType.CONSTANT:
            self.children[0].__set_and_reduce_constant(self.children[0].constant + const)
        else: self.children.insert(0, self.__new_constant_node(const))
        if len(self.children) > 1 and self.children[0].__is_constant(0): del self.children[0]

        return True

    # Returns a list of all terms in this sum node which are constant multiples
    # of bitwise operations of given type with a constant operator.
    def __collect_indices_of_bitw_with_constants_in_sum(self, expType):
        assert(self.type == NodeType.SUM)

        # A list containing tuples of factors and lists of indices.
        l = []
        for i in range(len(self.children)):
            factor, node = self.children[i].__get_factor_of_bitw_with_constant(expType)
            assert((factor == None) == (node == None))
            if factor == None: continue

            found = False
            for pair in l:
                if factor != pair[0]: continue

                sublist = pair[1]
                firstIdx = sublist[0]
                first = self.children[firstIdx]
                if first.type == NodeType.PRODUCT: first = first.children[1]
                assert(first.type == expType)

                if len(node.children) != len(first.children): continue
                if not do_children_match(node.children[1:], first.children[1:]): continue

                sublist.append(i)
                found = True
                break

            if not found:
                l.append([factor, [i]])

        return l

    # If this node is a multiple of a bitwise operation of given type and with
    # a constant operator, returns the factor. Otherwise returns None.
    # Additionally returns the bitwise operation or None, resp. If expType is
    # None, considers all binary bitwise operations.
    def __get_factor_of_bitw_with_constant(self, expType=None):
        factor = None
        node = None

        if self.__is_bitwise_binop():
            if expType != None and self.type != expType: return None, None

            factor = 1
            node = self

        elif self.type != NodeType.PRODUCT: return None, None
        elif len(self.children) != 2: return None, None
        elif self.children[0].type != NodeType.CONSTANT: return None, None
        elif not self.children[1].__is_bitwise_binop(): return None, None
        elif expType != None and self.children[1].type != expType: return None, None

        else:
            factor = self.children[0].constant
            node = self.children[1]

        if node.children[0].type != NodeType.CONSTANT: return None, None

        return factor, node


    # If this node is a sum, collect all terms which can be merged applying the
    # formulas "(a&x) + (b&x) == (a+b)&x" and "(a|x) + (b|x) == (a+b)|x" if a
    # and b are constants that have no set bit in common.
    def __check_bitw_pairs_with_constants(self):
        if self.type != NodeType.SUM: return False

        changed = False
        for conj in [True, False]:
            if self.__check_bitw_pairs_with_constants_impl(conj):
                changed = True
                if self.type != NodeType.SUM: return True

        return changed

    # If this node is a sum, collect all terms which can be merged applying the
    # formula "(a&x) + (b&x) == a+b&x" (if conj is True) or
    #"(a|x) + (b|x) == (a+b|x) + x" (otherwise) if a and b are constants that
    # have no set bit in common.
    def __check_bitw_pairs_with_constants_impl(self, conj):
        assert(self.type == NodeType.SUM)

        expType = NodeType.CONJUNCTION if conj else NodeType.INCL_DISJUNCTION
        l = self.__collect_indices_of_bitw_with_constants_in_sum(expType)
        if len(l) == 0: return False

        toRemove = []
        changed = False

        for pair in l:
            factor = pair[0]
            sublist = pair[1]

            for i in range(len(sublist) - 1, 0, -1):
                for j in range(0, i):
                    firstIdx = sublist[j]
                    first = self.children[firstIdx]
                    if first.type == NodeType.PRODUCT: first = first.children[1]
                    assert(first.type == expType)

                    secIdx = sublist[i]
                    second = self.children[secIdx]
                    if second.type == NodeType.PRODUCT: second = second.children[1]
                    assert(second.type == expType)

                    firstConst = first.children[0].constant % self.__modulus
                    secConst = second.children[0].constant % self.__modulus
                    # The set bits are not disjunct.
                    if (firstConst & secConst) != 0: continue

                    _, remove, _ = self.__merge_bitwise_terms(firstIdx, secIdx, first, second,
                                                              factor, firstConst, secConst)
                    if remove: toRemove.append(secIdx)

                    changed = True
                    break

        # Nothing has changed.
        if not changed: return False

        # Remove all children that have been merged into others.
        toRemove.sort()
        for idx in reversed(toRemove): del self.children[idx]

        if len(self.children) == 1: self.copy(self.children[0])
        return True


    # If this node is a sum, check whether we can merge terms applying the
    # following formulas:
    #
    #   -2*(a&x) + (b^x) -> 2*(~(a+b)&x) - x + b
    #    2*(a|x) + (b^x) -> 2*(~(a+b)&x) + x + 2*a + b
    #   -(a&x) + (b|x) -> (~(a+b)&x) + b
    #
    # They are consequences of the following formulas:
    #
    #   2*(x&y) - x - y -> -(x^y)
    #   2*(x|y) - x - y -> x^y
    #   (a^x) + (b^x) -> 2*(~(a+b)&x) + a + b
    #
    # We require that a and b are constants that have no set bits in common.
    def __check_diff_bitw_pairs_with_constants(self):
        if self.type != NodeType.SUM: return False

        l = self.__collect_all_indices_of_bitw_with_constants()
        if len(l) == 0: return False

        toRemove = []
        const = 0
        changed = False

        for sublist in l:
            for i in range(len(sublist) - 1, 0, -1):
                for j in range(0, i):
                    firstFactor, firstIdx = sublist[j]
                    first = self.children[firstIdx]
                    if first.type == NodeType.PRODUCT: first = first.children[1]

                    secFactor, secIdx = sublist[i]
                    second = self.children[secIdx]
                    if second.type == NodeType.PRODUCT: second = second.children[1]

                    # This case has already been handled previously.
                    if first.type == second.type: continue

                    firstConst = first.children[0].constant % self.__modulus
                    secConst = second.children[0].constant % self.__modulus
                    # The set bits are not disjunct.
                    if (firstConst & secConst) != 0: continue

                    # Check the factors.
                    factor = self.__get_factor_for_merging_bitwise(firstFactor, secFactor, first.type, second.type)
                    if factor == None: continue

                    bitwFactor, remove, add = self.__merge_bitwise_terms(firstIdx, secIdx, first, second,
                                                                         factor, firstConst, secConst)
                    const += add

                    if remove: toRemove.append(secIdx)
                    # Finally adapt the factor in the list.
                    sublist[j][0] = bitwFactor

                    changed = True
                    break

        # Nothing has changed.
        if not changed: return False

        # Remove all children that have been merged into others.
        toRemove.sort()
        for idx in reversed(toRemove): del self.children[idx]

        # Adapt the constant.
        if self.children[0].type == NodeType.CONSTANT:
            self.children[0].__set_and_reduce_constant(self.children[0].constant + const)
        else: self.children.insert(0, self.__new_constant_node(const))
        if len(self.children) > 1 and self.children[0].__is_constant(0): del self.children[0]

        if len(self.children) == 1: self.copy(self.children[0])
        return True

    # Returns a list of all terms in this sum node which are constant multiples
    # of bitwise operations with a constant operand.
    def __collect_all_indices_of_bitw_with_constants(self):
        assert(self.type == NodeType.SUM)

        # A list containing tuples of factors and lists of indices.
        l = []

        for i in range(len(self.children)):
            factor, node = self.children[i].__get_factor_of_bitw_with_constant()
            assert((factor == None) == (node == None))
            if factor == None: continue

            assert(node.__is_bitwise_binop())

            found = False
            for sublist in l:
                firstIdx = sublist[0]
                first = self.children[firstIdx[1]]
                if first.type == NodeType.PRODUCT: first = first.children[1]

                if len(node.children) == 2:
                    if len(first.children) == 2:
                        if not node.children[1].equals(first.children[1]): continue
                    else:
                        if node.children[1].type != first.type: continue
                        assert(len(first.children) > 2)
                        if not do_children_match(node.children[1].children, first.children[1:]): continue

                elif len(first.children) == 2:
                    if first.children[1].type != node.type: continue
                    assert(len(node.children) > 2)
                    if not do_children_match(first.children[1].children, node.children[1:]): continue

                elif not do_children_match(first.children[1:], node.children[1:]): continue

                sublist.append([factor, i])
                found = True
                break

            if not found:
                l.append([[factor, i]])

        return l

    # If the given factors and node types allow merging the nodes, returns a
    # factor for merging. Otherwise returns None.
    def __get_factor_for_merging_bitwise(self, fac1, fac2, type1, type2):
        if type1 == type2:
            if (fac1 - fac2) % self.__modulus != 0: return None
            return fac1

        if type1 == NodeType.EXCL_DISJUNCTION:
            if type2 == NodeType.CONJUNCTION:
                if (2*fac1 + fac2) % self.__modulus != 0: return None
            else:
                if (2*fac1 - fac2) % self.__modulus != 0: return None
            return fac1

        if type1 == NodeType.CONJUNCTION:
            if type2 == NodeType.EXCL_DISJUNCTION:
                if (fac1 + 2*fac2) % self.__modulus != 0: return None
            else:
                if (fac1 + fac2) % self.__modulus != 0: return None
            return fac2

        if type2 == NodeType.EXCL_DISJUNCTION:
            if (-fac1 + 2*fac2) % self.__modulus != 0: return None
            return fac2
        if (fac1 + fac2) % self.__modulus != 0: return None
        return fac1

    # Merges the given pair of bitwise operations. Returns the new factor of
    # the merged term, True iff the second one is to be removed and an optional
    # constant to be added later on. Apply the following rules:
    #
    #   (a&x) + (b&x) -> a+b&x
    #   (a|x) + (b|x) -> (a+b|x) + x
    #   (a^x) + (b^x) -> 2*(~(a+b)&x) + a + b
    #   -2*(a&x) + (b^x) -> 2*(~(a+b)&x) - x + b
    #    2*(a|x) + (b^x) -> 2*(~(a+b)&x) + x + 2*a + b
    #   -(a&x) + (b|x) -> (~(a+b)&x) + b
    def __merge_bitwise_terms(self, firstIdx, secIdx, first, second, factor, firstConst, secConst):
        bitwFactor, add, opfac = self.__merge_bitwise_terms_and_get_opfactor(firstIdx, secIdx, first, second,
                                                                             factor, firstConst, secConst)
        if opfac == 0: return bitwFactor, True, add

        if len(second.children) == 2: self.children[secIdx] = second.children[1]
        else:
            self.children[secIdx] = second.__get_shallow_copy()
            del self.children[secIdx].children[0]

        if opfac != 1: self.children[secIdx].__multiply(opfac)
        return bitwFactor, False, add

    # Merges the given pair of bitwise operations, but does not manipulate the
    # second bitwise yet, even if it would be to be replaced by the operand.
    # Returns the new factor of the merged term,  an optional constant to be
    # added later on and a factor for the operand.
    def __merge_bitwise_terms_and_get_opfactor(self, firstIdx, secIdx, first, second, factor, firstConst, secConst):
        constSum = firstConst + secConst
        constNeg = -constSum - 1
        bitwFactor = self.__get_bitwise_factor_for_merging_bitwise(factor, first.type, second.type)
        opfac, add = self.__get_operand_factor_and_constant_for_merging_bitwise(factor, first.type, second.type, firstConst, secConst)

        hasFactor = self.children[firstIdx].type == NodeType.PRODUCT
        # We modify the first child and mark the second for removal, or replace
        # it by the operand.
        first.children[0].__set_and_reduce_constant(self.__get_const_operand_for_merging_bitwise(constSum, first.type, second.type))
        if first.type != second.type or first.type != NodeType.INCL_DISJUNCTION:
            # If we have more operands, we have to reorganize everything before
            # we change the type.
            if first.type != NodeType.CONJUNCTION and len(first.children) > 2:
                node = self.__new_node(first.type)
                node.children.append(first.children[0].__get_shallow_copy())
                del first.children[0]
                node.children.append(first.__get_shallow_copy())
                first.copy(node)

            first.type = NodeType.CONJUNCTION

        if hasFactor:
            if bitwFactor == 1: self.children[firstIdx] = first
            else: self.children[firstIdx].children[0].__set_and_reduce_constant(bitwFactor)
        elif bitwFactor != 1:
            factorNode = self.__new_constant_node(bitwFactor)
            prod = self.__new_node_with_children(NodeType.PRODUCT, [factorNode, first.__get_shallow_copy()])
            self.children[firstIdx].copy(prod)

        return bitwFactor, add, opfac

    # For merging bitwise operations with given types and given factor, returns
    # the new constant operand of the bitwise.
    def __get_const_operand_for_merging_bitwise(self, constSum, type1, type2):
        if type1 == type2 and type1 != NodeType.EXCL_DISJUNCTION: return constSum
        # Return ~(const1 + const2).
        return -constSum - 1

    # For merging bitwise operations with given types and given factor, returns
    # the resulting factor of the new bitwise.
    def __get_bitwise_factor_for_merging_bitwise(self, factor, type1, type2):
        if type1 == NodeType.EXCL_DISJUNCTION or type2 == NodeType.EXCL_DISJUNCTION: return 2 * factor
        return factor

    # For merging bitwise operations with given types and given resulting
    # factor, returns the factor of their common second operand to be added.
    # Additionally returns a constant to be added.
    def __get_operand_factor_and_constant_for_merging_bitwise(self, factor, type1, type2, const1, const2):
        if type1 == type2:
            if type1 == NodeType.CONJUNCTION: return 0, 0
            if type1 == NodeType.INCL_DISJUNCTION: return factor, 0
            return 0, (const1 + const2) * factor

        if type1 == NodeType.EXCL_DISJUNCTION:
            if type2 == NodeType.CONJUNCTION: return -factor, const1 * factor
            return factor, (const1 + 2*const2) * factor

        if type1 == NodeType.CONJUNCTION:
            if type2 == NodeType.EXCL_DISJUNCTION: return -factor, const2 * factor
            return 0, const2 * factor

        if type2 == NodeType.EXCL_DISJUNCTION: return factor, (2*const1 + const2) * factor
        return 0, const1 * factor


    # If this node is a sum, check whether we can merge multiple terms applying
    # the formulas from above:
    #
    #   (a&x) + (b&x) -> a+b&x
    #   (a|x) + (b|x) -> (a+b|x) + x
    #   (a^x) + (b^x) -> 2*(~(a+b)&x) + a + b
    #   -2*(a&x) + (b^x) -> 2*(~(a+b)&x) - x + b
    #    2*(a|x) + (b^x) -> 2*(~(a+b)&x) + x + 2*a + b
    #   -(a&x) + (b|x) -> (~(a+b)&x) + b
    #
    # We require that a and b are constants that have no set bits in common.
    # TODO: We require that each bitwise has 2 operands, but actually
    # additional operands may be merged into a subexpression.
    # TODO: We only handle triples here, and in detail only those where only
    # one bitwise is merged into the others. This can be extended.
    def __check_bitw_tuples_with_constants(self):
        if self.type != NodeType.SUM: return False

        l = self.__collect_all_indices_of_bitw_with_constants()
        if len(l) == 0: return False

        toRemove = []
        const = 0
        changed = False

        for sublist in l:
            for i in range(len(sublist) - 1, 1, -1):
                add = self.__try_merge_bitwise_with_constants_with_2_others(sublist, i, toRemove)
                if add != None:
                    changed = True
                    const += add

        # Nothing has changed.
        if not changed: return False

        # Remove all children that have been merged into others.
        toRemove.sort()
        for idx in reversed(toRemove): del self.children[idx]

        # Adapt the constant.
        if self.children[0].type == NodeType.CONSTANT:
            self.children[0].__set_and_reduce_constant(self.children[0].constant + const)
        else: self.children.insert(0, self.__new_constant_node(const))
        if len(self.children) > 1 and self.children[0].__is_constant(0): del self.children[0]

        if len(self.children) == 1: self.copy(self.children[0])
        return True

    # Try to merge the bitwise operation with constant corresponding to the
    # given list and the given index with 2 others from that list. Returns a
    # constant to be added if they have been merged, or None otherwise.
    # Moreover a list of indices to be removed later on is given, and
    # optionally extended.
    def __try_merge_bitwise_with_constants_with_2_others(self, sublist, i, toRemove):
        for j in range(1, i):
            for k in range(0, j):
                add = self.__try_merge_triple_bitwise_with_constants(sublist, i, j, k, toRemove)
                if add != None: return add

        return None

    # Try to merge the triple of bitwise operations with constants
    # corresponding to the given list and the given indices. Returns a constant
    # to be added if they have been merged, or None otherwise. Moreover a list
    # of indices to be removed later on is given, and optionally extended.
    def __try_merge_triple_bitwise_with_constants(self, sublist, i, j, k, toRemove):
        for perm in [[i, j, k], [j, i, k], [k, i, j]]:
            mainFactor, mainIdx = sublist[perm[0]]
            main = self.children[mainIdx]
            if main.type == NodeType.PRODUCT: main = main.children[1]
            mainConst = main.children[0].constant % self.__modulus

            firstFactor, firstIdx = sublist[perm[1]]
            first = self.children[firstIdx]
            if first.type == NodeType.PRODUCT: first = first.children[1]
            firstConst = first.children[0].constant % self.__modulus

            secFactor, secIdx = sublist[perm[2]]
            second = self.children[secIdx]
            if second.type == NodeType.PRODUCT: second = second.children[1]
            secConst = second.children[0].constant % self.__modulus

            # Get factors for merging.
            factor1, factor2 = self.__get_factors_for_merging_triple(first.type, second.type, main.type,
                                        firstFactor, secFactor, mainFactor, firstConst, secConst, mainConst)
            assert((factor1 == None) == (factor2 == None))
            # We cannot merge this triple.
            if factor1 == None: continue

            i1 = perm[1]
            # We can merge the triple. Rearrange it such that
            # the one that vanishes has the highest index i.
            if perm[0] != i:
                assert(perm[1] == i)
                sublist[perm[0]], sublist[perm[1]] = sublist[perm[1]], sublist[perm[0]]
                i1 = perm[0]

            bitwFactor1, add1, opfac1 = self.__merge_bitwise_terms_and_get_opfactor(firstIdx, mainIdx, first,
                                                                main, factor1, firstConst, mainConst)
            bitwFactor2, add2, opfac2 = self.__merge_bitwise_terms_and_get_opfactor(secIdx, mainIdx, second,
                                                                main, factor2, secConst, mainConst)
            opfac = (opfac1 + opfac2) % self.__modulus

            if opfac == None: toRemove.append(mainIdx)
            else:
                self.children[mainIdx] = main.children[1]
                if opfac != 1: self.children[mainIdx].__multiply(opfac)

            # Finally adapt the factors in the list.
            sublist[i1][0] = bitwFactor1
            sublist[perm[2]][0] = bitwFactor2

            return add1 + add2

        return None

    # Returns a pair of factors for merging a bitwise operations with a
    # constant into the other two such. Returns None, None if this is not
    # possible.
    def __get_factors_for_merging_triple(self, type1, type2, type0, fac1, fac2, fac0, const1, const2, const0):
        # Check whether the constants's 1 positions are disjunct.
        if (const1 & const0) != 0: return None, None
        if (const2 & const0) != 0: return None, None

        # Check whether the factors fit.
        factor1 = self.__get_possible_factor_for_merging_bitwise(fac1, type1, type0)
        if factor1 == None: return None, None
        factor2 = self.__get_possible_factor_for_merging_bitwise(fac2, type2, type0)
        if factor2 == None: return None, None

        # We cannot merge this triple.
        if (factor1 + factor2 - fac0) % self.__modulus != 0: return None, None

        factor1 = self.__get_factor_for_merging_bitwise(fac1, factor1, type1, type0)
        factor2 = self.__get_factor_for_merging_bitwise(fac2, factor2, type2, type0)
        assert(factor1 != None)
        assert(factor2 != None)
        return factor1, factor2

    # If the given factors and node types allow merging the nodes, returns a
    # factor for merging. Otherwise returns None, None.
    def __get_possible_factor_for_merging_bitwise(self, fac1, type1, type0):
        if type1 == NodeType.EXCL_DISJUNCTION:
            if type0 == NodeType.CONJUNCTION: return -2*fac1
            if type0 == NodeType.INCL_DISJUNCTION: return 2*fac1
            return fac1

        if type1 == NodeType.CONJUNCTION:
            if type0 == NodeType.EXCL_DISJUNCTION:
                if fac1 % 2 != 0: return None
                return -fac1 // 2
            if type0 == NodeType.CONJUNCTION: return fac1
            return -fac1

        if type0 == NodeType.EXCL_DISJUNCTION:
            if fac1 % 2 != 0: return None
            return fac1 // 2
        if type0 == NodeType.CONJUNCTION: return -fac1
        return fac1


    # If this node is a sum, collect all terms which can be merged applying the
    # following formulas:
    #
    #    (x&y) + (~x&y) -> y
    #    (x|y) + (~x|y) -> -1 + y
    #    (x^y) + (~x^y) -> -1
    def __check_bitw_pairs_with_inverses(self):
        if self.type != NodeType.SUM: return False

        changed = False
        for expType in [NodeType.CONJUNCTION, NodeType.EXCL_DISJUNCTION, NodeType.INCL_DISJUNCTION]:
            if self.__check_bitw_pairs_with_inverses_impl(expType):
                changed = True
                if self.type != NodeType.SUM: return True

        return changed

    # If this node is a sum, collect all terms which can be merged applying one
    # of the following formulas, depending on expType:
    #
    #    (x&y) + (~x&y) -> y
    #    (x|y) + (~x|y) -> -1 + y
    #    (x^y) + (~x^y) -> -1
    def __check_bitw_pairs_with_inverses_impl(self, expType):
        assert(self.type == NodeType.SUM)

        l = self.__collect_indices_of_bitw_without_constants_in_sum(expType)
        if len(l) == 0: return False

        toRemove = []
        changed = False
        const = 0

        for pair in l:
            factor = pair[0]
            sublist = pair[2]
            done = [False for x in sublist]

            for i in range(len(sublist) - 1, 0, -1):
                if done[i]: continue

                for j in range(0, i):
                    if done[j]: continue

                    firstIdx = sublist[j]
                    first = self.children[firstIdx]
                    if first.type == NodeType.PRODUCT: first = first.children[1]
                    assert(first.type == expType)

                    secIdx = sublist[i]
                    second = self.children[secIdx]
                    if second.type == NodeType.PRODUCT: second = second.children[1]
                    assert(second.type == expType)

                    indices = first.__get_only_differing_child_indices(second)
                    # There are either no or too many differing children.
                    if indices == None: continue

                    # The differing children are not inverse.
                    if not first.children[indices[0]].equals_negated(second.children[indices[1]]): continue

                    removeFirst, removeSec, add = self.__merge_inverse_bitwise_terms(firstIdx, secIdx, first, second, factor, indices)
                    const += add

                    if removeFirst: toRemove.append(firstIdx)
                    if removeSec: toRemove.append(secIdx)

                    # Make sure that this node is not used any more since it is
                    # in general no bitwise expression any more.
                    done[j] = True
                    changed = True
                    break

        # Nothing has changed.
        if not changed: return False

        # Remove all children that have been merged into others.
        if len(toRemove) > 0:
            toRemove.sort()
            for idx in reversed(toRemove): del self.children[idx]

        # Adapt the constant. It can even happen that all children have been
        # removed.
        if len(self.children) == 0:
            self.copy(self.__new_constant_node(const))
            return True

        if self.children[0].type == NodeType.CONSTANT:
            self.children[0].__set_and_reduce_constant(self.children[0].constant + const)
        else: self.children.insert(0, self.__new_constant_node(const))
        if len(self.children) > 1 and self.children[0].__is_constant(0): del self.children[0]

        if len(self.children) == 1: self.copy(self.children[0])
        return True

    # Returns a list of all terms in this sum node which are constant multiples
    # of bitwise operations of given type with no constant operator. The nodes
    # are partitioned wrt. their factors and their numbers of operands in the
    # bitwise expressions.
    def __collect_indices_of_bitw_without_constants_in_sum(self, expType):
        assert(self.type == NodeType.SUM)

        # A list containing tuples of factors and lists of indices.
        l = []
        for i in range(len(self.children)):
            factor, node = self.children[i].__get_factor_of_bitw_without_constant(expType)
            assert((factor == None) == (node == None))
            if factor == None: continue

            opCnt = len(node.children)
            found = False
            for triple in l:
                if factor != triple[0]: continue
                if opCnt != triple[1]: continue

                triple[2].append(i)
                found = True
                break

            if not found:
                l.append([factor, opCnt, [i]])

        return l

    # If this node is a multiple of a bitwise operation of given type and with
    # no constant operand, returns the factor. Otherwise returns None.
    # Additionally returns the bitwise operation or None, resp. If expType is
    # None, considers all binary bitwise operations.
    def __get_factor_of_bitw_without_constant(self, expType=None):
        factor = None
        node = None

        if self.__is_bitwise_binop():
            if expType != None and self.type != expType: return None, None

            factor = 1
            node = self

        elif self.type != NodeType.PRODUCT: return None, None
        elif len(self.children) != 2: return None, None
        elif self.children[0].type != NodeType.CONSTANT: return None, None
        elif not self.children[1].__is_bitwise_binop(): return None, None
        elif expType != None and self.children[1].type != expType: return None, None

        else:
            factor = self.children[0].constant
            node = self.children[1]

        if node.children[0].type == NodeType.CONSTANT: return None, None

        return factor, node

    # If this node and the given one differ in ()their type and) only one
    # child, returns this child's indices wrt this and the other node.
    # Otherwise returns None.
    def __get_only_differing_child_indices(self, other):
        if self.type == other.type:
            # In this case the nodes would have to have same child count.
            if len(self.children) != len(other.children): return None
            return self.__get_only_differing_child_indices_same_len(other)

        if len(self.children) == len(other.children):
            if len(self.children) != 2: return None
            return self.__get_only_differing_child_indices_same_len(other)

        if len(self.children) < len(other.children):
            if len(self.children) != 2: return None
            return self.__get_only_differing_child_indices_diff_len(other)

        if len(other.children) != 2: return None

        indices = other.__get_only_differing_child_indices_diff_len(self)
        if indices == None: return None
        return indices[1], indices[0]

    # If this node and the given one, which are required to have a coincident
    # number of children and to have same type or exactly 2 children, differ in
    # only one child, returns this child's indices wrt this and the other node.
    # Otherwise returns None.
    def __get_only_differing_child_indices_same_len(self, other):
        assert(self.type == other.type or (len(self.children) == 2))
        assert(len(self.children) == len(other.children))

        idx1 = None

        oIndices = list(range(len(other.children)))
        for i in range(len(self.children)):
            child = self.children[i]
            found = False
            for j in oIndices:
                if child.equals(other.children[j]):
                    oIndices.remove(j)
                    found = True

            if not found:
                if idx1 == None: idx1 = i
                # This is already the second child that does not appear in
                # other's children.
                else: return None

        # There are no differing children.
        if idx1 == None: return None

        assert(len(oIndices) == 1)
        return idx1, oIndices[0]

    # If this node and the given one, which are required to have no coincident
    # number of children and to have different typea, differ in only one child,
    # returns this child's indices wrt this and the other node. Otherwise
    # returns None. This node is required to have 2 children.
    def __get_only_differing_child_indices_diff_len(self, other):
        assert(self.type != other.type)
        assert(len(self.children) == 2)
        assert(len(other.children) > 2)

        for i in [0, 1]:
            idx = other.__get_index_of_child_negated(self.children[i])
            if idx == None: continue

            oi = 1 if i == 0 else 0

            if self.children[oi].type != other.type: continue
            if not do_children_match(self.children[oi].children, other.children[:idx] + other.children[idx+1:]): continue

            return i, idx

        return None

    # Merges the given pair of bitwise operations without constants and with
    # all equal operands but one inverse pair. Returns an optional constant to
    # be added later on. Apply the following rules:
    #
    #    (x&y) + (~x&y) -> y
    #    (x|y) + (~x|y) -> -1 + y
    #    (x^y) + (~x^y) -> -1
    #    (x|y) - (~x&y) -> x
    #    (x^y) - 2*(~x&y) -> x - y
    #    (x^y) + 2*(~x|y) -> -2 - x + y
    def __merge_inverse_bitwise_terms(self, firstIdx, secIdx, first, second, factor, indices):
        type1 = first.type
        type2 = second.type
        invOpFac, sameOpFac, add = self.__get_operand_factors_and_constant_for_merging_inverse_bitwise(factor, type1, type2)

        removeFirst = sameOpFac == 0
        if not removeFirst:
            hasFactor = self.children[firstIdx].type == NodeType.PRODUCT

            if len(first.children) == 2:
                assert(indices[0] in [0, 1])
                oIdx = 0 if indices[0] == 1 else 1
                first.copy(first.children[oIdx])
            else: del first.children[indices[0]]

            if hasFactor:
                if sameOpFac == 1: self.children[firstIdx] = first
                else: self.children[firstIdx].children[0].__set_and_reduce_constant(sameOpFac)
            elif sameOpFac != 1:
                factorNode = self.__new_constant_node(sameOpFac)
                prod = self.__new_node_with_children(NodeType.PRODUCT, [factorNode, first.__get_shallow_copy()])
                self.children[firstIdx].copy(prod)

            # Flatten the node if necessary.
            self.children[firstIdx].__flatten()

        removeSecond = invOpFac == 0
        if not removeSecond:
            hasFactor = self.children[secIdx].type == NodeType.PRODUCT

            second.copy(second.children[indices[1]])
            if self.__must_invert_at_merging_inverse_bitwise(type1, type2): second.__negate()

            if hasFactor:
                if invOpFac == 1: self.children[secIdx] = second
                else: self.children[secIdx].children[0].__set_and_reduce_constant(invOpFac)
            elif invOpFac != 1:
                factorNode = self.__new_constant_node(invOpFac)
                prod = self.__new_node_with_children(NodeType.PRODUCT, [factorNode, second.__get_shallow_copy()])
                self.children[secIdx].copy(prod)

            # Flatten the node if necessary.
            self.children[secIdx].__flatten()

        return removeFirst, removeSecond, add

    # For merging bitwise operations with given types and given factor, returns
    # the factor of their (inverse) differing operand, the factor of their
    # common operand(s) to be added and a constant to be added.
    def __get_operand_factors_and_constant_for_merging_inverse_bitwise(self, factor, type1, type2):
        if type1 == type2:
            if type1 == NodeType.CONJUNCTION: return 0, factor, 0
            if type1 == NodeType.INCL_DISJUNCTION: return 0, factor, -factor
            return 0, 0, -factor

        if type1 == NodeType.EXCL_DISJUNCTION:
            if type2 == NodeType.CONJUNCTION: return factor, -factor, 0
            return -factor, factor, -2 * factor

        if type1 == NodeType.CONJUNCTION:
            if type2 == NodeType.EXCL_DISJUNCTION: return factor, -factor, 0
            return factor, 0, 0

        if type2 == NodeType.EXCL_DISJUNCTION: return -factor, factor, -2 * factor
        return factor, 0, 0

    # For merging bitwise operations with given types, returns True iff the
    # inverse operand has to be inverted in the second term.
    def __must_invert_at_merging_inverse_bitwise(self, type1, type2):
        assert(type1 != type2)

        if type1 == NodeType.EXCL_DISJUNCTION: return True
        if type2 == NodeType.EXCL_DISJUNCTION: return False
        return type1 == NodeType.INCL_DISJUNCTION


    # If this node is a sum, collect all terms which can be merged applying the
    # following formulas:
    #
    #    (x|y) - (~x&y) -> x
    #    (x^y) - 2*(~x&y) -> x - y
    #    (x^y) + 2*(~x|y) -> -2 - x + y
    def __check_diff_bitw_pairs_with_inverses(self):
        if self.type != NodeType.SUM: return False

        l = self.__collect_all_indices_of_bitw_without_constants()
        if len(l) == 0: return False

        toRemove = []
        done = [False for x in l]
        changed = False
        const = 0

        for i in range(len(l) - 1, 0, -1):
            if done[i]: continue

            for j in range(0, i):
                if done[j]: continue

                firstFactor, firstIdx = l[j]
                first = self.children[firstIdx]
                if first.type == NodeType.PRODUCT: first = first.children[1]

                secFactor, secIdx = l[i]
                second = self.children[secIdx]
                if second.type == NodeType.PRODUCT: second = second.children[1]

                # This case has already been handled previously.
                if first.type == second.type: continue

                # Check the factors.
                factor = self.__get_factor_for_merging_bitwise(firstFactor, secFactor, first.type, second.type)
                if factor == None: continue

                indices = first.__get_only_differing_child_indices(second)
                # There are either no or too many differing children.
                if indices == None: continue

                # The differing children are not inverse.
                if not first.children[indices[0]].equals_negated(second.children[indices[1]]): continue

                removeFirst, removeSec, add = self.__merge_inverse_bitwise_terms(firstIdx, secIdx, first, second, factor, indices)
                const += add

                if removeFirst: toRemove.append(firstIdx)
                if removeSec: toRemove.append(secIdx)

                # Make sure that this node is not used any more since it is
                # in general no bitwise expression any more.
                done[j] = True
                changed = True
                break

        # Nothing has changed.
        if not changed: return False

        # Remove all children that have been merged into others.
        if len(toRemove) > 0:
            toRemove.sort()
            for idx in reversed(toRemove): del self.children[idx]

        # Adapt the constant. It can even happen that all children have been
        # removed.
        if len(self.children) == 0:
            self.copy(self.__new_constant_node(const))
            return True

        if self.children[0].type == NodeType.CONSTANT:
            self.children[0].__set_and_reduce_constant(self.children[0].constant + const)
        else: self.children.insert(0, self.__new_constant_node(const))
        if len(self.children) > 1 and self.children[0].__is_constant(0): del self.children[0]

        if len(self.children) == 1: self.copy(self.children[0])
        return True

    # Returns a list of all terms in this sum node which are constant multiples
    # of bitwise operations with no constant operator.
    def __collect_all_indices_of_bitw_without_constants(self):
        assert(self.type == NodeType.SUM)

        # A list containing tuples of factors and indices.
        l = []
        for i in range(len(self.children)):
            factor, node = self.children[i].__get_factor_of_bitw_without_constant()
            assert((factor == None) == (node == None))
            if factor == None: continue

            l.append([factor, i])

        return l


    # If this node is a sum, check whether we can transform it into one term
    # applying the following formulas:
    #
    #    x - (x&y) -> x&~y
    #    (x|y) - x -> ~(x|~y)
    #
    # TODO: This is of course also possible if we have more terms in the sum,
    # but then we only reduce the number of terms, but cannot eliminate the
    # sum. Discuss.
    def __check_bitw_and_op_in_sum(self):
        if self.type != NodeType.SUM: return False

        for bitwIdx in range(len(self.children)):
            bitw = self.children[bitwIdx]
            disj = bitw.type == NodeType.INCL_DISJUNCTION

            if not disj:
                if bitw.type != NodeType.PRODUCT: continue
                if not bitw.children[0].__is_constant(-1): continue

                bitw = bitw.children[1]
                if bitw.type != NodeType.CONJUNCTION: continue

            # If we are here, the bitwise has already been validated. Now check
            # the other term(s).

            other = None
            if len(self.children) == 2:
                oIdx = 1 if bitwIdx == 0 else 0
                other = self.children[oIdx].get_copy()
            else:
                other = self.get_copy()
                del other.children[bitwIdx]

            if disj: other.__multiply_by_minus_one()
            idx = bitw.__get_index_of_child(other)

            # The bitwise does not contain the other term (or its inverse,
            # resp.) as an operand.
            if idx == None: continue

            # Finally transform the sum.

            self.copy(bitw)

            # If the bitwise has more than 2 operands, we have to rearrange
            # everything.
            if len(self.children) > 2:
                node = bitw.__get_shallow_copy()
                del node.children[idx]
                neg = self.__new_node_with_children(NodeType.NEGATION, [node])
                self.children = [self.children[idx].__get_shallow_copy(), neg]
            else:
                oIdx = 1 if idx == 0 else 0
                self.children[oIdx].__negate()

            if disj:
                self.copy(self.__new_node_with_children(NodeType.NEGATION, [self.__get_shallow_copy()]))

            return True

        return False


    # If this node is a sum, check whether we can merge terms applying the
    # following formula:
    #
    #    (x|y) - (x&y) -> x^y
    def __check_insert_xor_in_sum(self):
        if self.type != NodeType.SUM: return False

        changed = False
        i = -1
        while True:
            i += 1
            if i >= len(self.children): break

            first = self.children[i].get_copy()
            first.__multiply_by_minus_one()

            if first.type not in [NodeType.CONJUNCTION, NodeType.PRODUCT]: continue
            if first.type != NodeType.PRODUCT and len(first.children) != 2: continue

            for j in range(len(self.children)):
                if i == j: continue

                disj = self.children[j]

                if disj.type not in [NodeType.INCL_DISJUNCTION, NodeType.PRODUCT]: continue
                if (first.type == NodeType.PRODUCT) != (disj.type == NodeType.PRODUCT): continue

                conj = first
                if conj.type == NodeType.PRODUCT:
                    indices = conj.__get_only_differing_child_indices(disj)
                    if indices == None: continue

                    conj = conj.children[indices[0]]
                    disj = disj.children[indices[1]]

                    if conj.type != NodeType.CONJUNCTION: continue
                    if disj.type != NodeType.INCL_DISJUNCTION: continue

                if not do_children_match(conj.children, disj.children): continue

                disj.type = NodeType.EXCL_DISJUNCTION
                del self.children[i]
                # Decrease i because it will be increased at the start of the
                # next iteration.
                i -= 1

                changed = True
                break

        if not changed: return False

        if len(self.children) == 1: self.copy(self.children[0])
        return True


    # Returns if this node is a bitwise expression or at least a linear MBA.
    def is_linear(self):
        return self.state == NodeState.BITWISE or self.state == NodeState.LINEAR

    # Mark all nodes with labels indicating whether their subexpressions are
    # completely bitwise, linear or nonlinear expressions. If restrictedScope
    # is True, the child nodes are assumed to be already marked.
    def mark_linear(self, restrictedScope=False):
        for c in self.children:
            if not restrictedScope or c.state == NodeState.UNKNOWN: c.mark_linear()

        if self.type == NodeType.INCL_DISJUNCTION: self.__mark_linear_bitwise()
        elif self.type == NodeType.EXCL_DISJUNCTION: self.__mark_linear_bitwise()
        elif self.type == NodeType.CONJUNCTION: self.__mark_linear_bitwise()
        elif self.type == NodeType.SUM: self.__mark_linear_sum()
        elif self.type == NodeType.PRODUCT: self.__mark_linear_product()
        elif self.type == NodeType.NEGATION: self.__mark_linear_bitwise()
        elif self.type == NodeType.POWER: self.__mark_linear_power()
        elif self.type == NodeType.VARIABLE: self.__mark_linear_variable()
        elif self.type == NodeType.CONSTANT: self.__mark_linear_constant()

        # If the subexpression is nonlinear, check whether it has linear
        # children and reorder children such that the linear ones come first.
        self.__reorder_and_determine_linear_end()

    # Mark the node of a bitwise expression with labels indicating whether
    # their subexpressions are completely bitwise, linear or nonlinear
    # expressions. Assumes that its children have already been marked.
    def __mark_linear_bitwise(self):
        for c in self.children:
            assert(c.state != NodeState.UNKNOWN)
            if c.state != NodeState.BITWISE:
                self.state = NodeState.MIXED
                return

        self.state = NodeState.BITWISE

    # Mark the node of a sum with labels indicating whether their
    # subexpressions are completely bitwise, linear or nonlinear expressions.
    # Assumes that its children have already been marked.
    def __mark_linear_sum(self):
        assert (len(self.children) > 1)
        self.state = NodeState.UNKNOWN

        for c in self.children:
            assert(c.state != NodeState.UNKNOWN)
            if c.state == NodeState.MIXED:
                self.state = NodeState.MIXED
                return
            elif c.state == NodeState.NONLINEAR: self.state = NodeState.NONLINEAR

        if self.state != NodeState.NONLINEAR: self.state = NodeState.LINEAR

    # Mark the node of a product with labels indicating whether their
    # subexpressions are completely bitwise, linear or nonlinear expressions.
    # Assumes that its children have already been marked.
    def __mark_linear_product(self):
        assert(len(self.children) > 0)
        
        # Should not happen, but be sure.
        if len(self.children) < 2: self.state = self.children[0].state

        for c in self.children:
            assert(c.state != NodeState.UNKNOWN)
            if c.state == NodeState.MIXED:
                self.state = NodeState.MIXED
                return

        # We assume that all constants have been merged into the first child.
        if len(self.children) > 2:
            self.state = NodeState.NONLINEAR
        elif self.children[0].type == NodeType.CONSTANT and self.children[1].is_linear():
            self.state = NodeState.LINEAR
        elif self.children[1].type == NodeType.CONSTANT and self.children[0].is_linear():
            self.state = NodeState.LINEAR
        else: self.state = NodeState.NONLINEAR

    # Mark the node of a power to be nonlinear. Note that we assume that the
    # node has already been refined and is hence no trivial power.
    def __mark_linear_power(self):
        for c in self.children:
            assert(c.state != NodeState.UNKNOWN)
            if c.state == NodeState.MIXED:
                self.state = NodeState.MIXED
                return

        self.state = NodeState.NONLINEAR

    # Mark the node of a variable to be a bitwise expression.
    def __mark_linear_variable(self):
        self.state = NodeState.BITWISE

    # Mark the node of a constant to be a linear expression.
    def __mark_linear_constant(self):
        if self.__is_constant(0) or self.__is_constant(-1): self.state = NodeState.BITWISE
        else: self.state = NodeState.LINEAR

    # Determine the index of the first child that is not linear and reorder
    # the children such that the linear ones precede the nonlinear ones, except
    # for power nodes. Do nothing for the latter since the power is not
    # commutative.
    def __reorder_and_determine_linear_end(self):
        self.linearEnd = 0

        # We do not perform reordering for power operator.
        if self.type == NodeType.POWER: return

        if self.state != NodeState.NONLINEAR and self.state != NodeState.MIXED:
            self.linearEnd = len(self.children)
            return

        if self.type == NodeType.PRODUCT:
            self.__reorder_and_determine_linear_end_product()
            return

        for i in range(len(self.children)):
            child = self.children[i]
            bitwise = self.type in [NodeType.CONJUNCTION, NodeType.EXCL_DISJUNCTION, NodeType.INCL_DISJUNCTION, NodeType.NEGATION]
            if child.state == NodeState.BITWISE or (not bitwise and child.state == NodeState.LINEAR):
                if self.linearEnd < i:
                    self.children.remove(child)
                    self.children.insert(self.linearEnd, child)
                self.linearEnd += 1

    # Assuming that this node is a product, determine the index of the first
    # child that is not linear and reorder the children such that the linear
    # ones precede the nonlinear ones. In a product at most two nodes can
    # constitute a linear subexpression, where one of them has to be constant.
    def __reorder_and_determine_linear_end_product(self):
        if self.children[0].type != NodeType.CONSTANT: return

        self.linearEnd = 1
        for i in range(1, len(self.children)):
            child = self.children[i]
            if child.state != NodeState.NONLINEAR and child.state != NodeState.MIXED:
                if self.linearEnd < i:
                    self.children.remove(child)
                    self.children.insert(self.linearEnd, child)
                self.linearEnd += 1
                if self.linearEnd == 2: return


    # Returns, if existent, a node representing a subexpression whose
    # substitution may make the expression more suitable for simplification.
    def get_node_for_substitution(self, ignoreList):
        if self.__is_contained(ignoreList): return None

        if self.__is_bitwise_op():
            for child in self.children:
                if child.type == NodeType.CONSTANT or child.__is_arithm_op():
                    if not child.__is_contained(ignoreList): return child.get_copy()

                elif child.__is_bitwise_op():
                    node = child.get_node_for_substitution(ignoreList)
                    if node != None: return node

            return None

        # In powers, only substitute in their bases.
        if self.type == NodeType.POWER:
            return self.children[0].get_node_for_substitution(ignoreList)

        # For sums and products.
        for child in self.children:
            node = child.get_node_for_substitution(ignoreList)
            if node != None: return node

        return None

    # Returns true iff this node is equal to any contained in the given list.
    def __is_contained(self, l):
        return self.__get_index_in_list(l) != None

    # Returns true iff this node is equal to any contained in the given list.
    def __get_index_in_list(self, l):
        for i in range(len(l)):
            if self.equals(l[i]): return i
        return None

    # Substitute all nodes equivalent to the given one by a variable with given
    # name. Returns true iff at least one substitution is performed.
    def substitute_all_occurences(self, node, vname, onlyFullMatch=False, withMod=True):
        # In powers, only substitute in their bases.
        if self.type == NodeType.POWER:
            return self.children[0].substitute_all_occurences(node, vname, onlyFullMatch, withMod)

        changed = False
        bitwise = self.__is_bitwise_op()

        # The same node, but multiplied by minus one.
        inv = None
        if not bitwise and not onlyFullMatch and withMod:
            inv = node.get_copy()
            inv.__multiply_by_minus_one()

        for child in self.children:
            ch, done = child.__try_substitute_node(node, vname, bitwise)
            if ch: changed = True
            if done: continue

            if not bitwise and not onlyFullMatch and withMod:
                assert(inv != None)

                # Check whether the inverse node is equal to the child node.
                ch, done = child.__try_substitute_node(inv, vname, False, True)
                if ch: changed = True
                if done: continue

                # If the given node is a sum, try to substitute terms occuring in
                # it and adding the missing terms additionally.
                if child.__try_substitute_part_of_sum(node, vname):
                    changed = True
                    continue

                # Same for the inverse node.
                if child.__try_substitute_part_of_sum(inv, vname, True):
                    changed = True
                    continue

            if bitwise and not child.__is_bitwise_op(): continue

            if child.substitute_all_occurences(node, vname, onlyFullMatch, withMod):
                changed = True

        return changed

    # Substitute this node (or a part of it) by a variable with given name if
    # it is equivalent to the given node. If negated is True, the variable node
    # has to be multiplied by -1. Returns a flag indicating whether a
    # substition has been performed and another flag indicating whether no
    # other substitution is possible.
    def __try_substitute_node(self, node, vname, onlyFull, inverse=False):
        if self.equals(node):
            var = self.__new_variable_node(vname)
            if inverse: var.__multiply_by_minus_one()
            self.copy(var)
            return True, True

        if onlyFull: return False, False

        # Check whether the given node is equal to a part of this node.
        if len(node.children) > 1 and node.type == self.type and len(self.children) > len(node.children):
            if node.__are_all_children_contained(self):
                self.__remove_children_of_node(node)
                var = self.__new_variable_node(vname)
                if inverse: var.__multiply_by_minus_one()
                self.children.append(var)
                return True, False

        return False, False

    # If this node is equal to a child of the given node or it is a sum which
    # has at most one term in common with the given node, substitute it by a
    # variable with given name and subtract all other terms it has not in
    # common with the given node. If negated is True, the variable node has to
    # be multiplied by -1.
    def __try_substitute_part_of_sum(self, node, vname, inverse=False):
        # The given node is no sum.
        if node.type != NodeType.SUM or len(node.children) <= 1: return False

        # TODO: Try for negative sign too.

        if self.type == NodeType.SUM:
            return self.__try_substitute_part_of_sum_in_sum(node, vname, inverse)
        return self.__try_substitute_part_of_sum_term(node, vname, inverse)

    # If this node is a sum which has at most one term in common with the given
    # node, substitute it by a variable with given name and subtract all other
    # terms it has not in common with the given node.
    def __try_substitute_part_of_sum_in_sum(self, node, vname, inverse):
        assert(self.type == NodeType.SUM)

        common = self.__get_common_children(node)
        # The sums have no terms in common.
        if len(common) == 0: return False

        for c in common: self.children.remove(c)
        self.children.append(self.__new_variable_node(vname))
        if inverse: self.children[-1].__multiply_by_minus_one()

        for c in node.children:
            found = False
            for c2 in common:
                if c.equals(c2):
                    common.remove(c2)
                    found = True
                    break

            # If this node does not have the term, we have to subtract it.
            if not found:
                n = c.get_copy()
                n.__multiply_by_minus_one()
                self.children.append(n)

        return True

    # Returns a list of common children of this node and the given one.
    def __get_common_children(self, other):
        assert(other.type == self.type)

        common = []
        oIndices = list(range(len(other.children)))
        for child in self.children:
            for i in oIndices:
                if child.equals(other.children[i]):
                    oIndices.remove(i)
                    common.append(child)
                    break

        return common

    # If this node is equal to a child of the given node, substitute it by a
    # variable with given name and subtract all other terms.
    def __try_substitute_part_of_sum_term(self, node, vname, inverse):
        assert(self.type != NodeType.SUM)

        if not node.__has_child(self): return False

        var = self.__new_variable_node(vname)
        if inverse: var.__multiply_by_minus_one()
        sumNode = self.__new_node_with_children(NodeType.SUM, [var])

        found = False
        for c in node.children:
            if not found and self.equals(c):
                found = True
                continue

            n = c.get_copy()
            n.__multiply_by_minus_one()
            sumNode.children.append(n)

        self.copy(sumNode)
        return True


    # Returns the number of nodes with a type included in the given list.
    def count_nodes(self, typeList=None):
        cnt = 0
        for child in self.children: cnt += child.count_nodes(typeList)

        if typeList == None or self.type in typeList: cnt += 1
        return cnt

    # Returns the MBA alternation of this node, assuming that it represents a
    # linear MBA. That is, arithmetic operations may not occur in bitwise ones.
    def compute_alternation_linear(self, hasParent=False):
        if self.type in [NodeType.SUM, NodeType.PRODUCT]:
            assert(len(self.children) > 0)
            cnt = 0
            for child in self.children: cnt += child.compute_alternation_linear(True)
            return cnt

        # A bitwise operation contributes zero if it is not part of an
        # arithmetic operation.
        if not hasParent: return 0

        # Every other type than a variable and a constant occuring in a linear
        # MBA would now increase the alternation.
        return int(self.type != NodeType.VARIABLE and self.type != NodeType.CONSTANT)

    # Returns the MBA alternation of this node, i.e., the number of arithmetic
    # operations within bitwise operations and vice versa. The node has a
    # bitwise operation as a parent if parentBitwise is true, an arithmetic
    # operation if it is false and no parent if it is None.
    def compute_alternation(self, parentBitwise=None):
        if self.type == NodeType.VARIABLE: return 0
        if self.type == NodeType.CONSTANT: return int(parentBitwise != None and parentBitwise == True)

        bitw = self.__is_bitwise_op()
        cnt = int(parentBitwise != None and parentBitwise != bitw)
        for child in self.children: cnt += child.compute_alternation(bitw)
        return cnt


    # Polish this node for a nice final view, assuming that no further
    # refinement or simplification will be performed.
    def polish(self, parent=None):
        for c in self.children: c.polish(self)

        # Start (and end) with ordering for standardization in the steps in
        # between.
        self.__reorder_variables()
        self.__resolve_bitwise_negations_in_sums()
        self.__insert_bitwise_negations(parent)
        self.__reorder_variables()


    # If this node is a sum, first transform all its bitwise negations into
    # arithmetic form. Then try to split the sum's constant term, if present,
    # to arithmetically negated terms.
    def __resolve_bitwise_negations_in_sums(self):
        if self.type != NodeType.SUM: return

        # First rewrite all negations.
        count = 0
        for i in range(len(self.children)):
            if self.children[i].type != NodeType.NEGATION: continue

            self.children[i] = self.children[i].children[0]
            self.children[i].__multiply_by_minus_one()
            count += 1

        if count != 0:
            # Adapt the constant term.
            if self.children[0].type == NodeType.CONSTANT:
                self.children[0].__set_and_reduce_constant(self.children[0].constant - count)
                if self.children[0].__is_constant(0): del self.children[0]
            else: self.children.insert(0, self.__new_constant_node(-count))

        # If we have a constant term, check whether we can distribute it to
        # terms via negation.
        if self.children[0].type != NodeType.CONSTANT: return

        negConst = (-self.children[0].constant) % self.__modulus
        if len(self.children) < negConst: return

        countM = self.__count_children_mult_by_minus_one()
        # We cannot distribute the whole constant.
        if countM < negConst: return

        todo = negConst
        # Insert bitwise negations.
        for i in range(len(self.children)):
            child = self.children[i]

            # We are done:
            if todo == 0: break
            if child.type != NodeType.PRODUCT: continue
            if not child.children[0].__is_constant(-1): continue

            # Remove factor -1
            del child.children[0]

            assert(len(child.children) > 0)
            if len(child.children) == 1: child.type = NodeType.NEGATION
            else: self.children[i] = self.__new_node_with_children(NodeType.NEGATION, [child.__get_shallow_copy()])
            todo -= 1

        assert(todo == 0)

        # Finally remove the constant.
        del self.children[0]

    # Returns the number of this node's children that are multiplied by -1.
    def __count_children_mult_by_minus_one(self):
        count = 0
        for child in self.children:
            if child.type != NodeType.PRODUCT: continue
            if child.children[0].__is_constant(-1): count += 1
        return count


    # If this node is a bitwise negation transformed into an arithmetic form,
    # transform it into a bitwise negation.
    def __insert_bitwise_negations(self, parent):
        child, factor = self.__get_opt_transformed_negated_with_factor()
        assert((child != None) == (factor != None))

        # This node is no transformed negation with a factor.
        if child == None: return

        self.type = NodeType.NEGATION
        self.children = [child]

        if factor == 1: return

        if parent != None and parent.type == NodeType.PRODUCT: parent.__multiply(factor)
        else: self.__multiply(factor)

    # If this node has the form "c + c*x" for any constant c, returns x and -c.
    # Otherwise returns None, None.
    def __get_opt_transformed_negated_with_factor(self):
        if self.type != NodeType.SUM: return None, None

        # Should not happen, but be sure.
        if len(self.children) < 2: return None, None

        # First check for constant term.
        if self.children[0].type != NodeType.CONSTANT: return None, None

        # The constant factor.
        factor = self.children[0].constant

        # A node to store the result in case we have more terms.
        res = self.__new_node(NodeType.SUM)

        # Now collect the remaining terms. Stop if we encounter a term without
        # a factor divisibly by factor.
        for i in range(1, len(self.children)):
            res.children.append(self.children[i].get_copy())
            child = res.children[-1]

            # If the factor is 1, nothing more to do.
            if (factor - 1) % self.__modulus == 0: continue

            # If the factor is -1, multiply the child by -1.
            if (factor + 1) % self.__modulus == 0:
                child.__multiply_by_minus_one()
                continue

            # Otherwise we need a factor that is divisible by factor.
            if child.type != NodeType.PRODUCT: return None, None
            if child.children[0].type != NodeType.CONSTANT: return None, None

            constNode = child.children[0]
            c = self.__get_reduced_constant_closer_to_zero(constNode.constant)

            # We cannot divide the constant factor by factor.
            if c % factor != 0: return None, None

            constNode.__set_and_reduce_constant(c // factor)
            if constNode.__is_constant(1):
                del res.children[-1].children[0]
                if len(child.children) == 1: res.children[-1] = child.children[0]

        assert(len(res.children) > 0)
        if len(res.children) == 1: return res.children[0], -factor
        return res, -factor


    # Sort operands of binary operations.
    def sort(self):
        for c in self.children: c.sort()
        self.__reorder_variables()

    # In binary operations, make sure that node representing single variables
    # are at the front of the children list, potentially after a constant, and
    # sort them alphabetically.
    def __reorder_variables(self):
        if self.type < NodeType.PRODUCT: return
        if len(self.children) <= 1: return

        self.children.sort()

    # Used for sorting.
    def __lt__(self, other):
        if self.type == NodeType.CONSTANT: return True
        if other.type == NodeType.CONSTANT: return False

        vn1 = self.__get_extended_variable()
        vn2 = other.__get_extended_variable()
        if vn1 != None:
            if vn2 == None: return True
            if vn1 != vn2: return vn1 < vn2
            return self.type == NodeType.VARIABLE

        if vn2 != None: return False

        return self.type < other.type if self.type != other.type else len(self.children) < len(other.children)

    # Returns the node's variable name if it is a variable, a negated one or a
    # variable times a constant factor, or None otherwise.
    def __get_extended_variable(self):
        if self.type == NodeType.VARIABLE: return self.vname
        if self.type == NodeType.NEGATION:
            return self.children[0].vname if self.children[0].type == NodeType.VARIABLE else None
        if self.type == NodeType.PRODUCT:
            if len(self.children) == 2 and self.children[0].type == NodeType.CONSTANT and self.children[1].type == NodeType.VARIABLE:
                return self.children[1].vname
            return None

        return None


    # Verify that this node is equivalent to the given node via evaluation on
    # inputs with given bit count. Requires that all variables which occur in
    # this node also occur in other.
    def check_verify(self, other, bitCount=2):
        variables = []
        other.collect_and_enumerate_variables(variables)
        self.enumerate_variables(variables)
        vnumber = len(variables)

        def f1(X): return other.eval(X)
        def f2(X): return self.eval(X)

        mask = 2**bitCount - 1
        total = 2**(vnumber * bitCount)
        currJ = -1

        for i in range(total):
            n = i
            par = []
            for j in range(vnumber):
                par.append(n & mask)
                n = n >> bitCount

            v1 = f1(par)
            v2 = f2(par)

            if v1 != v2:
                print("\n*** ... verification failed for input " + str(par) + ": orig " + str(v1) + ", output " + str(v2))
                return False

            # Progress bar.
            j = (i + 1) / total
            if j != currJ:
                sys.stdout.write('\r')
                sys.stdout.write("*** ... verify via evaluation ... [%-20s] %d%%" % ('='*int(20*j), 100*j))
                sys.stdout.flush()

        print()
        print("*** ... verification successful!")
        return True


    # Returns the number of terms in this node which is required to be linear.
    def count_terms_linear(self):
        assert(self.is_linear())

        if self.type == NodeType.SUM:
            t = 0
            for child in self.children: t += child.count_terms_linear()
            return t

        if self.type == NodeType.PRODUCT:
            assert(len(self.children) == 2)
            if self.children[0].type == NodeType.CONSTANT: return self.children[1].count_terms_linear()
            assert(self.children[1].type == NodeType.CONSTANT)
            return self.children[0].count_terms_linear()

        return 1

    # Print information about the node.
    def print(self, level=0):
        indent = 2 * level
        prefix = indent*" " + "[" + str(level) + "] "

        if self.type == NodeType.CONSTANT:
            print(prefix + "CONST " + str(self.constant))
            return

        if self.type == NodeType.VARIABLE:
            print(prefix + "VAR " + self.vname + " [vidx " + str(self.__vidx) + "]")
            return

        print(prefix + str(self.type))
        for c in self.children: c.print(level + 1)
