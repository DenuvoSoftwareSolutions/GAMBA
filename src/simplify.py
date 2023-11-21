#!/usr/bin/python3

from enum import Enum, IntEnum
import inspect
import io
import os
import re
import sys
import traceback
try: import z3
except ModuleNotFoundError: pass
import argparse

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
sys.path.insert(0, os.path.join(currentdir, "bitwise-factory"))
from create_bitwise import BitwiseFactory
sys.path.insert(0, os.path.join(currentdir, "utils"))
from parse import parse, Node, NodeType


# An enum representing a decision metric for the comparation of possible
# solutions.
class Metric(IntEnum):
    ALTERNATION = 0,
    TERMS = 1,
    STRING = 2,
    BITWISE_NODES = 3,
    _COUNT = 4

    # Function for comparing metric types.
    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented

    # Function for comparing metric types.
    def __le__(self, other):
        if self.__class__ is other.__class__:
            return self.value <= other.value
        return NotImplemented


# Returns True iff the given expression constitutes a linear MBA for sure.
def check_linear(expr, bitCount):
    tree = parse(expr, bitCount, False, False, False)
    tree.refine()
    tree.mark_linear()
    return tree.is_linear()

# Returns the number of terms in the given expression under the assumption
# that it is linear.
def count_terms(expr):
    return expr.count('+') + expr.count('-') + int(expr[0] != '-')

# Returns a complexity penalty for the bitwise operations in the given node's
# expression.
def compute_bitwise_complexity(root):
    # TODO: More sophisticated complexity?
    return root.count_nodes([NodeType.VARIABLE, NodeType.NEGATION])


# The main simplification class which stores relevant parameters such as the
# number of variables, the modulus of the modular field as well as the vector
# of results of the target expression for combinations of truth values.
class Simplifier():
    # Initialize internals.
    def __init(self, bitCount, expr, modRed, refine, verifBitCount, metric):
        self.__origExpr = expr
        self.__groupsizes = [1]
        self.__bitCount = bitCount
        self.__modulus = 2**bitCount
        self.__modRed = modRed
        self.__refine = refine
        self.__verifBitCount = verifBitCount
        self.__metric = metric
        self.__variables = []
        self.__tree = parse(expr, bitCount, modRed, False, False)
        self.__vnumber = 0
        self.__bitwiseFactory = None
        self.__resultVector = []
        self.__res = None
        self.__compl = None
        self.__lincombTerms = None
        self.valid = self.__tree != None

        if self.valid:
            self.__collect_and_enumerate_variables()
            self.__init_groupsizes()
            self.__init_result_vector()

    # Constructor which initiates the initialization.
    def __init__(self, bitCount, expr, modRed=False, refine=True,
                 verifBitCount=None, metric=Metric.ALTERNATION):
        self.__init(bitCount, expr, modRed, refine, verifBitCount, metric)

    # Get the internal name of the variable with given index.
    def __get_tmp_vname(self, i):
        return "X[" + str(i) + "]"

    # Reduces the given number modulo modulus.
    def __mod_red(self, n):
        return n % self.__modulus

    # Returns the number of terms in the given expression.
    def get_term_count(self, expr):
        return expr.count('+') + expr.count('-') - int(expr[0] == '-') + 1

    # Returns a constant equivalent to the given one and ready for use in the
    # output expression. If modRed is True, the return value lies between 0 and
    # the modulus; otherwise the returned value is a close as possible to 0.
    def __prepare_constant(self, n):
        n = self.__mod_red(n)
        if self.__modRed: return n
        if n > self.__modulus // 2: return n - self.__modulus
        return n

    # Find all variables included in the stored original expression, store them
    # in a list and enumerate the tree's variable nodes accordingly.
    def __collect_and_enumerate_variables(self):
        self.__variables = []
        # Get a list of unique variables.
        self.__tree.collect_and_enumerate_variables(self.__variables)
        self.__vnumber = len(self.__variables)
        self.__bitwiseFactory = BitwiseFactory(self.__vnumber, self.__variables)

    # Initialize the group sizes of the various variables, i.e., their numbers
    # of subsequent occurences in the truth table.
    def __init_groupsizes(self):
        for i in range(1, self.__vnumber):
            self.__groupsizes.append(2 * self.__groupsizes[-1])

    # Initialize the vector storing results of expression evaluation for all
    # truth value combinations, i.e., [e(0,0,...), e(1,0,...), e(0,1,...),
    # e(1,1,...)].
    def __init_result_vector(self):
        def f(X): return self.__tree.eval(X)

        self.__resultVector = []
        for i in range(2**self.__vnumber):
            n = i
            par = []
            for j in range(self.__vnumber):
                par.append(n & 1)
                n = n >> 1
            self.__resultVector.append(f(par))


    # Returns a complexity penalty for the given expression, depending on the
    # occuring bitwise operations.
    def __compute_bitwise_complexity(self, expr):
        node = parse(expr, self.__bitCount, self.__modRed, False, False)
        return compute_bitwise_complexity(node)

    # Returns the MBA alternation of the given linear MBA.
    def __compute_alternation_linear(self, expr):
        node = parse(expr, self.__bitCount, self.__modRed, False, False)
        return node.compute_alternation_linear()

    # Returns the metric of given type for the given linear MBA with the term
    # count optionally given.
    def __compute_metric(self, e, metric, t=None):
        if metric == Metric.ALTERNATION: return self.__compute_alternation_linear(e)
        if metric == Metric.TERMS: return t if t != None else count_terms(e)
        if metric == Metric.STRING: return len(e)
        assert(metric == Metric.BITWISE_NODES)
        return self.__compute_bitwise_complexity(e)

    # Check whether the given solution is less complex than the currently
    # optimal known one. If so or if there is not yet any solution known, store
    # its computed complexity values. The term count is optionally given. If a
    # constant is given, this constant has to be added tot he expression and
    # the given term count has to be incremented by one accordingly.
    def __check_solution_complexity(self, e, t=None, constant=None):
        assert((self.__res == None) == (self.__compl == None))

        if constant != None:
            e = self.__add_constant(e, constant)
            if t != None: t += 1

        # No known solution yet.
        if self.__res == None:
            self.__res = e
            self.__compl = [None for i in range(int(self.__metric), int(Metric._COUNT))]
            if t != None and self.__metric <= Metric.TERMS:
                self.__compl[int(Metric.TERMS) - int(self.__metric)] = t
            return

        compl = [None for i in range(int(self.__metric), int(Metric._COUNT))]
        for m in range(int(Metric._COUNT) - int(self.__metric)):
            metric = Metric(int(self.__metric) + m)

            compl[m] = self.__compute_metric(e, metric, t)
            # If the optimal known result's metric value has not yet been
            # computed, compute it.
            if self.__compl[m] == None: self.__compl[m] = self.__compute_metric(self.__res, metric)

            # The solution has higher complexity than the optimal known one.
            # Reject it.
            if compl[m] > self.__compl[m]: return

            # The solution has lower complexity than the optimal known one.
            # Store it as the new best candidate.
            if compl[m] < self.__compl[m]:
                self.__res = e
                self.__compl = compl
                return

    # Returns the term count of the current optimal known solution. Requires
    # that a solution is known and its term count is already stored.
    def __get_term_count_of_current_solution(self):
        m = int(Metric.TERMS) - int(self.__metric)
        assert(m >= 0)

        assert(self.__compl != None)
        assert(self.__compl[m] != None)
        return self.__compl[m]


    # For the used vector of truth values, returns the corresponding bitwise
    # expression after subtracting the given offset. That is, returns the truth
    # table entry for a truth value vector which has zeros exactly in the
    # positions where the given vector contains the given offset.
    def __get_bitwise_expression(self, offset=0):
        return self.__bitwiseFactory.create_bitwise(self.__resultVector, offset)

    # For the given vector of truth values, returns the corresponding bitwise
    # expression after subtracting the given offset.
    def __get_bitwise_for_vector(self, vector, offset=0):
        return self.__bitwiseFactory.create_bitwise(vector, False, offset)

    # For the given vector of truth values, returns the negation of the
    # corresponding bitwise expression.
    def __get_negated_bitwise_for_vector(self, vector):
        return self.__bitwiseFactory.create_bitwise(vector, True)


    # Returns true iff a is the sum of s1 and s2 in the modular field.
    def __is_sum_modulo(self, s1, s2, a):
        return s1 + s2 == a or s1 + s2 == a + self.__modulus

    # Returns true iff a is double b in the modular field.
    def __is_double_modulo(self, a, b):
        return 2 * b == a or 2 * b == a + self.__modulus


    # Returns the given bitwise expressions times the given coefficients.
    # Appends a '+' if the final coefficient will be positive and first is
    # False.
    def __term(self, bitwise, coeff, first):
        coeff = self.__prepare_constant(coeff)
        term = ""

        if not first or coeff < 0:
            term += '+' if coeff >= 0 else '-'
            if coeff < 0: coeff = -coeff

        if coeff != 1: term += str(coeff) + '*'
        term += bitwise

        return term

    # Returns the linear combination of the given bitwise expressions with
    # given coefficients.
    def __compose(self, bitwises, coeffs):
        assert(len(bitwises) > 0)
        assert(len(bitwises) == len(coeffs))

        simpl = ""

        for i in range(len(bitwises)):
            simpl += self.__term(bitwises[i], coeffs[i], i == 0)

        return simpl

    # Returns a simple bitwise expression corresponding to the positions where
    # the vector of results for truth value combinations has a value of r1 or
    # rAlt to the given expression.
    def __term_refinement(self, r1, first, rAlt=None):
        t = []
        for r2 in self.__resultVector:
            t.append(int(r2 == r1 or (rAlt is not None and r2 == rAlt)))

        bitwise = self.__get_bitwise_for_vector(t)
        return self.__term(bitwise, r1, first)

    # Build an expression by summing up bitwise expressions, each corresponding
    # to a value in the lookup table and multiplied by this value thereafter.
    def __expression_for_each_unique_value(self, resultSet):
        expr = ""
        first = True
        for r in resultSet:
            if r != 0:
                expr += self.__term_refinement(r, first)
                first = False

        # If we only have 1 term, get rid of parentheses, if present.
        if len(resultSet) == 1 and expr[0] == '(' and expr[-1] == ')':
            expr = expr[1:-1]

        return expr

    # For the given set of results of the input expression for combinations of
    # truth values, try to find a single negated expression representing the
    # result vector.
    def __try_find_negated_single_expression(self, resultSet):
        # We can only find a negated expression if we have 2 distinct values.
        assert(len(resultSet) == 2)

        # Check whether we have a bitwise negation of a term in the lookup table.
        # This is the only chance for reducing the expression to one term.

        s = resultSet.copy()
        a = s.pop()
        b = s.pop()
        aDouble = self.__is_double_modulo(a, b)
        bDouble = self.__is_double_modulo(b, a)
        if not aDouble and not bDouble: return

        # Make sure that b is double a.
        if aDouble: a, b = b, a

        if self.__resultVector[0] == b: return

        t = [int(r == b) for r in self.__resultVector]
        e = self.__get_negated_bitwise_for_vector(t)

        e = self.__term(e, -a, True)
        if e[0] == '(' and e[-1] == ')': e = e[1:-1]

        self.__check_solution_complexity(e, 1)

    # For the given unique values appearing in the simplifier's result vector,
    # possibly, after subtraction of a constant, try to express one of them as
    # sum of others in order to find a combination of fewer simple bitwise
    # expressions.
    def __try_eliminate_unique_value(self, uniqueValues, constant=None):
        l = len(uniqueValues)
        # NOTE: Would be possible also for higher l, implementation is generic.
        if l > 4: return ""

        # Try to get rid of a value by representing it as a sum of the others.
        for i in range(l - 1):
            for j in range(i + 1, l):
                for k in range(l):
                    if k == i or k == j: continue

                    if self.__is_sum_modulo(uniqueValues[i], uniqueValues[j], uniqueValues[k]):
                        simpler = ""
                        for i1 in [i, j]:
                            simpler += self.__term_refinement(uniqueValues[i1], i1 == i, uniqueValues[k])

                        if l > 3:
                            resultSet = set(uniqueValues)
                            resultSet.discard(uniqueValues[i])
                            resultSet.discard(uniqueValues[j])
                            resultSet.discard(uniqueValues[k])

                            while len(resultSet) > 0:
                                r1 = resultSet.pop()
                                simpler += self.__term_refinement(r1, False)

                        self.__check_solution_complexity(simpler, l - 1, constant)
                        return

        if l < 4: return 

        # Finally, if we have more than 3 values, try to express one of them as
        # a sum of all others.
        for i in range(l):
            if not 2 * uniqueValues[i] == sum(uniqueValues): continue

            simpler = ""
            first = True
            for j in range(l):
                if i == j: continue

                simpler += self.__term_refinement(uniqueValues[j], first, uniqueValues[i])
                first = False

            self.__check_solution_complexity(simpler, l - 1, constant)
            return

    # Subtract the result vector's first entry from the others and return it.
    def __reduce_by_constant(self):
        constant = self.__resultVector[0]
        if constant != 0:
            for i in range(len(self.__resultVector)):
                self.__resultVector[i] -= constant
                self.__resultVector[i] = self.__mod_red(self.__resultVector[i])

        return constant


    # For the stored list of results of the input expression for combinations
    # of truth values, try to find two unnegated expressions representing the
    # result vector.
    def __find_two_expressions_by_two_values(self):
        assert(self.__resultVector[0] == 0)
        resultSet = set(self.__resultVector)
        assert(len(resultSet) == 3)

        resultSet.remove(0)
        assert(len(resultSet) == 2)

        a = resultSet.pop()
        b = resultSet.pop()

        # We have three possible solutions. Return that with lowest complexity.
        self.__determine_comb_of_two(a, b)
        self.__determine_comb_of_two((a - b) % self.__modulus, b)
        self.__determine_comb_of_two(a, (b - a) % self.__modulus)


    # An enum representing a decision on whether an entry in the result vector
    # represents a negated or an unnegated bitwise expression, none or both.
    class Decision(Enum):
        NONE = 0,
        FIRST = 1,
        SECOND = 2,
        BOTH = 3

    # Returns a vector of decitions for each entry in the result vector.
    def __get_decision_vector(self, coeff1, coeff2, vec):
        if vec == None: vec = self.__resultVector

        d = []
        for r in vec:
            e = []
            f = (r - coeff1) % self.__modulus == 0
            s = (r - coeff2) % self.__modulus == 0
            b = (r - coeff1 - coeff2) % self.__modulus == 0
            # For more variables, this would take too long.
            if r == 0 and self.__vnumber > 4: b = False
            # Same.
            if f and s and self.__vnumber > 4: s = False

            if r % self.__modulus == 0: e.append(self.Decision.NONE)
            if b:                       e.append(self.Decision.BOTH)
            if f:                       e.append(self.Decision.FIRST)
            if s:                       e.append(self.Decision.SECOND)

            assert(len(e) > 0)
            d.append(e)

        return d

    # Returns true iff at least one entry in the given list is a list with more
    # than one entry.
    def __must_split(self, d):
        for e in d:
            assert(len(e) > 0)
            if len(e) > 1: return True
        return False

    # Splits the given list of lists at the first entry which has more than one
    # entry.
    def __split(self, d):
        sec = []
        split = False

        for e in d:
            assert(len(e) > 0)
            # Splitting has already happened.
            if split:
                sec.append(list(e))
                continue

            # Split at this entry.
            if len(e) > 1:
                split = True
                sec.append([e.pop()])
                continue

            sec.append(list(e))

        assert(split)
        return [d, sec]

    # Returns a linear combination of two bitwise expressions with given
    # coefficients and given result vector for the given case. The second
    # bitwise expression is negated iff secNegated is True. In that case the
    # negated coefficient is already subtracted from the vector.
    def __determine_comb_of_two_for_case(self, coeff1, coeff2, case, secNegated):
        l = [int(c == [self.Decision.FIRST] or c == [self.Decision.BOTH]) for c in case]
        first = self.__get_bitwise_for_vector(l)

        l = [int(c == [self.Decision.SECOND] or c == [self.Decision.BOTH]) for c in case]
        second = self.__get_negated_bitwise_for_vector(l) if secNegated else self.__get_bitwise_for_vector(l)

        e = self.__compose([first, second], [coeff1, -coeff2 if secNegated else coeff2])
        self.__check_solution_complexity(e, 2)

    # Returns a linear combination of two bitwise expressions with given
    # coefficients and given result vector. The second bitwise expression is
    # negated iff secNegated is True. In that case the negated coefficient is
    # already subtracted from the vector.
    def __determine_comb_of_two(self, coeff1, coeff2, vec=None, secNegated=False):
        d = self.__get_decision_vector(coeff1, coeff2, vec)
        cases = [d]

        res = ""
        resCompl = None

        while len(cases) > 0:
            case = cases.pop()
            if self.__must_split(case):
                cases += self.__split(case)
                continue

            self.__determine_comb_of_two_for_case(coeff1, coeff2, case, secNegated)

    # For the stored list of results of the input expression for combinations
    # of truth values, try to find a negated and an unnegated expression
    # representing the result vector.
    def __try_find_negated_and_unnegated_expression(self):
        # TODO: We can still try to find a solution with 2 terms if we already
        # have one with one term, and then compare complexities.
        if len(set(self.__resultVector)) not in [3, 4]: return

        negCoeff = self.__resultVector[0]
        assert(negCoeff != 0)
        vec = [(a - negCoeff) % self.__modulus for a in self.__resultVector]
        assert(vec[0] == 0)

        uniqueValues = [r for r in set(vec) if r != 0 and r != negCoeff]
        assert(len(uniqueValues) >= 1)

        # Not possible to find a combination if we still have more than two
        # unique values.
        if len(uniqueValues) > 2: return

        if len(uniqueValues) == 2:
            a = uniqueValues[0]
            b = uniqueValues[1]

            # Try to express one of these values as the sum of the negated
            # bitwise expression's coefficient and the other value.
            if (b - a - negCoeff) % self.__modulus != 0:
                a, b = b, a
                if (b - a - negCoeff) % self.__modulus != 0: return

            unnegCoeff = a

            self.__determine_comb_of_two(unnegCoeff, negCoeff, vec, True)
            return

        a = uniqueValues[0]
        # If we have just one unique value a left, we have one degree of
        # freedom to choose the unnegated bitwise expression's coefficient: It
        # can either be a or a reduced by the negated expression's coefficient.
        self.__determine_comb_of_two(a, negCoeff, vec, True)
        self.__determine_comb_of_two((a - negCoeff) % self.__modulus, negCoeff, vec, True)

    # For the stored list of results of the input expression for combinations
    # of truth values, try to find two negated expressions representing the
    # result vector.
    def __try_find_two_negated_expressions(self):
        # TODO: We can still try to find a solution with 2 terms if we already
        # have one with one term, and then compare complexities.
        if len(set(self.__resultVector)) not in [3, 4]: return

        coeffSum = self.__resultVector[0]
        assert(coeffSum != 0)
        vec = [(a - coeffSum) % self.__modulus for a in self.__resultVector]
        assert(vec[0] == 0)

        uniqueValues = [r for r in set(vec) if r != 0 and r != coeffSum]
        assert(len(uniqueValues) >= 1)

        # Not possible to find a combination if we still have more than two
        # unique values.
        if len(uniqueValues) > 2: return

        # This case has already been handled in
        # try_find_negated_and_unnegated_expression().
        # TODO: Handle here too and compare complexity?
        if len(uniqueValues) == 1: return

        a = uniqueValues[0]
        b = uniqueValues[1]

        # Try to express one of these values as the difference of coeffSum and
        # the other value.
        if (b + a - coeffSum) % self.__modulus != 0: return

        coeff1 = a
        l = [int(r == coeff1 or r == coeffSum) for r in vec]
        bitwise1 = self.__get_negated_bitwise_for_vector(l)

        coeff2 = b
        vec = [self.__mod_red(vec[i] - coeff1 * l[i]) for i in range(len(vec))]
        vec = [int(r == coeff2) for r in vec]
        bitwise2 = self.__get_negated_bitwise_for_vector(vec)

        e = self.__compose([bitwise1, bitwise2], [-coeff1, -coeff2])
        self.__check_solution_complexity(e, 2)

    # Add a given constant to the given expression.
    def __add_constant(self, expr, constant):
        if constant == 0: return expr

        if self.__is_bitwise_with_binop(expr): expr = '(' + expr + ')'

        constant = self.__prepare_constant(constant)
        prefix = str(constant)
        if expr[0] != '-': prefix += '+'

        return prefix + expr

    # Try to find a multiple of a single bitwise expression corresponding to
    # the stored result vector and the corresponding given set of its values.
    def __try_refine_single_term(self, resultSet):
        l = len(resultSet)
        assert(l > 1)

        # We cannot come down to a single expression in this case.
        if l > 2: return

        # NOTE: The case (1) that we only have one unique value has already
        # been handled in simplify_one_value().
        
        # (2) If only one nonzero value occurs and the result for all variables
        # being zero is zero, we can find a single expression.
        if self.__resultVector[0] == 0:
            e = self.__expression_for_each_unique_value(resultSet)
            if e[0] == '(' and e[-1] == ')': e = e[1:-1]
            self.__check_solution_complexity(e, 1)

        # (3) Check whether we can find one single negated term.
        self.__try_find_negated_single_expression(resultSet)

    # Try to find a linear combination of two bitwise expressions corresponding
    # to the stored result vector and the corresponding given set of its
    # values, given that the result vector's first entry is 0.
    def __try_refine_two_terms_first_zero(self, resultSet):
        assert(self.__resultVector[0] == 0)
        l = len(resultSet)

        # In the case l==2 we know that the constant is nonzero since we would
        # have run into the case (2) otherwise.
        # TODO: We can still try to find a solution with 2 terms if we already
        # have one with one term, and then compare complexities.

        if l == 3:
            # (4) We can reduce the expression to two terms.
            self.__find_two_expressions_by_two_values()

        elif l == 4:
            # (5) We can still come down to 2 expressions if we can express one
            # value as a sum of the others.
            uniqueValues = [r for r in set(self.__resultVector) if r != 0]
            self.__try_eliminate_unique_value(uniqueValues)

    # Try to find a linear combination of two bitwise expressions corresponding
    # to the stored result vector and the corresponding given set of its
    # values, given that the result vector's first entry is not 0.
    def __try_refine_two_terms_first_nonzero(self, resultSet):
        assert(self.__resultVector[0] != 0)
        l = len(resultSet)

        resultVector = list(self.__resultVector)

        if l == 2:
            # (6) In this case we know that the constant is nonzero since we
            # would have run into the case (2) otherwise.
            constant = self.__reduce_by_constant()
            e = self.__expression_for_each_unique_value(set(self.__resultVector))
            e = self.__add_constant(e, constant)
            self.__check_solution_complexity(e, 2)

            # Restore the result vector since it has been modified above.
            self.__resultVector = list(resultVector)

        if l <= 4:
            # (7) Try to express the expression as the linear combination of a
            # negated and an unnegated bitwise expression.
            self.__try_find_negated_and_unnegated_expression()

            # (8) Try to express the expression as the linear combination of
            # two negated bitwise expressions.
            self.__try_find_two_negated_expressions()

    # Try to find a linear combination of two bitwise expressions corresponding
    # to the stored result vector and the corresponding given set of its values.
    def __try_refine_two_terms(self, resultSet):
        if self.__resultVector[0] == 0:
            self.__try_refine_two_terms_first_zero(resultSet)
        else:
            self.__try_refine_two_terms_first_nonzero(resultSet)

    # Returns True iff the term count metric is used and therer is already a
    # solution with at most the given term count known.
    def __check_term_count(self, value):
        if self.__lincombTerms <= value: return True
        if self.__metric != Metric.TERMS: return False
        return self.__get_term_count_of_current_solution() <= value

    # For the given expression, check whether the number of its terms can be
    # decreased by finding suitable combinations of simple expressions in a
    # lookup table. Currently only tries to simplify to at most 3 terms.
    # NOTE: Could be extended to more terms for 3 variables.
    def __try_refine(self):
        assert(self.__lincombTerms != None)

        # Rebuild the result vector since it has been modified during
        # simplification.
        self.__init_result_vector()

        # The number of terms in the linear combination of conjunctions only
        # has one term.
        if self.__check_term_count(1): return

        resultSet = set(self.__resultVector)
        l = len(resultSet)
        assert(l > 1)

        # We try to find a solution that is simpler than the linear combination.
        # In this course we perform several attempts, numbered according to the
        # paper.

        # (1-3) Try to find a single term that fits.
        self.__try_refine_single_term(resultSet)

        # We cannot simplify the expression better.
        if self.__check_term_count(2): return

        # (4-8) Try to find a sum of two terms that fits.
        self.__try_refine_two_terms(resultSet)

        # We cannot simplify the expression better.
        if self.__check_term_count(3): return

        # (9) Try to reduce the number of unique values by expressing one as a
        # combination of the others.
        constant = self.__reduce_by_constant()
        uniqueValues = [r for r in set(self.__resultVector) if r != 0]
        self.__try_eliminate_unique_value(uniqueValues, constant)

        c = len(uniqueValues) + int(constant != 0)
        if self.__check_term_count(c): return

        # (10) Find expressions corresponding to the unique values.
        simpler = self.__expression_for_each_unique_value(uniqueValues)
        simpler = self.__add_constant(simpler, constant)
        self.__check_solution_complexity(simpler, c)


    # Returns a trivial expression constituted by only one constant which is
    # the only element of the given set.
    def __simplify_one_value(self, resultSet):
        coefficient = resultSet.pop()
        e = str(self.__prepare_constant(coefficient))
        # This is of course the optimal solution, but still use the existing
        # infrastructure.
        self.__check_solution_complexity(e, 1)

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

    # Returns the conjunction of all variables included in the given list to the
    # given expression if the given coefficient is nonzero and multiply it with
    # that coefficient.
    def __conjunction(self, coeff, variables, first):
        assert(len(variables) > 0)
        if coeff == 0: return ""

        conj = ""
        # If we have a nontrivial conjunction, we need parentheses.
        if len(variables) > 1: conj += "("

        for v in variables:
            conj += self.__variables[v] + "&"

        # Get rid of last '&'.
        conj = conj[:-1]
        if len(variables) > 1: conj += ")"
        return self.__term(conj, coeff, first)

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
    def __subtract_coefficient(self, coeff, firstStart, variables):
        groupsize1 = self.__groupsizes[variables[0]]
        period1 = 2 * groupsize1
        for start in range(firstStart, len(self.__resultVector), period1):
            for i in range(start, start + groupsize1):
                # The first variable is true by design of the for loops.
                if i != firstStart and (len(variables) == 1 or self.__are_variables_true(i, variables[1:])):
                    self.__resultVector[i] -= coeff

    # For the given vector of results for the combinations of truth values for
    # variables, and for the used number t of variables, determine a linear
    # combination of the 2^t base bitwise expressions.
    def __simplify_generic(self):
        l = len(self.__resultVector)
        expr = ""
        term_count = 0

        # The constant term.
        constant = self.__prepare_constant(self.__resultVector[0])
        for i in range(1, l):
            self.__resultVector[i] -= constant

        first = True
        if constant != 0:
            expr += str(constant)
            term_count += 1
            first = False

        # Append all conjunctions of variables (including trivial conjunctions
        # of single variables) if their coefficients are nonzero.
        combinations = self.__get_variable_combinations()
        for comb in combinations:
            index = sum([self.__groupsizes[v] for v in comb])
            coeff = self.__prepare_constant(self.__resultVector[index])

            if coeff == 0: continue

            self.__subtract_coefficient(coeff, index, comb)
            expr += self.__conjunction(coeff, comb, first)
            term_count += 1
            first = False

        if expr == "": expr = "0"
        elif expr[0] == '(' and expr[-1] == ')' and term_count == 1: expr = expr[1:-1]

        # This should be the first computed solution, but still use the
        # existing infrastructure.
        self.__check_solution_complexity(expr, term_count)
        self.__lincombTerms = term_count

    # For the optimal currently known solution, check how many variables it
    # uses effectively. If it is not more than 3, run the simplification
    # procedure again for that variable count since we might be able to
    # simplify the expression using truth tables.
    def __try_simplify_fewer_variables(self):
        assert(self.__res != None)

        # Collect the variables in the result.
        occuring = []
        t = parse(self.__res, self.__bitCount, self.__modRed, False, False)
        t.collect_and_enumerate_variables(occuring)

        vnumber = len(occuring)
        # No function available for more than 3.
        if vnumber > 3: return False

        # Exchange the variables by temporary ones.
        tmpVars = [self.__get_tmp_vname(i) for i in range(vnumber)]
        expr = t.to_string(False, -1, tmpVars)

        innerSimplifier = Simplifier(self.__bitCount, expr, self.__modRed, self.__refine, self.__metric)
        expr = innerSimplifier.__simplify(False)

        # Back-replace the variables.
        t = parse(expr, self.__bitCount, self.__modRed, False, False)
        t.enumerate_variables(tmpVars)
        expr = t.to_string(False, -1, occuring)

        self.__check_solution_complexity(expr)
        return True

    # Split the given expression into terms, '+' and '-'.
    def __split_into_terms(self, expr):
        l = re.split("([\+-])", expr)
        # The first element is empty if the expression starts with a '-'.
        if len(l[0]) == 0: l = l[1:]

        # If it does not start with a '-', we add a '+'.
        if l[0] != '-': l.insert(0, '+')

        return l

    # Create a list of lists of the variables in the given list of terms.
    def __find_variables_in_terms(self, l):
        v = []
        for e in l:
            v.append(set([]))

            if e == '+' or e == '-': continue

            # Store the term's variables in v's last element we have added
            # above.
            node = parse(e, self.__bitCount, self.__modRed, False, False)
            variables = []
            node.collect_and_enumerate_variables(variables)
            v[-1] = set(variables)

        return v

    # Partition the terms of the given list depending on the numbers of their
    # variables. Returns the index of a constant (only one can exist; -1 if
    # none exists), lists of indices of terms with 1, 2, 3 or more than 4
    # variables.
    def __partition_terms_wrt_variable_count(self, l, v):
        # Constant (should be at most one).
        constIdx = -1
        # Terms with 1 variable.
        l1 = []
        # Terms with 2 variables.
        l2 = []
        # Terms with 3 variables.
        l3 = []
        # Terms with at least 4 variables.
        lrem = []

        for i in range(len(v)):
            lv = len(v[i])
            if lv == 0:
                if l[i] != '+' and l[i] != '-':
                    assert(constIdx == -1)
                    constIdx = i
                continue
            elif lv == 1: l1.append(i)
            elif lv == 2: l2.append(i)
            elif lv == 3: l3.append(i)
            else: lrem.append(i)

        return constIdx, l1, l2, l3, lrem

    # Try to find an entry in the given partition of variables containing the
    # given set of variables.
    def __try_find_matching_partition(self, i, variables, partitionV, partitionT):
        assert(len(partitionV) == len(partitionT))

        for j in range(len(partitionV)):
            # The variable set matches the part.
            if len(variables - partitionV[j]) == 0:
                partitionT[j].append(i)
                return True

        return False

    # Returns all indices of entries in the given partition having a nonempty
    # intersection with the given set of variables. Additionally returns False
    # iff there is at least one intersection with more than 3 variables.
    def __determine_intersections(self, variables, partitionV):
        intersections = []
        valid = True

        for j in range(len(partitionV)):
            part = partitionV[j]

            # The variable set has an empty intersection with the part.
            if len(variables & part) == 0: continue

            # The variable set has a nonempty intersection with the part,
            # but does not match it. Check whether we can merge it into the
            # part. If not, reject it.

            intersections.append(j)

            if valid and (len(intersections) > 0 or len(variables | part) > 3):
                valid = False

        return intersections, valid

    # Partition the variables of the given list and the terms of the given list
    # correspondingly such that all terms with indices in an entry of the term
    # partition only use variables of the corresponding part of the variable
    # partition. If the terms cannot perfectly be split, the indices of term
    # that cannot be distributed to the partition are stored in the list of
    # remaining term indices.
    def __partition(self, v, l1, l2, l3, lrem):
        partitionV = []
        partitionT = []
        remV = set([])

        # Initialize the list of variables we cannot split.
        for i in lrem: remV.update(v[i])

        l23 = l2 + l3
        for i in l23:
            # The variable set has a nonempty intersection with the variables
            # we cannot split, so merge them.
            if len(v[i] & remV) > 0:
                remV.update(v[i])
                lrem.append(i)
                continue

            # Now check whether the term matches any partitions' part, if
            # existent.
            if self.__try_find_matching_partition(i, v[i], partitionV, partitionT):
                continue

            # If the term does not match any, check whether it violates any. If
            # so, reject it.
            intersections, valid = self.__determine_intersections(v[i], partitionV)

            # Create a new part.
            if len(intersections) == 0:
                partitionV.append(v[i])
                partitionT.append([i])

            # We can merge the variable set into an existing one.
            elif len(intersections) == 1:
                partitionV[intersections[0]].update(v[i])
                partitionT[intersections[0]].append(i)

            # We have a conflict.
            else:
                remV.update(v[i])
                lrem.append(i)

                for j in reversed(intersections):
                    remV.update(partitionV[j])
                    lrem += partitionT[j]

                    del partitionV[j]
                    del partitionT[j]

        # Now check for each term with 1 variable whether it matches any
        # partitions' part, if existent. Note that it cannot violate any.
        for i in l1:
            var = v[i].pop()

            # Variable is already known not to be able to split.
            if var in remV:
                lrem.append(i)
                continue

            done = False

            for j in range(len(partitionV)):
                part = partitionV[j]

                # The variable is included in the part.
                if var in part:
                    partitionT[j].append(i)
                    done = True
                    break

            # The variable is not included in any part. Add a part for it.
            if not done:
                partitionV.append(set([var]))
                partitionT.append([i])

        return partitionT

    # Returns a sum of the given list's entries with indices contained in the
    # given list, each preceded by a sign which is the preceding entry in the
    # list. Includes a leading sign as a first character in all cases if
    # leadingSign is True.
    def __compose_terms(self, l, indices, leadingSign):
        e = ""

        for i in indices:
            assert(i > 0)
            e += l[i - 1] + l[i]

        # Remove a leading '+' if necessary.
        return e if leadingSign or e[0] == '-' else e[1:]

    # Returns true iff the given string represents a bitwise expression with at
    # least one binary operand.
    def __is_bitwise_with_binop(self, expr):
        # The expression must have at least one binary bitwise operator, but no
        # '+', '-' or '*'.
        return not bool(re.search("([\+*-])", expr)) and bool(re.search("([&|^])", expr))

    # Simplify the sum of terms in the given list for each given partition and
    # compose the results.
    def __simplify_parts_and_compose(self, l, partition, constIdx, lrem):
        simpl = ""

        # Simplify the partition's parts seperately and compose the results.
        for part in partition:
            e = self.__compose_terms(l, part, False)

            innerSimplifier = Simplifier(self.__bitCount, e, self.__modRed, self.__refine, self.__metric)
            s = innerSimplifier.__simplify(False, True)

            # Append the constant if existent and check whether the result has
            # the same number of terms. If so, use that instead and eliminate
            # the constant.
            if constIdx != -1:
                assert(constIdx > 0)
                e += l[constIdx - 1] + l[constIdx]

                innerSimplifier = Simplifier(self.__bitCount, e, self.__modRed, self.__refine, self.__metric)
                s2 = innerSimplifier.__simplify(False, True)

                if count_terms(s) == count_terms(s2):
                    s = s2
                    constIdx = -1

            assert(len(s) > 0)
            if len(s) == 0 or s == '0': continue

            # Add parentheses if necessary.
            if self.__is_bitwise_with_binop(s): s = '(' + s + ')'

            # Add a '+' if necessary to compose the results.
            if len(simpl) > 0 and s[0] != '-': simpl += '+'

            simpl += s

        # If there are no remaining terms but the constant, add the constant.
        if len(lrem) == 0:
            if constIdx != -1:
                assert(constIdx > 0)
                simpl += l[constIdx - 1] + l[constIdx]

            return simpl if len(simpl) > 0 else "0"

        # Now consider the terms which did not fit the partition, if existent.
        e = self.__compose_terms(l, lrem, False)
        # Append the constant if existent and not used yet.
        if constIdx != -1:
            assert(constIdx > 0)
            e += l[constIdx - 1] + l[constIdx]

        if len(e) > 0:
            innerSimplifier = Simplifier(self.__bitCount, e, self.__modRed, self.__refine, self.__metric)
            s = innerSimplifier.__simplify(False, True)

            if len(s) != 0 and s != '0':
                # Add parentheses if necessary.
                if self.__is_bitwise_with_binop(s): s = '(' + s + ')'

                # Add a '+' if necessary to compose the results.
                if len(simpl) > 0 and s[0] != '-': simpl += '+'

                simpl += s

        return simpl if len(simpl) > 0 else "0"

    # Try to split the given expression, which is supposed to be a linear MBA,
    # into subexpressions with at most 3 variables each such that the list of
    # occurring variables is partitioned thereby, simplify these subexpressions
    # and compose the results.
    def __try_split(self):
        expr = self.__res
        assert(expr != None)

        l = self.__split_into_terms(expr)
        v = self.__find_variables_in_terms(l)
        constIdx, l1, l2, l3, lrem = self.__partition_terms_wrt_variable_count(l, v)
        partition = self.__partition(v, l1, l2, l3, lrem)

        e = self.__simplify_parts_and_compose(l, partition, constIdx, lrem)
        self.__check_solution_complexity(e)


    # Verify that the original expression and the simplified one are equivalent
    # using Z3.
    def __verify_using_z3(self):
        orig = self.__tree.to_string()
        assert(self.__res)
        simpl = self.__res
        if simpl == orig: return True

        # In self.__tree, the variables are already enumerated. Use the same
        # order for the simplification result.
        simplTree = parse(simpl, self.__bitCount, self.__modRed, False, False)
        simplTree.enumerate_variables(self.__variables)

        tmpVars = [self.__get_tmp_vname(i) for i in range(len(self.__variables))]
        # The expressions with their variables replaced by temporary ones.
        orig = self.__tree.to_string(False, -1, tmpVars)
        simpl = simplTree.to_string(False, -1, tmpVars)

        X = [z3.BitVec(v, self.__bitCount) for v in tmpVars]

        origEval = eval("(" + orig + ") % " + str(self.__modulus))
        simplEval = eval("(" + simpl + ") % " + str(self.__modulus))

        solver = z3.Solver()
        solver.add(origEval != simplEval)
        result = solver.check()

        return str(result) == "unsat"

    # Returns the number of variables occuring in the given expression.
    def get_variable_count(self, expr):
        return self.__vnumber

    # Simplify the expression with used number of variables.
    def __simplify(self, useZ3, alreadySplit=False):
        if not self.valid:
            sys.exit("Error: Simplifier not correctly initialized!")

        assert(self.__res == None)
        assert(self.__compl == None)

        if self.__vnumber > 3:
            if alreadySplit:
                resultSet = set(self.__resultVector)
                if self.__refine and len(resultSet) == 1:
                    self.__simplify_one_value(resultSet)

                else:
                    self.__simplify_generic()
                    if self.__refine: self.__try_refine()
                    
            else:
                self.__simplify_generic()
                if not self.__try_simplify_fewer_variables():
                    self.__try_split()

        else:
            resultSet = set(self.__resultVector)
            if self.__refine and len(resultSet) == 1:
                self.__simplify_one_value(resultSet)

            else:
                self.__simplify_generic()
                if self.__refine: self.__try_refine()

        assert(self.__res != None)

        # TODO: Discuss whether to compare to input wrt. complexity.
        if False and self.__refine:
            # If the input is linear and less complex than the result, return
            # the former. Should not happen for fewer than 4 variables.
            root = parse(self.__origExpr, self.__bitCount, self.__modRed, False, False)

            if root != None:
                root.refine()
                root.mark_linear()

                if root.is_linear():
                    self.__check_solution_complexity(root.to_string())

        if useZ3 and not self.__verify_using_z3():
            sys.exit("Error in simplification! Simplified expression is not equivalent to original one!")

        return self.__res

    # Returns True iff the original expression is linear.
    def __is_input_linear(self):
        self.__tree.refine()
        self.__tree.mark_linear()
        return self.__tree.is_linear()

    # Verify the given solution via evaluation.
    def __check_verify(self, simpl):
        if self.__verifBitCount == None: return True
        if self.__is_input_linear():
            print("*** ... input is considered linear")
            return True

        print("*** ... input is not considered linear")

        simplTree = parse(simpl, self.__bitCount, self.__modRed, False, False)
        return simplTree.check_verify(self.__tree, self.__verifBitCount)


    # Simplify the expression with used number of variables.
    def simplify(self, useZ3):
        self.__res = None
        self.__compl = None

        simpl = self.__simplify(useZ3)
        return simpl if self.__check_verify(simpl) else ""


# Simplify the given expression with given number of variables. For that,
# evaluate it for all possible combinations of truth values for the variables
# and run the simplification procedure based on the resulting vector.
def simplify_linear_mba(expr, bitCount, useZ3, checkLinear=False, modRed=False,
                        refine=True, verifBitCount=None, metric=Metric.ALTERNATION):
    if checkLinear and not check_linear(expr, bitCount):
        sys.exit("Error: Input expression may be no linear MBA: " + expr)

    simplifier = Simplifier(bitCount, expr, modRed, refine, verifBitCount, metric)
    if not simplifier.valid:
        sys.exit("Error: Simplifier not correctly initialized!")

    simpl = simplifier.simplify(useZ3)
    return simpl


if __name__ == "__main__":
    parser = argparse.ArgumentParser(prog='GAMBA', description='Simplification of linear Mixed Boolean-Arithmetic Expressions', epilog='Each command line input not preceded by option indicators is considered an expression to be simplified. Expressions are read from standard input if none are given on command line.')
    parser.add_argument("-b", default=64, dest="bitCount", help="Specify the bit number of variables", type=int)
    parser.add_argument("-z", default=False, dest="useZ3", help="Enable a check for valid simplification using Z3", type=bool)
    parser.add_argument("-l", default=False, dest="checkLinear", help="Enable a check for input expressions being linear MBAs", type=bool)
    parser.add_argument("-m", default=False, dest="modRed", help="Enable a reduction of all constants modulo 2**b where b is the bit count", type=bool)
    parser.add_argument("-c", default=True, dest="refine", help="Only use conjunctions in the output, i.e., do not refine", type=bool)
    parser.add_argument("-d", choices=["ALTERNATION","TERMS","STRING","BITWISE_NODES"], default="ALTERNATION", dest="metric", help="Specify decision metric")
    parser.add_argument("-v", default=None, dest="verifyBitCount", help="Specify a bit count for verification for nonlinear input", type=int)
    parser.add_argument('exprs', nargs='*', type=str)
    args = parser.parse_args()

    if len(args.exprs) == 0:
        args.exprs.extend(sys.stdin.read().splitlines())

    metric = None
    if args.metric == "ALTERNATION":
        metric = Metric.ALTERNATION
    elif args.metric == "TERMS":
        metric = Metric.TERMS
    elif args.metric == "STRING":
        metric = Metric.STRING
    else:
        metric = Metric.BITWISE_NODES

    for expr in args.exprs:
        print("*** Expression " + expr)
        simpl = simplify_linear_mba(expr, args.bitCount, args.useZ3, args.checkLinear, args.modRed, args.refine, args.verifyBitCount, metric)
        if simpl != "": print("*** ... simplified to " + simpl)
        else: print("*** ... not simplified correctly")

    sys.exit(0)
