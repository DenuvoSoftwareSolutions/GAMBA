#!/usr/bin/python3

from enum import Enum


# The type of a node representing a bitwise (sub-)expression.
class BitwiseType(Enum):
    TRUE = 0
    VARIABLE = 1
    CONJUNCTION = 2
    EXCL_DISJUNCTION = 3
    INCL_DISJUNCTION = 4

    # Function for comparing types.
    def __lt__(self, other):
        if self.__class__ is other.__class__:
            return self.value < other.value
        return NotImplemented

# An abstract syntax tree structure representing a bitwise (sub-)expression.
# Each node has a type (constant, variable or binary operation) and is possibly
# negated. The bitwise negation is not realized via a separate node, but via a
# flag which each node is equipped with.
class Bitwise():
    # Initialize a bitwise node with given type.
    def __init__(self, bType, negated=False, vidx=-1):
        assert((vidx >= 0) == (bType == BitwiseType.VARIABLE))

        self.__type = bType
        self.__vidx = vidx
        self.__negated = negated
        self.__children = []

    # Add the given node as a child node.
    def add_child(self, child):
        self.__children.append(child)

    # Add a child node for a variable with given index.
    def add_variable(self, vidx, negated=False):
        self.add_child(Bitwise(BitwiseType.VARIABLE, negated, vidx))

    # Returns the number of children.
    def child_count(self):
        return len(self.__children)

    # Returns this node's first child.
    def first_child(self):
        return self.__children[0]

    # Returns a string representation of this node's operation. Requires that
    # this node represents a binary operation.
    def __op_to_string(self):
        assert(self.__type > BitwiseType.VARIABLE)

        if self.__type == BitwiseType.CONJUNCTION: return "&"
        if self.__type == BitwiseType.EXCL_DISJUNCTION: return "^"
        return "|"

    # Returns a string representation of this node, including all its
    # (transitive) children.
    def to_string(self, variables=[], withParentheses=False):
        if self.__type == BitwiseType.TRUE:
            return "0" if self.__negated else "1"

        if self.__type == BitwiseType.VARIABLE:
            if len(variables) == 0:
                return ("~x" if self.__negated else "x") + str(self.__vidx)
            return ("~" if self.__negated else "") + variables[self.__vidx]

        withParentheses = withParentheses or self.__negated
        assert(self.child_count() > 1)

        s = "~" if self.__negated else ""
        s += "(" if withParentheses else ""
        s += self.__children[0].to_string(variables, True)
        for child in self.__children[1:]:
            s += self.__op_to_string() + child.to_string(variables, True)
        s += ")" if withParentheses else ""

        return s

    # Returns true iff this node's children are all contained in the
    # given one's children'.
    def __are_all_children_contained(self, other):
        assert(other.__type == self.__type)

        oIndices = list(range(len(other.__children)))
        for child in self.__children:
            found = False
            for i in oIndices:
                if child.equals(other.__children[i]):
                    oIndices.remove(i)
                    found = True

            if not found:
                return False

        return True

    # Returns true iff this node equals the given one.
    def equals(self, other, negated=False):
        if (self.__type != other.__type): return False
        if self.__vidx != other.__vidx: return False
        if (self.__negated == other.__negated) == negated: return False
        if len(self.__children) != len(other.__children): return False

        return self.__are_all_children_contained(other)

    # Copy the only child's content to this node.
    def __pull_up_child(self):
        assert(len(self.__children) == 1)
        child = self.__children[0]

        self.__type = child.__type
        self.__vidx = child.__vidx
        self.__negated ^= child.__negated
        self.__children = child.__children

    # Copy the given node's content to this node.
    def __copy(self, node):
        self.__type = node.__type
        self.__vidx = node.__vidx
        self.__negated = node.__negated
        self.__children = node.__children

    # Copy this node's content to a new node.
    def __get_copy(self):
        n = Bitwise(self.__type, self.__negated, self.__vidx)
        n.__children = []

        for child in self.__children:
            n.__children.append(child.__get_copy())

        return n

    # Try to refine the structure of the tree whose root node is this node.
    # That is, try to write the bitwise expression more simply, possibly
    # introducing exclusive disjunctions, flipping negations or extracting
    # common nodes of children.
    def refine(self):
        MAX_IT = 10

        for i in range(MAX_IT):
            if not self.__refine_step(): return

    # Perform one step of the refinement, see refine().
    def __refine_step(self):
        changed = False

        for child in self.__children:
            if child.__refine_step(): changed = True

        if self.__check_insert_xor(): changed = True
        if self.__check_flip_negation(): changed = True
        if self.__check_extract(): changed = True

        return changed

    # Try to replace any subexpressions with an exclusive disjunction, see
    # __try_insert_xor().
    def __check_insert_xor(self):
        if self.__type not in [BitwiseType.CONJUNCTION, BitwiseType.INCL_DISJUNCTION]:
            return

        changed = False
        for i in range(len(self.__children) - 1):
            # The range above is not updated when a child is deleted.
            if i >= len(self.__children) - 1: break

            for j in range(1, len(self.__children)):
                if self.__try_insert_xor(i, j):
                    changed = True
                    break

        if changed and len(self.__children) == 1:
            self.__pull_up_child()

        return changed

    # Try to insert an exclusive disjunction applying the rules
    # "(x|y) & (~x|~y) -> (x^y)" or "(x&y) | (~x&~y) -> (x^~y)".
    def __try_insert_xor(self, i, j):
        child1 = self.__children[i]
        child2 = self.__children[j]
        
        t = self.__type
        ot = BitwiseType.INCL_DISJUNCTION if t == BitwiseType.CONJUNCTION else BitwiseType.CONJUNCTION

        if child1.__type != ot or child2.__type != ot: return False

        # TODO: Group children of children together if there are more.
        if len(child1.__children) != 2 or len(child2.__children) != 2:
            return False

        for perm in [[0, 1], [1, 0]]:
            if child1.__children[0].equals(child2.__children[perm[0]], True):
                if not child1.__children[1].equals(child2.__children[perm[1]], True):
                    return False

                child1.__type = BitwiseType.EXCL_DISJUNCTION

                # (x|y) & (~x|~y) -> (x^y)
                if t == BitwiseType.CONJUNCTION:
                    if child1.__children[0].__negated:
                        child1.__children[0].__negated = False
                        child1.__children[1].__negated = not child1.__children[1].__negated

                # (x&y) | (~x&~y) -> (x^~y)
                else:
                    if child1.__children[0].__negated: child1.__children[0].__negated = False
                    else: child1.__children[1].__negated = not child1.__children[1].__negated

                del self.__children[j]
                return True

        return False

    # Check whether the subexpression corresponding to this node becomes
    # simpler when flipping the negation of this node together with that of its
    # children.
    def __check_flip_negation(self):
        if len(self.__children) == 0: return False

        changed = False

        for child in self.__children:
            if child.__check_flip_negation(): changed = True

        cnt = len(self.__children)
        negCnt = sum([(1 if c.__negated else 0) for c in self.__children])
        if 2 * negCnt < cnt: return changed
        if 2 * negCnt == cnt and (not self.__negated or self.__type == BitwiseType.EXCL_DISJUNCTION):
            return changed

        if self.__type != BitwiseType.EXCL_DISJUNCTION:
            self.__negated = not self.__negated
            if self.__type == BitwiseType.INCL_DISJUNCTION: self.__type = BitwiseType.CONJUNCTION
            else: self.__type = BitwiseType.INCL_DISJUNCTION

        for child in self.__children:
            child.__negated = not child.__negated

        return True

    # Returns true iff all this node's children have the given type.
    def __do_all_children_have_type(self, t):
        for child in self.__children:
            if child.__type != t: return False
            if child.__negated: return False
        return True

    # Check whether a common node can be factored out of this node's children.
    def __check_extract(self):
        t = self.__type
        if t != BitwiseType.CONJUNCTION and t != BitwiseType.INCL_DISJUNCTION: return False

        ot = BitwiseType.INCL_DISJUNCTION if t == BitwiseType.CONJUNCTION else BitwiseType.CONJUNCTION
        if not self.__do_all_children_have_type(ot): return False

        commons = []
        while True:
            common = self.__try_extract()
            if common == None: break
            commons.append(common)

        if len(commons) == 0: return False

        for child in self.__children:
            assert(len(child.__children) > 0)
            if len(child.__children) == 1:
                child = child.__pull_up_child()

        node = Bitwise(ot, self.__negated)
        self.__negated = False
        node.__children = commons + [self.__get_copy()]
        self.__copy(node)

        return True

    # Try to factor a common node out of this node's children.
    def __try_extract(self):
        assert(self.__type in [BitwiseType.CONJUNCTION, BitwiseType.INCL_DISJUNCTION])

        common = self.__get_common_child()
        if common == None: return None

        for child in self.__children:
            child.__remove_child(common)

        return common

    # Returns a node, if existent, which appear in all children and hence can
    # be factored out.
    def __get_common_child(self):
        assert(self.__type in [BitwiseType.CONJUNCTION, BitwiseType.INCL_DISJUNCTION])

        # It is enough to consider the first child and check for all of its
        # children whether they appear in the other children too.

        first = self.__children[0]
        for child in first.__children:
            if self.__has_child_in_remaining_children(child):
                return child.__get_copy()
        return None

    # Returns true iff the given node can be factored out from all children but
    # the first one.
    def __has_child_in_remaining_children(self, node):
        assert(self.__type in [BitwiseType.CONJUNCTION, BitwiseType.INCL_DISJUNCTION])

        for child in self.__children[1:]:
            if not child.__has_child(node): return False
        return True

    # Returns true iff this node has a child equal to the given node.
    def __has_child(self, node):
        for child in self.__children:
            if child.equals(node): return True
        return False

    # Remove the given node from this node's children.
    def __remove_child(self, node):
        for i in range(len(self.__children)):
            if self.__children[i].equals(node):
                del self.__children[i]
                return

        assert(False)
