#!/usr/bin/python3

import re
import sys

from node import Node, NodeType, NodeState


# A class which constructs a tree representation for a given expression.
class Parser():
    def __init__(self, expr, modulus, modRed=False):
        self.__expr = expr
        self.__modulus = modulus
        self.__modRed = modRed
        self.__idx = 0
        self.__error = ""

    # Parse the whole expression and in this course merge or rearrange constants.
    # Sets self.__error if an error occurs.
    def parse_expression(self):
        if self.__has_space():
            self.__skip_space()
        root = self.__parse_inclusive_disjunction()

        while self.__idx < len(self.__expr) and self.__has_space():
            self.__skip_space()

        if self.__idx != len(self.__expr):
            self.__error = "Finished near to " + self.__peek() + " before everything was parsed"
            return None

        return root

    # Returns a node with given type.
    def __new_node(self, t):
        return Node(t, self.__modulus, self.__modRed)

    # Parse the inclusive disjunction starting at current idx. Sets self.__error
    # if an error occurs.
    def __parse_inclusive_disjunction(self):
        child = self.__parse_exclusive_disjunction()
        if child == None:
            return None
        # We have a trivial inclusive disjunction, no need for a dedicated node.
        if self.__peek() != '|':
            return child

        node = self.__new_node(NodeType.INCL_DISJUNCTION)
        node.children.append(child)

        while self.__peek() == '|':
            self.__get()
            child = self.__parse_exclusive_disjunction()
            if child == None:
                return None

            node.children.append(child)

        return node

    # Parse the exclusive disjunction starting at current idx and in this course
    # merge or rearrange constants. Sets self.__error if an error occurs.
    def __parse_exclusive_disjunction(self):
        child = self.__parse_conjunction()
        if child == None:
            return None
        # We have a trivial exclusive disjunction, no need for a dedicated node.
        if self.__peek() != '^':
            return child

        node = self.__new_node(NodeType.EXCL_DISJUNCTION)
        node.children.append(child)

        while self.__peek() == '^':
            self.__get()
            child = self.__parse_conjunction()
            if child == None:
                return None

            node.children.append(child)

        return node

    # Parse the conjunction starting at current idx and in this course merge or
    # rearrange constants. Sets self.__error if an error occurs.
    def __parse_conjunction(self):
        child = self.__parse_shift()
        if child == None:
            return None
        # We have a trivial conjunction, no need for a dedicated node.
        if self.__peek() != '&':
            return child

        node = self.__new_node(NodeType.CONJUNCTION)
        node.children.append(child)

        while self.__peek() == '&':
            self.__get()
            child = self.__parse_shift()
            if child == None:
                return None

            node.children.append(child)

        return node

    def __parse_shift(self):
        base = self.__parse_sum()
        if base == None:
            return None

        # We have a trivial shift only consisting of a base, no need for a
        # dedicated node.
        if not self.__has_lshift():
            return base

        # We write "a << b" as "a * 2**b".

        prod = self.__new_node(NodeType.PRODUCT)
        prod.children.append(base)

        self.__get()
        self.__get()

        op = self.__parse_sum()
        if op == None:
            return None

        power = self.__new_node(NodeType.POWER)
        two = self.__new_node(NodeType.CONSTANT)
        two.constant = 2
        power.children.append(two)
        power.children.append(op)

        prod.children.append(power)

        # Nested shift operations require parentheses.
        if self.__has_lshift():
            self.__error = "Disallowed nested lshift operator near " + self.__peek()
            return None

        return prod

    # Parse the sum starting at current idx and in this course merge or
    # rearrange constants. Sets self.__error if an error occurs.
    def __parse_sum(self):
        child = self.__parse_product()
        if child == None:
            return None
        # We have a trivial sum, no need for a dedicated node.
        if self.__peek() != '+' and self.__peek() != '-':
            return child

        node = self.__new_node(NodeType.SUM)
        node.children.append(child)

        while self.__peek() == '+' or self.__peek() == '-':
            negative = self.__peek() == '-'
            self.__get()
            child = self.__parse_product()
            if child == None:
                return None

            if negative:
                node.children.append(self.__multiply_by_minus_one(child))
            else:
                node.children.append(child)

        return node

    # Parse the product starting at current idx and in this course merge or
    # rearrange constants. Sets self.__error if an error occurs.
    def __parse_product(self):
        child = self.__parse_factor()
        if child == None:
            return None
        # We have a trivial product, no need for a dedicated node.
        if not self.__has_multiplicator():
            return child

        node = self.__new_node(NodeType.PRODUCT)
        node.children.append(child)

        while self.__has_multiplicator():
            self.__get()
            child = self.__parse_factor()
            if child == None:
                return None

            node.children.append(child)

        return node

    # Parse the factor of a (trivial or nontrivial) product starting at current
    # idx and in this course merge or rearrange constants. Sets self.__error if
    # an error occurs.
    def __parse_factor(self):
        if self.__has_bitwise_negated_expression():
            return self.__parse_bitwise_negated_expression()

        if self.__has_negative_expression():
            return self.__parse_negative_expression()

        return self.__parse_power()

    # Parse the bitwise negated expression starting at current idx and in this
    # course merge or rearrange constants. Sets self.__error if an error occurs.
    def __parse_bitwise_negated_expression(self):
        # Skip '~'.
        self.__get()
        node = self.__new_node(NodeType.NEGATION)

        child = self.__parse_factor()
        if child == None:
            return None

        node.children = [child]
        return node

    # Parse the arithmetically negated expression starting at current idx and
    # in this course merge or rearrange constants. Sets self.__error if an error
    # occurs.
    def __parse_negative_expression(self):
        # Skip '-'.
        self.__get()

        node = self.__parse_factor()
        if node == None:
            return None

        # Multiply by -1.
        return self.__multiply_by_minus_one(node)

    # Returns a node which is the negative of the given node.
    def __multiply_by_minus_one(self, node):
        if node.type == NodeType.CONSTANT:
            node.constant = -node.constant
            return node

        if node.type == NodeType.PRODUCT:
            if node.children[0].type == NodeType.CONSTANT:
                node.children[0].constant *= -1
                return node

            minusOne = self.__new_node(NodeType.CONSTANT)
            minusOne.constant = -1
            node.children.insert(0, minusOne)
            return node

        # We need a new node for the multiplication with -1.
        minusOne = self.__new_node(NodeType.CONSTANT)
        minusOne.constant = -1
        prod = self.__new_node(NodeType.PRODUCT)
        prod.children = [minusOne, node]
        return prod

    # Parse the power starting at current idx.
    def __parse_power(self):
        base = self.__parse_terminal()
        if base == None:
            return None
        # We have a trivial power only consisting of a base, no need for a
        # dedicated node.
        if not self.__has_power():
            return base

        node = self.__new_node(NodeType.POWER)
        node.children.append(base)

        self.__get()
        self.__get()

        exp = self.__parse_terminal()
        if exp == None:
            return None

        node.children.append(exp)

        # Nested power operations require parentheses.
        if self.__has_power():
            self.__error = "Disallowed nested power operator near " + self.__peek()
            return None

        return node

    # Parse the terminal expression starting at current idx.
    def __parse_terminal(self):
        if self.__peek() == '(':
            self.__get()
            node = self.__parse_inclusive_disjunction()
            if node == None:
                return None
            if not self.__peek() == ')':
                self.__error = "Missing closing parentheses near to " + self.__peek()
                return None
            self.__get()

            return node

        if self.__has_variable():
            return self.__parse_variable()

        return self.__parse_constant()

    # Parse the variable name starting at current idx.
    def __parse_variable(self):
        start = self.__idx
        # Skip first character that has already been checked.
        self.__get(False)

        while self.__has_decimal_digit() or self.__has_letter() or self.__peek() == '_':
            self.__get(False)

        if self.__peek() == '[':
            self.__get(False)

            while self.__has_decimal_digit():
                self.__get(False)

            if self.__peek() == ']':
                self.__get()
            else:
                return None

        else:
            while self.__has_space():
                self.__skip_space()

        node = self.__new_node(NodeType.VARIABLE)
        node.vname = self.__expr[start:self.__idx].rstrip()
        return node

    # Parse the constant starting at current idx. Sets self.__error if an error
    # occurs.
    def __parse_constant(self):
        if self.__has_binary_constant():
            return self.__parse_binary_constant()

        if self.__has_hex_constant():
            return self.__parse_hex_constant()

        return self.__parse_decimal_constant()

    # Parse the binary constant starting at current idx. Sets self.__error if an
    # error occurs.
    def __parse_binary_constant(self):
        # Skip '0' and 'b'.
        self.__get(False)
        self.__get(False)

        if self.__peek() not in ['0', '1']:
            self.__error = "Invalid binary digit near to " + self.__peek()
            return None

        start = self.__idx
        while self.__peek() in ['0', '1']:
            self.__get(False)

        while self.__has_space():
            self.__skip_space()

        node = self.__new_node(NodeType.CONSTANT)
        node.constant = self.__get_constant(start, 2)
        return node

    # Parse the hex constant starting at current idx. Sets self.__error if an
    # error occurs.
    def __parse_hex_constant(self):
        # Skip '0' and 'x'.
        self.__get(False)
        self.__get(False)

        if not self.__has_hex_digit():
            self.__error = "Invalid hex digit near to " + self.__peek()
            return None

        start = self.__idx
        while self.__has_hex_digit():
            self.__get(False)

        while self.__has_space():
            self.__skip_space()

        node = self.__new_node(NodeType.CONSTANT)
        node.constant = self.__get_constant(start, 16)
        return node

    # Parse the decimal constant starting at current idx. Sets self.__error if an
    # error occurs.
    def __parse_decimal_constant(self):
        if not self.__has_decimal_digit():
            self.__error = "Expecting constant at " + self.__peek() + ", but no digit around."
            return None

        start = self.__idx
        while self.__has_decimal_digit():
            self.__get(False)

        while self.__has_space():
            self.__skip_space()

        node = self.__new_node(NodeType.CONSTANT)
        node.constant = self.__get_constant(start, 10)
        return node

    # Returns the constant starting at given index of the expression and in
    # given base representation.
    def __get_constant(self, start, base):
        return int(self.__expr[start:self.__idx].rstrip(), base)

    # Returns the character at position idx of expr, increments idx and skips
    # spaces.
    def __get(self, skipSpace=True):
        c = self.__peek()
        self.__idx += 1

        if skipSpace:
            while self.__has_space():
                self.__skip_space()

        return c

    # Set idx to the position of the next character of expr which is no space.
    def __skip_space(self):
        self.__idx += 1

    # Returns the character at position idx of expr or '' if the end of expr is
    # reached.
    def __peek(self):
        if self.__idx >= len(self.__expr):
            return ''
        return self.__expr[self.__idx]

    # Returns true iff the character at position idx of expr indicates a
    # bitwise negation.
    def __has_bitwise_negated_expression(self):
        return self.__peek() == '~'

    # Returns true iff the character at position idx of expr is a unary minus.
    def __has_negative_expression(self):
        return self.__peek() == '-'

    # Returns true iff the character at position idx is '*', but the succeeding
    # one, if existent, isn't.
    def __has_multiplicator(self):
        return self.__peek() == '*' and self.__peek_next() != '*'

    # Returns true iff the character at position idx initiates a power operator
    # '**'.
    def __has_power(self):
        return self.__peek() == '*' and self.__peek_next() == '*'

    # Returns true iff the character at position idx initiates a left shift
    # operator '<<'.
    def __has_lshift(self):
        return self.__peek() == '<' and self.__peek_next() == '<'

    # Returns true iff the character at position idx of expr and its succeeding
    # character indicate a binary number, i.e., are '0b'.
    def __has_binary_constant(self):
        return self.__peek() == '0' and self.__peek_next() == 'b'

    # Returns true iff the character at position idx of expr and its succeeding
    # character indicate a hexadecimal number, i.e., are '0x'.
    def __has_hex_constant(self):
        return self.__peek() == '0' and self.__peek_next() == 'x'

    # Returns true iff the character at position idx of expr is a valid digit in
    # hexadecimal representation.
    def __has_hex_digit(self):
        return self.__has_decimal_digit() or re.match(r'[a-fA-F]', self.__peek())

    # Returns true iff the character at position idx of expr is a valid digit in
    # decimal representation.
    def __has_decimal_digit(self):
        return re.match(r'[0-9]', self.__peek())

    # Returns true iff the character at position idx of expr indicates a
    # variable name.
    def __has_variable(self):
        return self.__has_letter()

    # Returns true iff the character at position idx of expr is a letter.
    def __has_letter(self):
        return re.match(r'[a-zA-Z]', self.__peek())

    # Returns true iff the character at position idx of expr is a space.
    def __has_space(self):
        return self.__peek() == ' '

    # Returns the character at position idx + 1 of expr or '' if the end of
    # expr would be reached.
    def __peek_next(self):
        if self.__idx >= len(self.__expr) - 1:
            return ''
        return self.__expr[self.__idx + 1]


# Parse the given expression in a modular field with given bit count.
def parse(expr, bitCount, reduceConstants=True, refine=False, marklinear=False):
    parser = Parser(expr, 2**bitCount, reduceConstants)
    root = parser.parse_expression()

    if root != None and refine:
        root.refine()
    if root != None and marklinear:
        if not refine:
            sys.exit("Error: Refine before marking linear subexpressions!")
        else:
            root.mark_linear()
    return root


# Print options.
def print_usage():
    print("Usage: python3 parse.py")
    print("Command line input not preceded by option indicators below are considered expressions to be parsed.")
    print("Command line options:")
    print("    -h:    print usage")
    print("    -b:    specify the bit number of variables (default is 64)")
    print("    -r:    refine the expressions")
    print("    -l:    mark linear subexpressions")


if __name__ == "__main__":
    argc = len(sys.argv)
    bitCount = 64
    refine = False
    marklinear = False
    expressions = []

    i = 0
    while i < argc - 1:
        i = i + 1

        if sys.argv[i] == "-h":
            print_usage()
            sys.exit(0)

        elif sys.argv[i] == "-b":
            i = i + 1
            if i == argc:
                print_usage()
                sys.exit("Error: No bit count given!")

            bitCount = int(sys.argv[i])

        elif sys.argv[i] == "-r":
            refine = True

        elif sys.argv[i] == "-l":
            marklinear = True

        else:
            expressions.append(sys.argv[i])

    if marklinear:
        refine = True

    if len(expressions) == 0:
        sys.exit("No expressions to parse given!")

    for expr in expressions:
        print("*** Expression " + expr)
        root = parse(expr, refine, bitCount, marklinear)
        if root == None:
            print("*** ... invalid")
        else:
            print("*** ... parsed to " + root.to_string())
            if marklinear:
                if root.state == NodeState.BITWISE:
                    print("*** +++ expression is a bitwise expression and hence a linear MBA")
                elif root.state == NodeState.LINEAR:
                    print("*** +++ expression is a linear MBA")
                elif root.state == NodeState.NONLINEAR:
                    print("*** --- expression is no linear MBA")
                else:
                    print("*** --- could not determine linearity")

    sys.exit(0)
