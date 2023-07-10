#!/usr/bin/python3

import re
import sys

from parse import parse, Node, NodeType


# A class which classifies expressions and computes statistics.
class Classifier():
    # Initialize internals.
    def __init__(self, bitCount):
        self.__bitCount = bitCount
        self.__tree = None

    # Parse the given expression into an AST.
    def __parse(self, expr):
        self.__tree = parse(expr, self.__bitCount, True, False, False)
        self.__tree.mark_linear()

    # Find all variables occuring in the stored tree, store them in a list and
    # enumerate the tree's variable nodes accordingly. Returns the number of
    # variables.
    def __collect_and_enumerate_variables(self):
        variables = []
        # Get a list of unique variables.
        self.__tree.collect_and_enumerate_variables(variables)
        return len(variables)

    def __count_terms_linear(self, expr):
        assert(self.__tree.state == NodeState.LINEAR)

        # NOTE: We do not operate on the tree here because a string analysis is
        # more flexible in this case.
        #if self.__tree.type == NodeType.SUM: 

    # Classify the given expression.
    def classify(self, expr):
        self.__parse(expr)
        if self.__tree == None: sys.exit("Error: Could not parse expression!")

        vnumber = self.__collect_and_enumerate_variables()
        state = self.__tree.state
        stringlen = len(expr.replace(" ", ""))
        nodes = self.__tree.count_nodes()
        alternation = self.__tree.compute_alternation()
        terms = None
        if self.__tree.is_linear(): terms = self.__tree.count_terms_linear()

        return vnumber, state, stringlen, nodes, alternation, terms


# Classify the given expression.
def classify_mba(expr, bitCount):
    classifier = Classifier(bitCount)
    stats = classifier.classify(expr)
    return stats


# Print options.
def print_usage():
    print("Usage: python3 classify.py")
    print("Command line input not preceded by option indicators below are considered expressions to be classified.")
    print("Command line options:")
    print("    -h:    print usage")
    print("    -b:    specify the bit number of variables (default is 64)")


if __name__ == "__main__":
    argc = len(sys.argv)
    bitCount = 64
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

        else:
            expressions.append(sys.argv[i])

    if len(expressions) == 0:
        sys.exit("No expressions to parse given!")

    for expr in expressions:
        print("*** Expression " + expr)
        vnumber, state, stringlen, nodes, alternation, terms = classify_mba(expr, bitCount)

        print("*** ... vnumber: " + str(vnumber))
        print("*** ... state: " + str(state))
        print("*** ... stringlen: " + str(stringlen))
        print("*** ... nodes: " + str(nodes))
        print("*** ... alternation: " + str(alternation))
        if terms != None: print("*** ... terms: " + str(terms))

    sys.exit(0)
