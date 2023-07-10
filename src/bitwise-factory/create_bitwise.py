#!/usr/bin/python3

import inspect
import io
import os
import re
import sys
import traceback

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
utilsdir = os.path.join(currentdir, "utils")
sys.path.insert(0, utilsdir)
from dnf import Dnf
from bitwise import Bitwise


# Class for creating bitwise expressions for a given number of variables.
class BitwiseFactory():
    def __init__(self, vnumber, variables=None, noTable=False):
        assert(variables == None or len(variables) >= vnumber)

        self.__vnumber = vnumber
        self.__variables = variables
        self.__usesDefaultVars = variables == None
        self.__table = None
        self.__noTable = noTable

        if self.__usesDefaultVars:
            self.__variables = [self.__get_alt_vname(i) for i in range(vnumber)]

    # Get the alternative name of the variable with given index used if no
    # variable names are specified.
    def __get_alt_vname(self, i):
        return "X[" + str(i) + "]"

    # Initializes the lookup table containing 2^2^t base expressions for the
    # used number t of variables. Requires that the number of variables is not
    # larger than 3.
    def __init_table(self):
        if self.__vnumber == 1: self.__init_table_1var()
        elif self.__vnumber == 2: self.__init_table_2vars()
        elif self.__vnumber == 3: self.__init_table_3vars()
        else: assert(False)

    # Initializes the lookup table for 1 variable.
    def __init_table_1var(self):
        self.__table = [
                        "0",    # [0 0]
                        "X[0]"  # [0 1]
                       ]

    # Initializes the lookup table for 2 variables.
    def __init_table_2vars(self):
        self.__table = [
                        "0",                # [0 0 0 0]
                        "(X[0]&~X[1])",     # [0 1 0 0]
                        "(~X[0]&X[1])",     # [0 0 1 0]
                        "(X[0]^X[1])",      # [0 1 1 0]
                        "(X[0]&X[1])",      # [0 0 0 1]
                        "X[0]",             # [0 1 0 1]
                        "X[1]",             # [0 0 1 1]
                        "(X[0]|X[1])"       # [0 1 1 1]
                       ]

    # Initializes the lookup table for 3 variables.
    def __init_table_3vars(self):
        truthfile = os.path.join(utilsdir, "bitwise_list_" + str(self.__vnumber) + "vars.txt")
        bitwiseExprList = []

        with open(truthfile, "r") as fr:
            for line in fr:
                line = line.strip()
                b = re.split("#", line)[0].rstrip()
                bitwiseExprList.append(b)

        self.__table = bitwiseExprList


    # Create a bitwise expression with given truth value vector.
    def __create_bitwise(self, vector):
        d = Dnf(self.__vnumber, vector)
        b = d.to_bitwise()
        b.refine()
        s = b.to_string(self.__variables)

        # Add parentheses if necessary.
        if bool(re.search("([&|^])", s)): s = "(" + s + ")"
        return s

    # For the given vector of truth values, returns the truth value vector for
    # the corresponding expression after subtracting the given offset. That
    # is, returns a vector which has zeros exactly in the positions where the
    # given vector contains the given offset.
    def __get_bitwise_vector(self, vector, offset):
        return [(0 if v == offset else 1) for v in vector]

    # For the given vector of truth values, returns the index of the
    # corresponding expression in the lookup table after subtracting the given
    # offset. That is, returns the index of the truth table entry for a truth
    # value vector which has zeros exactly in the positions where the given
    # vector contains the given offset.
    def __get_bitwise_index_for_vector(self, vector, offset):
        index = 0
        add = 1
        for i in range(len(vector) - 1):
            if vector[i+1] != offset: index += add
            add <<= 1

        return index

    # For the given vector of truth values, returns the corresponding bitwise
    # expression from the lookup table after subtracting the given offset, if
    # given. Initializes the table if not yet initialized.
    def __get_bitwise_from_table(self, vector, offset):
        if self.__table == None: self.__init_table()

        index = self.__get_bitwise_index_for_vector(vector, offset)
        bitwise = self.__table[index]

        if not self.__usesDefaultVars:
            # Exchange variables.
            for i in range(self.__vnumber):
                bitwise = bitwise.replace(self.__get_alt_vname(i), self.__variables[i])

        return bitwise

    # For the given vector of truth values, creates the corresponding bitwise
    # expression after subtracting the given offset. Uses the Quine-McCluskey
    # algorithm and some addiitonal refinement.
    def __create_bitwise_with_offset(self, vector, offset):
        vector = self.__get_bitwise_vector(vector, offset)
        return self.__create_bitwise(vector)

    # For the given vector of truth values, returns the corresponding bitwise
    # expression after subtracting the given offset, if given.
    def __create_bitwise_unnegated(self, vector, offset=0):
        if not self.__noTable and self.__vnumber <= 3:
            return self.__get_bitwise_from_table(vector, offset)
        return self.__create_bitwise_with_offset(vector, offset)

    # For the given vector of truth values, returns the corresponding bitwise
    # expression after subtracting the given offset, if given. That is, returns
    # the truth table entry for a truth value vector which has zeros exactly in
    # the positions where the given vector contains the given offset. If
    # negated is True, the bitwise expression is negated.
    def create_bitwise(self, vector, negated=False, offset=0):
        # If the vector's first entry is nonzero after subtracting the offset,
        # negate the truth values and negate the bitwise thereafter.
        if not self.__noTable and self.__vnumber <= 3 and vector[0] != offset:
            assert(vector[0] == offset + 1)
            for i in range(len(vector)):
                vector[i] = offset + (vector[i] - offset + 1) % 2
            negated = True

        e = self.__create_bitwise_unnegated(vector, offset)
        if negated: return e[1:] if e[0] == "~" else "~" + e
        return e


# Returns a bitwise expression in string representation corresponding to the
# given truth value vector If an offset is given, the truth value vector is
# derived via subtracting the offset from the given vector. If no variables are
# passed, the variables haven names "X[i]".
def create_bitwise(vnumber, vec, offset=0, variables=None, noTable=False):
    factory = BitwiseFactory(vnumber, variables, noTable)
    return factory.create_bitwise(vec, False, offset)


# Print usage.
def print_usage():
    print("Usage: python3 create_bitwise.py <vnumber> <truth values>")
    print("The truth value list starts with \"[\", ends with \"]\" and contains values separated by spaces.")
    print("The variables are expected to start with letters and consist of letters, underscores and digits.")
    print("Command line options:")
    print("    -h:    print usage")
    print("    -v:    specify the variables (in same notation as the truth values)")
    print("    -o:    specify some offset for the truth value vector")
    print("    -n:    disable usage of lookup tables")


if __name__ == "__main__":
    argc = len(sys.argv)

    if argc == 2 and sys.argv[1] == "-h":
        print_usage()
        sys.exit(0)

    if argc < 3: sys.exit("Requires vnumber and truth values as arguments!")

    vnumber = int(sys.argv[1])
    vec = list(map(int, sys.argv[2].strip('[]').split(' ')))

    if len(vec) != 2**vnumber:
        sys.exit("Incorrect number of truth values! Requires exactly " + str(2**vnumber) + " values.")

    offset = 0
    variables = None
    noTable = False

    i = 2
    while i < argc - 1:
        i = i + 1

        if sys.argv[i] == "-h":
            print_usage()
            sys.exit(0)

        elif sys.argv[i] == "-o":
            i += 1
            if i == argc:
                print_usage()
                sys.exit("Error: No offset list!")

            offset = int(sys.argv[i])

        elif sys.argv[i] == "-v":
            i += 1
            if i == argc:
                print_usage()
                sys.exit("Error: No variable list!")

            variables = input.strip('[]').split(' ')

            if len(vec) < vnumber:
                sys.exit("Incorrect number of variables! Requires at least " + str(vnumber) + " values.")

        elif sys.argv[i] == "-n": noTable = True

        else: sys.exit("Unknown option " + sys.argv[i] + "!")

    if vec.count(offset) + vec.count(offset + 1) != len(vec):
        sys,exit("Error: Only offset and offset+1 allowed in truth vector!")

    print("*** Truth values " + str(vec))
    bw = create_bitwise(vnumber, vec, 0, variables, noTable)
    print("*** ... yields " + bw)

