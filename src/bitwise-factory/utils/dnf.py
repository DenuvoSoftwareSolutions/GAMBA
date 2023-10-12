import re

from implicant import Implicant, Bitwise, BitwiseType

usingGmpy = True
try: import gmpy2
except ModuleNotFoundError: usingGmpy = False

# Returns the number of ones in the given number's binary representation.
def popcount(x):
    if usingGmpy: return gmpy2.popcount(x)
    try: return x.bit_count()
    except AttributeError: return bin(x).count("1")


# A structure representing a disjunctive normal form, i.e., a disjunction of
# conjunctions of possibly negated variables.
class Dnf():
    # Initialize a disjunctive normal form with given number of variables and
    # the given truth value vector.
    def __init__(self, vnumber, vec):
        self.__groups = []
        self.primes = []

        self.__init_groups(vnumber, vec)
        self.__merge()
        self.__drop_unrequired_implicants(vec)

    # Create a vector representation of conjunction for each 1 in the given
    # vector, equivalent to the corresponding evaluation of variables according
    # to its position, and classify the conjunctions according to their numbers
    # of ones.
    def __init_groups(self, vnumber, vec):
        assert(len(vec) == 2**vnumber)

        self.__groups = [dict() for i in range(vnumber + 1)]
        for i in range(len(vec)):
            bit = vec[i]

            if bit == 0: continue
            assert(bit == 1)

            impl = Implicant(vnumber, i)
            onesCnt = popcount(i)
            group = self.__groups[onesCnt]

            if "0" in group: group["0"].append(impl)
            else: group["0"] = [impl]

    # Try to merge implicants (i.e., vector representations of conjunctions)
    # whose vectors differ in just one position. Note that, e.g., the
    # disjunction of "x&y&z" and "x&y&~z" can be simplified to "x&y" since the
    # "z" has no influence on its values."
    def __merge_step(self):
        changed = False
        newGroups = [dict() for g in self.__groups]

        for onesCnt in range(len(self.__groups)):
            group = self.__groups[onesCnt]

            if onesCnt < len(self.__groups) - 1:
                nextGroup = self.__groups[onesCnt + 1]

                # Iterate over hashes of indifferent positions.
                for h in group:
                    # The next group has no implicants with coincident
                    # indifferent positions.
                    if h not in nextGroup: continue

                    for impl1 in group[h]:
                        for impl2 in nextGroup[h]:
                            newImpl = impl1.try_merge(impl2)
                            # Could not merge the implicants.
                            if newImpl == None: continue

                            changed = True
                            impl1.obsolete = True
                            impl2.obsolete = True

                            newGroup = newGroups[newImpl.count_ones()]
                            newH = newImpl.get_indifferent_hash()

                            if newH in newGroup: newGroup[newH].append(newImpl)
                            else: newGroup[newH] = [newImpl]

            for h in group:
                for impl in group[h]:
                    if not impl.obsolete:
                        self.primes.append(impl)

        self.__groups = newGroups
        # The only group which may vanish is the last one, since it was not
        # empty before and its elements can only be merged into the second-last
        # group.
        if len(self.__groups[-1]) == 0: del self.__groups[-1]
        return changed

    # Try to merge implicants iteratively until nothing can be merged any more.
    def __merge(self):
        while True:
            changed = self.__merge_step()

            if not changed:
                return

    # Remove impliciants which are already represented by others.
    def __drop_unrequired_implicants(self, vec):
        requ = set([i for i in range(len(vec)) if vec[i] == 1])
        
        i = 0
        while i < len(self.primes):
            impl = self.primes[i]

            mtSet = set(impl.minterms)
            # The implicant has still required terms.
            if mtSet & requ:
                requ -= mtSet
                i += 1
                continue

            del self.primes[i]

    # Returns a string representation of this DNF.
    def __str__(self):
        s = "implicants:\n"

        for impl in self.primes:
            s += "    " + str(impl) + "\n"

        return s

    # Create an abstract syntax tree structure corresponding to this DNF.
    def to_bitwise(self):
        cnt = len(self.primes)
        if cnt == 0: return Bitwise(BitwiseType.TRUE, True)
        if cnt == 1: return self.primes[0].to_bitwise()

        root = Bitwise(BitwiseType.INCL_DISJUNCTION)
        for p in self.primes:
            root.add_child(p.to_bitwise())

        return root

    # Returns a more detailed string representation.
    def get(self, variables):
        if len(self.primes) == 0: return "0"

        s = ""
        for p in self.primes:
            if len(s) > 0: s += "|"

            ps = p.get(variables)
            withPar = len(self.primes) > 1 and bool(re.search("([&])", ps))
            s += "(" + ps + ")" if withPar else ps

        return s
