#!/usr/bin/python3



# An index together with a multitude it appears with.
class IndexWithMultitude():
    def __init__(self, idx, multitude=1):
        self.idx = idx
        self.multitude = multitude

    def __str__(self): return "[idx " + str(self.idx) + ", mult " + str(self.multitude) + "]"

# A node representing a subset of a sum.
class Batch():
    # Initialize internals
    def __init__(self, prevFactorIndices, factorIndices, termIndices, nodesToTerms,
                 termsToNodes, nodesTriviality, nodesOrder):
        self.prevFactorIndices = prevFactorIndices
        self.factorIndices = factorIndices
        self.atoms = []
        self.children = []

        self.__partition(nodesToTerms, termIndices, termsToNodes, nodesTriviality, nodesOrder)

    # Partition the batch into subbatches and atoms.
    def __partition(self, nodesToTerms, termIndices, termsToNodes, nodesTriviality, nodesOrder):
        todo = set(termIndices)

        while True:
            if len(nodesToTerms) == 0: break

            # The index of the next node to be factored out.
            idx = self.__get_next_batch(nodesToTerms, termsToNodes, nodesTriviality, nodesOrder)
            # No such index, i.e., no factorization possible.
            if idx == None: break

            assert(len(nodesToTerms[idx][1]) > 1)

            factor = nodesToTerms[idx][0]
            multitude = self.__get_lowest_multitude(nodesToTerms[idx][1])

            factors = [IndexWithMultitude(factor, multitude)]
            # The terms which contain the node to be factored out.
            terms = set([p.idx for p in nodesToTerms[idx][1]])
            # The new list mapping nodes to terms contained in the list above.
            ntt = []

            # Reduce multitude due to the node being factored out.
            nodesToTerms[idx][1] = self.__reduce_multitudes(nodesToTerms[idx][1], multitude)
            if len(nodesToTerms[idx][1]) > 0: ntt.append(nodesToTerms[idx])
            del nodesToTerms[idx]

            # Now collect all occurrences of nodes in the new term list.
            for i in range(len(nodesToTerms) - 1, -1, -1):
                b = nodesToTerms[i]

                # Terms containing the current node.
                t = {p.idx for p in b[1]}
                # The intersection with the batch.
                inters = t & terms
                if len(inters) > 1:
                    # b contains all terms.
                    if len(inters) == len(terms):
                        # If b contains additional terms, we have to split it.
                        spl = {p for p in b[1] if p.idx in inters}

                        multitude = self.__get_lowest_multitude(spl)
                        factors.append(IndexWithMultitude(b[0], multitude))

                        spl = self.__reduce_multitudes(spl, multitude)
                        if len(spl) > 0: ntt.append([b[0], spl])

                        # It may be that b is larger than the currently chosen
                        # batch, since we neglect factoring out nodes that
                        # would only apply triviality.

                    else:
                        # Split b.
                        ntt.append([b[0], {p for p in b[1] if p.idx in inters}])

                    b[1] = {p for p in b[1] if p.idx not in inters}
                    if len(b[1]) <= 1: del nodesToTerms[i]

                elif len(inters) > 0:
                    b[1] = {p for p in b[1] if p.idx not in inters}
                    if len(b[1]) <= 1: del nodesToTerms[i]

            self.children.append(Batch(self.factorIndices + self.prevFactorIndices, factors,
                                       terms, ntt, termsToNodes, nodesTriviality, nodesOrder))
            todo -= terms

        # Add atoms for the remaining terms.
        self.atoms = todo

    # Determine the next largest possible batch, if there is any.
    def __get_next_batch(self, nodesToTerms, termsToNodes, nodesTriviality, nodesOrder):
        indices = self.__get_largest_termset_indices(nodesToTerms, termsToNodes, nodesTriviality)
        if indices == None: indices = self.__get_largest_termset_indices(nodesToTerms)
        if indices == None: return None

        if len(indices) == 1: return indices[0]

        # If there are multiple largest batches, check for coincidences.
        collected = self.__collect_largest_batches(nodesToTerms, indices)
        largest = self.__get_largest_list_indices(collected)
        for o in nodesOrder:
            if o in largest: return indices[o]
        assert(False)
        return indices[largest[0]]

    # For all batches corresponding to the given indices, count their
    # occurrences.
    def __collect_largest_batches(self, nodesToTerms, indices):
        collected = []
        i = 0

        while True:
            if i == len(indices): break

            found = False
            for j in range(i):
                if nodesToTerms[i] == nodesToTerms[j]:
                    collected[j].append(i)
                    del indices[i]
                    found = True
                    break

            if not found:
                collected.append([i])
                i += 1

        return collected

    # Returns the lowest multitude of any element in the given list.
    def __get_lowest_multitude(self, indicesWithMultitude):
        return min(indicesWithMultitude, key=lambda x:x.multitude).multitude

    # In the given list of indices and multitudes, reduce the multitudes by the
    # given value.
    def __reduce_multitudes(self, indicesWithMultitude, delta):
        for p in indicesWithMultitude:
            assert(p.multitude >= delta)
            p.multitude -= delta

        return {p for p in indicesWithMultitude if p.multitude > 0}

    # Returns the indices of the largest sets that are each second elements of
    # the given pairs.
    def __get_largest_termset_indices(self, pairs, termsToNodes=None, nodesTriviality=None):
        assert(len(pairs) > 0)
        assert((termsToNodes == None) == (nodesTriviality == None))

        indices = None
        maxl = None

        for i in range(len(pairs)):
            l = len(pairs[i][1])
            # We are only interested in factors which can be factored out from
            # at least 2 terms.
            if l < 2: continue

            # We already have a better candidate.
            if maxl != None and l < maxl: continue

            # The factor cannot be factored out from any nontrivial term.
            if nodesTriviality != None:
                if not self.__check_for_nontrivial(pairs[i], termsToNodes, nodesTriviality):
                    continue

            if l == maxl: indices.append(i)
            else:
                indices = [i]
                maxl = l

        return indices

    # Returns true iff the given list of pairs contains a pair whose
    # second-element list contains the index of a term which has nontrivial
    # factors left.
    def __check_for_nontrivial(self, nodeToTerms, termsToNodes, nodesTriviality):
        for pair in nodeToTerms[1]:
            # Copy set in order not to change any states.
            t = {IndexWithMultitude(p.idx, p.multitude) for p in termsToNodes[pair.idx]}
            t = self.__reduce_multitudes_corresponding_to_list(t, self.factorIndices)
            t = self.__reduce_multitudes_corresponding_to_list(t, self.prevFactorIndices)

            for p in t:
                if p.idx == nodeToTerms[0]: continue
                if not nodesTriviality[p.idx]: return True

        return False

    # In the given list of indices and multitudes, reduce the multitudes by the
    # given values.
    def __reduce_multitudes_corresponding_to_list(self, indicesWithMultitude, reductions):
        for r in reductions:
            res = [p for p in indicesWithMultitude if p.idx == r.idx]
            assert(len(res) == 1)
            res[0].multitude -= r.multitude
            assert(res[0].multitude >= 0)

        return {p for p in indicesWithMultitude if p.multitude > 0}

    # Returns the indices of the largest lists.
    def __get_largest_list_indices(self, lists):
        assert(len(lists) > 0)

        indices = [0]
        maxl = len(lists[0])

        for i in range(1, len(lists)):
            l = len(lists[i])
            if l == maxl: indices.append(i)
            elif l > maxl:
                indices = [i]
                maxl = l

        return indices


    # Returns true iff this batch has no subbatches.
    def is_trivial(self):
        return len(self.children) == 0

    # Print information about the batch.
    def print(self, indent=0):
        print(indent*" " + "BATCH")
        indent += 2
        print(indent*" " + "factors:", end="")
        for f in self.factorIndices: print(" " + str(f), end="")
        print()
        print(indent*" " + "atoms: ", end="")
        for a in self.atoms: print(" " + str(a), end="")
        print()
        print(indent*" " + "children: ")
        for c in self.children: c.print(indent + 2)
