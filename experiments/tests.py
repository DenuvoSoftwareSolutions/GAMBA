#!/usr/bin/python3

from enum import Enum
import inspect
import os
import sys
import hashlib
import time
import numpy as np

from datasets import datasets, classify_dataset

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)
sys.path.insert(0, os.path.join(parentdir, "src"))
from simplify import Simplifier, check_linear
from simplify_general import GeneralSimplifier, verify_using_z3

class Mode(Enum):
    LINEAR = 1   # Only run on MBAs with linear ground truth.
    GENERAL = 2

class Property(Enum):
    LINEAR = 1
    LINEAR_GT = 2 # linear ground truth

# unique experiments (hash expression)
experiments = {}

class Experiment:
    def __init__(self, expr, gt, dsName):
        self.expression = expr
        self.groundtruth = gt
        self.dataset_names = {dsName}
        self.properties = set()
        self.solved = set()

    @staticmethod
    def hash(expr, gt):
        return hashlib.sha256((expr + gt).encode('utf-8')).hexdigest()

def create_simplifier(mode, bitCount, expr, check=False):
    verifBitCount = 4 if check else None
    if mode == Mode.LINEAR: return Simplifier(bitCount, expr, False, True, verifBitCount)
    return GeneralSimplifier(bitCount, False, verifBitCount)

def simplify(mode, simplifier, expr):
    if mode == Mode.LINEAR: return simplifier.simplify(False)
    return simplifier.simplify(expr)

def check_print_error(ex, verbosity, idx, lineno, expr):
    if verbosity >= 1:
        print('ERR%d(line %d): "%s" -- "%s"' % (idx, lineno, expr, str(ex)))
        if verbosity >= 4:
            import traceback
            traceback.print_tb(ex.__traceback__)

def process_dataset(fname, bitCount=64, mode=Mode.GENERAL, verbosity=0, limit=-1, check=False, useZ3=False):
    f = open(os.path.join(currentdir, "datasets", fname), 'rt')
    
    lineno = 0 # line number in file
    ok = 0     # expected results (completely equal to ground truth)
    okz = 0    # not ok, but verified using GAMBA
    z3 = 0     # not okz, but verified using Z3
    to = 0     # timed out
    ng = 0     # non-verifiable results
    nc = 0     # unchecked expressions which do not meet requirements
    err = 0    # error

    dur = 0
    cnt = 0
    timing = []

    for line in f.readlines():
        lineno += 1

        # Allow to limit processing of dataset.
        if limit > 0 and ok + okz + z3 + to + ng + nc + err >= limit: break

        # Ignore comments.
        if line.startswith('#'): continue

        # Split line: expression, ground truth [, whatever, ...]
        try: e, gt = line.split(',')[:2]
        except ValueError as ex:
            err += 1
            if verbosity >= 1: print('ERR0(line %d): "%s" -- "%s"' % (lineno, line.strip(), str(ex)))
            continue

        e = e.strip()
        gt = gt.strip()

        if verbosity >= 5: print("\n" + str(lineno) + ": Expression: " + e)

        h = Experiment.hash(e, gt)
        if h in experiments:
            exp = experiments[h]
            exp.dataset_names.add('%s:%d' % (ds.name, lineno))
        else:
            exp = Experiment(e, gt, '%s:%d' % (ds.name, lineno))
            experiments[h] = exp

        # Do check for linear MBA.
        try:
            if not check_linear(e, bitCount):
                if mode == Mode.LINEAR:
                    if verbosity >= 3: print('NC(line %d): "%s"' % (lineno, e))
                    nc += 1
                    continue
            else: exp.properties.add(Property.LINEAR)
        except Exception as ex:
            err += 1
            check_print_error(ex, verbosity, 1, lineno, e)
            continue

        # Do check for linear groundtruth.
        try:
            if not check_linear(gt, bitCount): assert(mode != Mode.LINEAR)
            else: exp.properties.add(Property.LINEAR_GT)
        except Exception as ex:
            err += 1
            check_print_error(ex, verbosity, 2, lineno, e)
            continue

        # Run MBA simplifier.
        try:
            start = time.perf_counter()
            s = create_simplifier(mode, bitCount, e, check)
            r = simplify(mode, s, e)

            cnt += 1
            d = time.perf_counter() - start
            timing.append(d)
            dur += d
        except (Exception, BaseException) as ex:
            err += 1
            check_print_error(ex, verbosity, 3, lineno, e)
            continue

        if r == gt:
            ok += 1
            exp.solved.add(mode)
            continue

        # Empty string is returned in case of timeout.
        if r == "":
            assert(mode == Mode.GENERAL)
            if verbosity >= 2: print('TO(line %d): "%s": "%s" <=> "%s"' % (lineno, e, r, gt))
            to += 1
            continue

        # Simplify the ground truth in order to have some standard format for comparison.
        try:
            sgt = create_simplifier(mode, bitCount, gt, check)
            rgt = simplify(mode, sgt, gt)
        except (Exception, BaseException) as ex:
            err += 1
            check_print_error(ex, verbosity, 4, lineno, gt)
            continue

        if verbosity >= 5:
            print("Result: " + r)
            print("Groundtruth: " + gt + " => " + rgt)

        # We have got the expected result.
        if r == rgt:
            ok += 1
            exp.solved.add(mode)
            continue

        # Simplification did not end in the very expected result. Check whether
        # we can verify the equivalence to the ground truth.

        diff = "(" + r + ") - (" + rgt + ")"
        try:
            sdiff = create_simplifier(mode, bitCount, diff, check)
            rdiff = simplify(mode, sdiff, diff)
        except (Exception, BaseException) as ex:
            err += 1
            check_print_error(ex, verbosity, 5, lineno, gt)
            continue

        # Verification was successful.
        if rdiff == "0":
            okz += 1
            exp.solved.add(mode)
            if verbosity >= 2: print('OKZ(line %d): "%s": "%s" <=> "%s"' % (lineno, e, r, gt))
            continue

        # Try verification again with the original expression.
        diff = "(" + e + ") - (" + gt + ")"
        try:
            sdiff = create_simplifier(mode, bitCount, diff, check)
            rdiff = simplify(mode, sdiff, diff)
        except (Exception, BaseException) as ex:
            err += 1
            check_print_error(ex, verbosity, 6, lineno, gt)
            continue

        # Now the verification succeeded.
        if rdiff == "0":
            okz += 1
            exp.solved.add(mode)
            if verbosity >= 2: print('OKZ(line %d): "%s": "%s" <=> "%s"' % (lineno, e, r, gt))
            continue

        # Try to verify using Z3, if that is enabled.
        if useZ3:
            z3res = verify_using_z3(r, rgt, bitCount, 60000)
            if z3res:
                z3 += 1
                exp.solved.add(mode)
                if verbosity >= 2: print('Z3(line %d): "%s": "%s" <=> "%s"' % (lineno, e, r, gt))
                continue

        # Finally neither simplification nor verification were successful.
        ng += 1
        if verbosity >= 2: print('NG(line %d): "%s": "%s" <=> "%s"' % (lineno, e, r, gt))

    # Print timing statistics
    if cnt > 0:
        avg = (1.0 * dur) / cnt
        print("  * average duration: %.3f s / %d" % (avg, cnt))
        q = np.quantile(timing, [0.0, 0.25, 0.5, 0.75, 1.0])
        print("  * quantiles: " + str(q))

    return ok, okz, z3, to, ng, nc, err

def print_usage():
    print("Usage: python3 tests.py")
    print("")
    print("Command line options:")
    print("    --check (-c):      enable verification of simplification results on 4-bit inputs")
    print("    --classify (-f):   additionally classify the MBAs")
    print("    --dataset (-d):    specify dataset (0-5, default: all)")
    print("    --help (-h):       print usage")
    print("    --linear (-l):     run the linear simplifier only (default: general)")
    print("    --number (-n):     limit processing to first n expressions per dataset (default: all)")
    print("    --verbosity (-v):  specify verbosity: 0 (default): summary / 1: errors / 2: errors and incorrect / 3: errors and not checked / 4: debug / 5: each line")
    print("    --z3 (-z):         enable check for semantic equivalence using Z3")

if __name__ == "__main__":
    argc = len(sys.argv)
    verbosity = 0
    mode = Mode.GENERAL
    indexList = []
    nmax = -1
    check = False
    useZ3 = False
    classify = False

    i = 0
    while i < argc - 1:
        i = i + 1
        arg = sys.argv[i]

        if arg in ["--help", "-h"]:
            print_usage()
            sys.exit(0)

        elif arg in ["--verbosity", "-v"]:
            i = i + 1
            if i == argc:
                print("Error: No verbosity given!")
                print_usage()
                sys.exit(1)

            try: verbosity = int(sys.argv[i])
            except ValueError:
                print('Error: Invalid verbosity value "%s" given!' % (sys.argv[i]))
                print_usage()
                sys.exit(1)

        elif arg in ["--linear", "-l"]: mode = Mode.LINEAR

        elif arg in ["--dataset", "-d"]:
            i = i + 1
            if i == argc:
                print("Error: No dataset indices given!")
                print_usage()
                sys.exit(1)

            try:
                indexList = [int(idx) for idx in sys.argv[i].split(',')]
            except ValueError:
                print('Error: Invalid dataset indices "%s" given!' % (sys.argv[i]))
                print_usage()
                sys.exit(1)

        elif arg in ["--number", "-n"]:
            i = i + 1
            if i == argc:
                print("Error: No number/limit given!")
                print_usage()
                sys.exit(1)

            try: nmax = int(sys.argv[i])
            except ValueError:
                print('Error: Invalid number/limit "%s" given!' % (sys.argv[i]))
                print_usage()
                sys.exit(1)

        elif arg in ["--check", "-c"]: check = True
        elif arg in ["--z3", "-z"]: z3 = True
        elif arg in ["--classify", "-f"]: classify = True

        else:
            print("Error: Unknown command line option!")
            print_usage()
            sys.exit(1)

    if indexList:
        datasets = [datasets[i] for i in indexList]
    print('Got %d datasets to test..., mode %s' % (len(datasets), mode.name))

    for ds in datasets:
        if classify:
            path = os.path.join(currentdir, "datasets", ds.fname)
            count, linear, nonlinear, mixed, bitwise, vnumber_min, vnumber_max, vnumber_avg, alt_min, alt_max, alt_avg, strlen_min, strlen_max, strlen_avg, nodes_min, nodes_max, nodes_avg = classify_dataset(path, ds.bitCount)
            print('------------- %s: %d bitwise, %d linear, %d nonlinear, %d mixed / %d (%d to %d vars, %d to %d nodes / %2.f, %d to %d alt / %.2f)' % (ds, bitwise, linear, nonlinear, mixed, count, vnumber_min, vnumber_max, nodes_min, nodes_max, nodes_avg, alt_min, alt_max, alt_avg))
        else:
            print('------------- %s' % (ds))

        ok, okz, z3, to, ng, nc, err = process_dataset(ds.fname, ds.bitCount, mode, verbosity, nmax, check, useZ3)
        print('%s: OK %d, OKZ %d, Z3 %d, TO %d, NG %d, NC %d, err %d' % (mode.name, ok, okz, z3, to, ng, nc, err))

    total = 0
    solved = unsolved = 0
    for h, exp in experiments.items():
        if len(exp.dataset_names) > 1:
            total += len(exp.dataset_names)
        else: total += 1

        if exp.solved: solved += 1
        else: unsolved += 1

    print('Got %d unique experiments, %d total' % (len(experiments), total))
    print('%d solved, %d unsolved' % (solved, unsolved))

    print()
    print('Unsolved:')
    for h, exp in experiments.items():
        if not exp.solved:
            s = create_simplifier(Mode.GENERAL, 64, exp.expression)
            r = simplify(Mode.GENERAL, s, exp.expression)

            sgt = create_simplifier(Mode.GENERAL, 64, exp.groundtruth)
            rgt = simplify(Mode.GENERAL, sgt, exp.groundtruth)

            print("Expression: " + exp.expression)
            print("Result: " + r)
            print("Groundtruth: " + exp.groundtruth + " => " + rgt)
            print()

    sys.exit(0)
