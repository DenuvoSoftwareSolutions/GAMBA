#!/usr/bin/python3

import sys
import os
import inspect

currentdir = os.path.dirname(os.path.abspath(inspect.getfile(inspect.currentframe())))
parentdir = os.path.dirname(currentdir)
sys.path.insert(0, os.path.join(parentdir, "src", "utils"))
from classify import classify_mba
from node import NodeState

# Each dataset has a name, a file name and a number of bits.
class DataSet:
    def __init__(self, fname, name=None, bitCount=64):
        self.fname = fname
        self.name = name if name else fname.split('.')[0]
        self.bitCount = bitCount

    def __str__(self):
        if self.name: return self.name
        else: return self.fname

datasets = [
    DataSet('neureduce.txt'),           # 0
    DataSet('mba_obf_linear.txt'),      # 1
    DataSet('mba_obf_nonlinear.txt'),   # 2
    DataSet('syntia.txt'),              # 3
    DataSet('mba_flatten.txt'),         # 4
    DataSet('qsynth_ea.txt'),           # 5
    DataSet('bonus/loki_tiny.txt')      # 6
]

def classify_dataset(fname, bitCount=64, types=[]):
    f = open(fname, 'rt')

    # Line number in file.
    lineno = 0

    count = 0
    vnumber = 0
    vnumber_min = vnumber_max = None
    alternations = 0
    alt_min = alt_max = None
    stringlen = 0
    strlen_min = strlen_max = None
    nodes_min = nodes_max = None
    nodes = 0
    mixed = 0
    linear = 0
    nonlinear = 0
    bitwise = 0

    if not types: types = ['linear', 'poly', 'nonpoly']

    for line in f.readlines():
        lineno += 1

        # Ignore comments.
        if line.startswith('#'):
            continue

        # Split line: expression, ground truth [, whatever, ...]
        try: e, gt = line.split(',')[:2]
        except ValueError as ex: continue

        vn, state, strlen, n, alt, terms = classify_mba(e, bitCount)

        if state == NodeState.MIXED and 'nonpoly' in types: mixed += 1
        elif state == NodeState.LINEAR and 'linear' in types: linear += 1
        elif state == NodeState.NONLINEAR and 'poly' in types: nonlinear += 1
        elif state == NodeState.BITWISE: bitwise += 1
        else: continue

        count += 1

        vnumber += vn
        if not vnumber_min or vn < vnumber_min: vnumber_min = vn
        if not vnumber_max or vn > vnumber_max: vnumber_max = vn

        alternations += alt
        if not alt_min or alt < alt_min: alt_min = alt
        if not alt_max or alt > alt_max: alt_max = alt

        stringlen += strlen
        if not strlen_min or strlen < strlen_min: strlen_min = strlen
        if not strlen_max or strlen > strlen_max: strlen_max = strlen

        nodes += n
        if not nodes_min or n < nodes_min: nodes_min = n
        if not nodes_max or n > nodes_max: nodes_max = n

    return count, linear, nonlinear, mixed, bitwise, \
           vnumber_min, vnumber_max, vnumber / count, \
           alt_min, alt_max, alternations / count, \
           strlen_min, strlen_max, stringlen / count, \
           nodes_min, nodes_max, nodes / count
