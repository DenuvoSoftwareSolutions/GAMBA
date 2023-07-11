# GAMBA

GAMBA is a tool for the simplification of mixed Boolean-arithmetic expressions (MBAs). 
GAMBA is short for General Advanced Mixed Boolean Arithmetic simplifier.
It uses the linear algebraic simplifier [SiMBA](https://github.com/DenuvoSoftwareSolutions/SiMBA) to iteratively 
simplify linear subexpressions of a potentially nonlinear input MBA. Overall, its core ingredients are the following:

- Usage of abstract syntax trees (ASTs)
- Isolation of linear subexpressions via application of (trivial and more sophisticated) transformations
- Refactoring in order to increase the chance of building linear subexpressions that can be simplified
- Simplification of linear subexpressions using SiMBA
- Substitution logic to temporarily get rid of nontrivial constants and arithmetic operations within bitwise operations

GAMBA is based on the following [paper](paper/paper.pdf), see also the [slides](slides/slides.pdf) used for presentation:
<pre>@inproceedings{gamba2023,
    author = {Reichenwallner, Benjamin and Meerwald-Stadler, Peter},
    title = {Simplification of General Mixed Boolean-Arithmetic Expressions: GAMBA},
    address = {Delft, The Netherlands},
    year = {2023},
    month = jul,
    publisher = {IEEE},
    howpublished = {https://arxiv.org/abs/2305.06763},
    booktitle = {Proceedings of the 2nd Workshop on Robust Malware Analysis, WORMA'23, 
                 co-located with the 8th IEEE European Symposium on Security and Privacy}
}
</pre>

# Content

Two main programs are provided:

- <code>simplify_general.py</code> for the simplification of general MBAs
- <code>simplify.py</code> for the simplification of linear MBAs

Additionally, a test script is provided to reproduce the results stated in the paper.


## Usage

### Simplifying single general expressions

In order to simplify a single expression <code>expr</code>, use

    python3 src/simplify_general.py "expr"
 
 Alternatively, multiple expressions can be simplified at once, e.g.:

    python3 src/simplify_general.py "x+x" "y*y" "a&a"

In fact, each command line argument which is not an option is considered an expression to be simplified. Note that omitting the quotation marks may lead to undesired behavior. The simplification results are printed to the command line as shown in the following:

    *** Expression x+x
    *** ... simplified to 2*x
    *** Expression y*y
    *** ... simplified to y**2
    *** Expression a
    *** ... simplified to a

If option **-z** is used, the simplification results are finally verified to be semantically equivalent to the original expressions using *Z3*. This does not effect the command line output as long as the algorithm works correctly:

    python3 src/simplify_general.py "x+x" -z

If the algorithm would output a wrong result, the following error would be triggered:

    *** Expression x+x
    Error in simplification! Simplified expression is not equivalent to original one!

Additionally, a numeric validation of results with all possible inputs up to a specific bit count can be performed. This is enabled with option **-v**, followed by a maximum bit count of the used inputs:

    python3 src/simplify_general.py "x+x" -v 3

Again in case of a wrong result, the output may look like the following:

    *** Expression x+x
    *** ... verify via evaluation ... [                    ] 0%
    *** ... verification failed for input [1, 0]: orig 1, output 2


The constants occuring in GAMBA's output expressions may obviously depend on the number of bits used for constants as well as variables. This number is $64$ by default and can be set using the option **-b**:

    python3 src/simplify_general.py "-x" -b 32

By default, the constants occurring in the output are reported in the representation that is as close as possible to zero. That is, in the case above, the number -1 would remain:

    *** Expression -x
    *** ... simplified to -x

This behavior can be changed: Using option **-m**, a modulo-reduction of constants is enabled:

    python3 src/simplify_general.py "-x" -b 32 -m

Then, for a number $b$ of bits, the constants always lie between $0$ and $2^b-1$. Hence the call above would imply the following output:

    *** Expression -x
    *** ... simplified to 4294967295*x

### Simplifying single linear expressions

The file <code>src/simplify.py</code> is meant to be utilized by <code>src/simplify_general.py</code>, but can also be run isolatedly. Use command line option **-h** to see the available settings.


### Reproduction of experiments

The file <code>experiments/tests.py</code> can be used to reproduce the experiments stated in the paper. By default it runs GAMBA on 6 datasets:

    python3 experiments/tests.py

Alternatively it can be instructed to run SiMBA instead using the option **--linear** or **-l**. In that case, SiMBA is only run on MBAs with linear ground truths:

    python3 experiments/tests.py --linear

Numeric checks or checks using Z3 can be enabled via options **--check** (**-c**) or **--z3** (**-z**), resp.

The expressions are categorized depending on the simplification or verification success:

- *ok*: expressions which are simplified to the exactly same result as the corresponding ground truths
- *okz*: expressions whose equivalence to the ground truths can be verified using the algorithm (by simplifying the expression minus to the ground truth expression to 0)
- *z3*: expressions whose equivalence to the ground truths can be verified using Z3
- *to*: expressions for which the algorithm ran into a timeout
- *ng*: expressions for which simplification and verification were not successful
- *nc*: expressions for which the algorithm, in case SiMBA is used, was not run since the ground truths are not linear
- *err*: expressions for which an error occurred


### Datasets

Datasets for use with <code>experiments/tests.py</code> can be found in the directory <code>experiments/datasets/</code>.

- neureduce.txt: Use option <code>-d 0</code>; from https://github.com/fvrmatteo/NeuReduce/tree/master/dataset/linear/test/test_data.csv (with some fixes applied)
- mba_obf_linear.txt: Use option <code>-d 1</code>; from https://github.com/nhpcc502/MBA-Obfuscator/tree/main/samples/ground.linear.poly.txt (1000 linear expressions)
- mba_obf_nonlinear.txt: Use option <code>-d 2</code>; from https://github.com/nhpcc502/MBA-Obfuscator/tree/main/samples/ground.linear.poly.txt and https://github.com/nhpcc502/MBA-Obfuscator/tree/master/samples/ground.linear.nonpoly.txt (500 expressions each; with some fixes for nonpolynomial expressions)
- syntia.txt: Use option <code>-d 3</code>; from MBA-Flatten, dataset/dataset_syntia.txt
- mba_flatten.txt: Use option <code>-d 4</code>; from MBA-Flatten, first 1000 expressions from dataset/pldi_dataset_linear_MBA.txt, dataset/pldi_dataset_poly_MBA.txt, dataset/pldi_dataset_nonpoly_MBA.txt
- qsynth_ea.txt: Use option <code>-d 5</code>; from https://github.com/werew/qsynth-artifacts/tree/master/datasets/syntia/ground_truth.json

## Format of MBAs

The number of variables is in theory unbounded, but of course the runtime increases with variable count. There is no strong restriction on the notation of variables. They have to start with a letter and can contain letters, numbers and underscores. E.g., the following variable names would all be fine:
- $a$, $b$, $c$, ..., $x$, $y$, $z$, ...
- $v0$, $v1$, $v2$, ...
- $v\_0$, $v\_1$, $v\_2$, ...
- $X0$, $X1$, $X2$, ...
- $var0$, $var1$, $var2$, ...
- $var1a$, $var1b$, $var1c$, ...
- ...

The following operators are supported, ordered by their precedence in Python:
- $**$: exponentiation
- $\mathord{\sim}$, $-$: bitwise negation and unary minus
- $*$: product
- $+$, $-$: sum and difference
- <<: left shift
- &: conjunction
- $\mathbin{^\wedge}$: exclusive disjunction
- $|$: inclusive disjunction

Whitespace can be used in the input expressions. E.g., the expression <code>"x+y"</code> may alternatively be written <code>"x + y"</code>.

> Please respect the precedence of operators and use parentheses if necessary! E.g., the expressions $1 + (x|y)$ and $1 + x|y$ are not equivalent since $+$ has a higher precedence than $|$. Note that the latter is not even a linear MBA.

## Dependencies

### Z3

The SMT Solver **Z3** is required by <code>simplify_general.py</code> and <code>simplify.py</code> if the optional verification of simplified expressions is used. If this option is unused, no error is thrown even if Z3 is not installed.

Installing Z3:
- from  the Github repository: https://github.com/Z3Prover/z3
- on Debian: <code>sudo apt-get install python3-z3</code>

### NumPy

The scientific computing package **NumPy** is required due to lazyness, but not really essential for the operation.
Note: at least version 1.15.0 is required for numpy.quantile

Installing NumPy:
- from  the Github repository: https://github.com/numpy/numpy.git
- on Debian: <code>sudo apt-get install python3-numpy</code>

## License

Copyright (c) 2023 Denuvo GmbH, released under [GPLv3](LICENSE).


## Contact
- Benjamin Reichenwallner: benjamin(dot)reichenwallner(at)denuvo(dot)com
- Peter Meerwald-Stadler: peter(dot)meerwald(at)denuvo(dot)com


