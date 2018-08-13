[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](https://opensource.org/licenses/MIT)
[![Build Status](https://travis-ci.org/Boolector/boolector.svg?branch=master)](https://travis-ci.org/Boolector/boolector)

Boolector
===============================================================================

Boolector is a Satisfiability Modulo Theories (SMT) solver for the theories
of fixed-size bit-vectors, arrays and uninterpreted functions.
It supports the [SMT-LIB](http://www.smt-lib.org) logics
BV,
[QF_ABV](http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_ABV),
[QF_AUFBV](http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_AUFBV),
[QF_BV](http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_BV) and
[QF_UFBV](http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_UFBV).
Boolector provides a rich C and Python API and supports incremental solving,
both with the SMT-LIB commands push and pop, and as solving under assumptions.
The documentation of its API can be found
[here](https://boolector.github.io/docs).


Download
-------------------------------------------------------------------------------

  The latest version of Boolector can be found on GitHub:
  https://github.com/boolector/boolector

Prerequisites
-------------------------------------------------------------------------------

To build Boolector from source you need:
  * cmake >= 2.8
  * gcc/clang
  * g++/clang++

To build the python module `pyboolector` you further need:
  * Cython >= 0.22


Build
-------------------------------------------------------------------------------

Boolector can be built with support for the SAT solvers
[Lingeling](http://fmv.jku.at/lingeling),
[CaDiCaL](https://github.com/arminbiere/cadical),
[PicoSAT](http://fmv.jku.at/picosat) and
[MiniSAT](https://github.com/niklasso/minisat).
To build and setup these solvers you can use the scripts
`setup-{cadical,lingeling,minisat,picosat}.sh` in the `contrib` directory.
Optionally, you can place any of these solvers in a directory on the same level
as the Boolector source directory or provide a path to `configure.sh`.
You can build Boolector with support for
multiple SAT solvers.
Note that using MiniSAT will force `libboolector.a` to depend not only on
`libz.so` but also on `libstdc++.so`. Thus, if you want to link
`libboolector.a` with MiniSAT backend against your own programs,
you need to use `-lz -lstdc++` as linking options.

Boolector has one other external dependency,
the [BTOR2 format tools package](https://github.com/boolector/btor2tools).
As with the SAT solvers, you can either use the provided script
`setup-btor2tools.sh` in `contrib` or clone the BTOR2Tools repository into
directory `btor2tools` on the same level as the Boolector repository or
provide a path to `configure.sh`.

### Linux and Unix-like OS

Assume that we build Boolector with support for Lingeling:
```
# Download and build Boolector
git clone https://github.com/boolector/boolector
cd boolector

# Download and build Lingeling
./contrib/setup-lingeling.sh

# Download and build BTOR2Tools
./contrib/setup-btor2tools.sh

# Build Boolector
./configure.sh && cd build && make
```

All binaries (boolector, btormc, btormbt, btoruntrace) are generated into
directory `boolector/build/bin`,
and all libraries (libboolector.a, libboolector.so) are generated into
directory `boolector/build/lib`.

For more build configuration options of Boolector, see `configure.sh -h`.

To build Boolector with Python bindings you need to install
[Cython](http://cython.org/),
and `btor2tools` and SAT solvers must be compiled with flag `-fPIC`
(see build instructions of these tools for more details on how to build as
shared library). The provided setup-\*.sh scripts automatically compile all
dependencies with `-fPIC`.
Then, from Boolector's root directory configure and build Boolector as follows:
```
./configure.sh --python
cd build
make
```

To build the API documentation of Boolector, it is required to install
[Sphinx](http://www.sphinx-doc.org) (>= version 1.2).
Then build Boolector and issue:
```
cd doc
make html
```
The documentation is then generated into `doc/_build/html`.
Make sure to build Boolector with Python bindings, else the documentation of
its Python API will not be included.

Usage
-------------------------------------------------------------------------------

For a list of command line options, refer to `boolector -h`.

For examples and instructions on how to use Boolector's C API, refer to
`examples/api/c` and the [API documentation](https://boolector.github.io/docs).
To build all examples in `examples/api/c` issue:
```
cd build
make examples
```

For examples and instructions on how to use Boolector's Python API, refer to
`examples/api/python/api_usage_examples.py`
and the [API documentation](https://boolector.github.io/docs).  
To run `api_usage_examples.py`, from Boolector's root directory issue:
```
PYTHONPATH="build/lib" python examples/api/python/api_usage_examples.py
```
