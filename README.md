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


Website
-------------------------------------------------------------------------------

More information about Boolector is available at: https://boolector.github.io

Download
-------------------------------------------------------------------------------

The latest version of Boolector is available on GitHub:
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

### Windows 32-bit on Windows 64-bit

For build and installation instructions of a Boolector Windows 32-bit build
on a Windows 64-bit system, see file [COMPILING_WIN32.md](
    https://github.com/Boolector/boolector/blob/master/COMPILING_WIN32.md).

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

Contributing
-------------------------------------------------------------------------------

Boolector is distributed under the MIT license
(see [COPYING](https://github.com/Boolector/boolector/blob/master/COPYING)
file).
By submitting a contribution you automatically accept the conditions described
in [COPYING](https://github.com/Boolector/boolector/blob/master/COPYING).
Additionally, we ask you to certify that you have the right to submit such
contributions.
To manage this process we use a mechanism known as
[Developer Certificate of Origin](https://developercertificate.org), which
can be acknowledged by signing-off your commits with `git commit -s`.
We require all pull requests to be squashed into a single commit and
signed-off.


```
Developer Certificate of Origin
Version 1.1

Copyright (C) 2004, 2006 The Linux Foundation and its contributors.
1 Letterman Drive
Suite D4700
San Francisco, CA, 94129

Everyone is permitted to copy and distribute verbatim copies of this
license document, but changing it is not allowed.


Developer's Certificate of Origin 1.1

By making a contribution to this project, I certify that:

(a) The contribution was created in whole or in part by me and I
    have the right to submit it under the open source license
    indicated in the file; or

(b) The contribution is based upon previous work that, to the best
    of my knowledge, is covered under an appropriate open source
    license and I have the right under that license to submit that
    work with modifications, whether created in whole or in part
    by me, under the same open source license (unless I am
    permitted to submit under a different license), as indicated
    in the file; or

(c) The contribution was provided directly to me by some other
    person who certified (a), (b) or (c) and I have not modified
    it.

(d) I understand and agree that this project and the contribution
    are public and that a record of the contribution (including all
    personal information I submit with it, including my sign-off) is
    maintained indefinitely and may be redistributed consistent with
    this project or the open source license(s) involved.
```
