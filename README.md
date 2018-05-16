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
The documentation of its API can be found [here]().


Download
-------------------------------------------------------------------------------

  The latest version of Boolector can be found on GitHub:
  https://github.com/boolector/boolector

Build
-------------------------------------------------------------------------------

Boolector can be built with support for the SAT solvers
[Lingeling](http://fmv.jku.at/lingeling),
[CaDiCaL](https://github.com/arminbiere/cadical),
[PicoSAT](http://fmv.jku.at/picosat) and
[MiniSAT](https://github.com/niklasso/minisat).  
It is required to place any of these solvers in a directory on the same level
as the Boolector source directory. You can build Boolector with support for
multiple SAT solvers. Script `configure.sh` searches automatically for the
SAT solver directories and expects them to be named as `lingeling`, `cadical`,
`picosat` and `minisat`, respectively.

Note that using MiniSAT will force `libboolector.a` to depend not only on
`libz.so` but also on `libstdc++.so`. Thus, if you want to link
`libboolector.a` with MiniSAT backend against your own programs,
you need to use `-lz -lstdc++` as linking options.

Boolector has one other external dependency,
the [BTOR2 format tools package](https://github.com/boolector/btor2tools).
As with the SAT solvers, make sure to clone this repository into directory
`btor2tools` on the same level as the Boolector repository.

### Linux and Unix-like OS

Assume that we build Boolector with support for Lingeling:
```
# Download and build Lingeling
wget -c http://fmv.jku.at/lingeling/lingeling-bbc-9230380-160707.tar.gz
tar xvf lingeling-bbc-9230380-160707.tar.gz
mv lingeling-bbc-9230380-160707 lingeling
cd lingeling && ./configure.sh && make && cd -

# Download and build btor2tools
git clone https://github.com/boolector/btor2tools
cd btor2tools && ./configure.sh && make && cd -

# Download and build Boolector
git clone https://github.com/boolector/boolector
cd boolector && ./configure.sh && make && cd -
```

All binaries (boolector, btormc, btormbt, btoruntrace) are generated into
directory `boolector/bin`,
and all libraries (libboolector.a, libboolector.so) are generated into
directory `boolector/build`.

For more build configuration options of Boolector, see `configure.sh -h`.

To build Boolector with Python bindings, `btor2tools` and SAT solvers must
be compiled with flag `-fPIC`
(see build instructions of these tools for more details on how to build as
shared library).  
Then, from Boolector's root directory configure and build Boolector as follows:
```
./configure.sh -python
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
`examples/api/c` and the [API documentation]().  
To build all examples in `examples/api/c` issue:
```
cd examples/api/c
make
```

For examples and instructions on how to use Boolector's Python API, refer to
`src/api/python/api_usage_examples.py`
and the [API documentation]().  
To run `api_usage_examples.py`, from Boolector's root directory issue:
```
PYTHONPATH="build" python examples/api/python/api_usage_examples.py 
```
