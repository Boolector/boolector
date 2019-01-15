#!/bin/bash

SETUP_DIR=$1
if [ -z "$SETUP_DIR" ]; then
  SETUP_DIR="./deps"
fi

mkdir -p ${SETUP_DIR}

CADICAL_DIR=${SETUP_DIR}/cadical

# Download and build CaDiCaL
git clone --depth 1 https://github.com/arminbiere/cadical.git ${CADICAL_DIR}
cd ${CADICAL_DIR}
case "$(uname -s)" in
   CYGWIN*|MINGW32*|MSYS*)
     revision=58331fd
     echo ""
     echo " *** WARNING: Building CaDiCaL on Windows relies on a specific"
     echo " ***          revision (${revision})."
     echo " ***          This version of Boolector may be built against an"
     echo " ***          older version of CaDiCaL."
     echo ""
     git reset --hard "${revision}"
     patch -p1 < ../../contrib/windows_patches/cadical_"${revision}".patch
     EXTRA_FLAGS="-q"
     ;;
esac
CXXFLAGS="-fPIC" ./configure ${EXTRA_FLAGS}
make -j2
