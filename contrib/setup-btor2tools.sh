#!/bin/bash

SETUP_DIR=$1
if [ -z "$SETUP_DIR" ]; then
  SETUP_DIR="./deps"
fi

mkdir -p ${SETUP_DIR}

BTOR2TOOLS_DIR=${SETUP_DIR}/btor2tools

# Download and build btor2tools
git clone --depth 1 https://github.com/Boolector/btor2tools.git ${BTOR2TOOLS_DIR}
cd ${BTOR2TOOLS_DIR}
case "$(uname -s)" in
   CYGWIN*|MINGW32*|MSYS*)
     revision=8c150b3
     echo ""
     echo " *** WARNING: Building btor2tools on Windows relies on a specific"
     echo " ***          revision (${revision})."
     echo " ***          This version of Boolector may be built against an"
     echo " ***          older version of btor2tools."
     echo ""
     git reset --hard "${revision}"
     patch -p1 < ../../contrib/windows_patches/btor2tools_"${revision}".patch
     ;;
esac
./configure.sh -fPIC
make -j2
