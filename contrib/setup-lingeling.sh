#!/bin/bash

SETUP_DIR=$1
if [ -z "$SETUP_DIR" ]; then
  SETUP_DIR="./deps"
fi

mkdir -p ${SETUP_DIR}

LINGELING_DIR=${SETUP_DIR}/lingeling

# Download and build Lingeling
git clone --depth 1 https://github.com/arminbiere/lingeling.git ${LINGELING_DIR}
cd ${LINGELING_DIR}
case "$(uname -s)" in
   CYGWIN*|MINGW32*|MSYS*)
     revision=03b4860
     echo ""
     echo " *** WARNING: Building Lingeling on Windows relies on a specific"
     echo " ***          revision (${revision})."
     echo " ***          This version of Boolector may be built against an"
     echo " ***          older version of Lingeling."
     echo ""
     git reset --hard "${revision}"
     patch -p1 < ../../contrib/windows_patches/lingeling_"${revision}".patch
     ;;
esac
./configure.sh -fPIC
make -j2
