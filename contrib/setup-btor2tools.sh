#!/bin/bash

source "$(dirname "$0")/setup-utils.sh"

BTOR2TOOLS_DIR=${DEPS_DIR}/btor2tools

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
make -j${NPROC}
install_lib build/libbtor2parser.a
install_include src/btor2parser/btor2parser.h btor2parser
