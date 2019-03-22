#!/bin/bash

source "$(dirname "$0")/setup-utils.sh"

PICOSAT_DIR=${DEPS_DIR}/picosat

# Download and build PicoSAT
mkdir ${PICOSAT_DIR}
cd ${PICOSAT_DIR}
wget http://fmv.jku.at/picosat/picosat-965.tar.gz
tar xzf picosat-965.tar.gz
mv picosat-965/* .
rmdir picosat-965
case "$(uname -s)" in
   CYGWIN*|MINGW32*|MSYS*)
     patch -p1 < ../../contrib/windows_patches/picosat-965.patch
     EXTRA_FLAGS="--optimize --no-stats --no-trace"
     ;;
esac
./configure.sh --shared ${EXTRA_FLAGS}
make -j${NPROC} libpicosat.a libpicosat.so
install_lib libpicosat.a
install_lib libpicosat.so
install_include picosat.h
