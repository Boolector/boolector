#!/bin/bash

SETUP_DIR=$1
if [ -z "$SETUP_DIR" ]; then
  SETUP_DIR="./deps"
fi

mkdir -p ${SETUP_DIR}

PICOSAT_DIR=${SETUP_DIR}/picosat

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
make -j2
