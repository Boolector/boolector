#!/bin/bash

if [ $# -ne 1 ]; then
  echo "No setup directory specified"
  echo "$(basename $0) <setup-dir>"
  exit 1
fi

SETUP_DIR=$1

mkdir -p ${SETUP_DIR}

PICOSAT_DIR=${SETUP_DIR}/picosat

# Download and build PicoSAT
mkdir ${PICOSAT_DIR}
cd ${PICOSAT_DIR}
wget http://fmv.jku.at/picosat/picosat-965.tar.gz
tar xzf picosat-965.tar.gz
mv picosat-965/* .
rmdir picosat-965
./configure.sh #--shared
make -j2
