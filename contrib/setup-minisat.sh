#!/bin/bash

SETUP_DIR=$1
if [ -z "$SETUP_DIR" ]; then
  SETUP_DIR="./deps"
fi

mkdir -p ${SETUP_DIR}

MINISAT_DIR=${SETUP_DIR}/minisat

# Download and build MiniSat
git clone --depth 1 https://github.com/niklasso/minisat.git ${MINISAT_DIR}
cd ${MINISAT_DIR}
make -j${NPROC} CXXFLAGS=-fPIC
