#!/bin/bash

if [ $# -ne 1 ]; then
  echo "No setup directory specified"
  echo "$(basename $0) <setup-dir>"
  exit 1
fi

SETUP_DIR=$1

mkdir -p ${SETUP_DIR}

MINISAT_DIR=${SETUP_DIR}/minisat

# Download and build MiniSat
git clone --depth 1 https://github.com/niklasso/minisat.git ${MINISAT_DIR}
cd ${MINISAT_DIR}
make -j${NPROC}
