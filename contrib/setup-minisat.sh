#!/bin/bash

source "$(dirname "$0")/setup-utils.sh"

MINISAT_DIR=${DEPS_DIR}/minisat

# Download and build MiniSat
git clone --depth 1 https://github.com/niklasso/minisat.git ${MINISAT_DIR}
cd ${MINISAT_DIR}
make config prefix=${INSTALL_DIR} -j${NPROC}
make install
