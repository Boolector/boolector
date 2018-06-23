#!/bin/bash

SETUP_DIR=$1
if [ -z "$SETUP_DIR" ]; then
  SETUP_DIR="./deps"
fi

mkdir -p ${SETUP_DIR}

BTOR2TOOLS_DIR=${SETUP_DIR}/btor2tools

# Download and build CaDiCaL
git clone --depth 1 https://github.com/Boolector/btor2tools.git ${BTOR2TOOLS_DIR}
cd ${BTOR2TOOLS_DIR}
./configure.sh -fPIC
make -j2
