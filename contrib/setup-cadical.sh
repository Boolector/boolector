#!/bin/bash

if [ $# -ne 1 ]; then
  echo "No setup directory specified"
  echo "$(basename $0) <setup-dir>"
  exit 1
fi

SETUP_DIR=$1

mkdir -p ${SETUP_DIR}

CADICAL_DIR=${SETUP_DIR}/cadical

# Download and build CaDiCaL
git clone --depth 1 https://github.com/arminbiere/cadical.git ${CADICAL_DIR}
cd ${CADICAL_DIR}
#CXXFLAGS="-fPIC"
./configure
make -j2
