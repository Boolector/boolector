#!/bin/bash

if [ $# -ne 1 ]; then
  echo "No setup directory specified"
  echo "$(basename $0) <setup-dir>"
  exit 1
fi

SETUP_DIR=$1

mkdir -p ${SETUP_DIR}

SETUP_DIR=$(readlink -f ${SETUP_DIR})
LINGELING_DIR=${SETUP_DIR}/lingeling

NPROC=2
if hash nproc; then
  NPROC=$(nproc)
fi

# Download and build Lingeling
git clone --depth 1 https://github.com/arminbiere/lingeling.git ${LINGELING_DIR}
cd ${LINGELING_DIR}
./configure.sh #-fPIC
make -j${NPROC}
