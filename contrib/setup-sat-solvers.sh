#!/bin/bash

if [ $# -ne 1 ]; then
  echo "No setup directory specified"
  echo "$(basename $0) <setup-dir>"
  exit 1
fi

SETUP_DIR=$1

mkdir -p ${SETUP_DIR}

SETUP_DIR=$(readlink -f ${SETUP_DIR})
CADICAL_DIR=${SETUP_DIR}/cadical
LINGELING_DIR=${SETUP_DIR}/lingeling
MINISAT_DIR=${SETUP_DIR}/minisat
PICOSAT_DIR=${SETUP_DIR}/picosat

NPROC=2
if hash nproc; then
  NPROC=$(nproc)
fi


# Download and build CaDiCaL
git clone --depth 1 https://github.com/arminbiere/cadical.git ${CADICAL_DIR}
cd ${CADICAL_DIR}
#CXXFLAGS="-fPIC"
./configure
make -j${NPROC}

# Download and build Lingeling
git clone --depth 1 https://github.com/arminbiere/lingeling.git ${LINGELING_DIR}
cd ${LINGELING_DIR}
./configure.sh #-fPIC
make -j${NPROC}

# Download and build MiniSat
git clone --depth 1 https://github.com/niklasso/minisat.git ${MINISAT_DIR}
cd ${MINISAT_DIR}
make -j${NPROC}

# Download and build PicoSAT
mkdir ${PICOSAT_DIR}
cd ${PICOSAT_DIR}
wget http://fmv.jku.at/picosat/picosat-965.tar.gz
tar xzf picosat-965.tar.gz
mv picosat-965/* .
rmdir picosat-965
./configure.sh #--shared
make -j${NPROC}
