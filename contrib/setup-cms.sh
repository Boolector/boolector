#!/bin/bash

source "$(dirname "$0")/setup-utils.sh"

CMS_DIR=${DEPS_DIR}/cryptominisat

# Download and build CryptoMinisat
version="5.6.3"
wget https://github.com/msoos/cryptominisat/archive/$version.tar.gz -O cryptominisat-$version.tar.gz
tar xfvz cryptominisat-$version.tar.gz
rm cryptominisat-$version.tar.gz
mv cryptominisat-$version ${CMS_DIR}
cd ${CMS_DIR}
mkdir build
cd build
cmake -DENABLE_PYTHON_INTERFACE=OFF \
      -DSTATICCOMPILE=ON \
      -DNOM4RI=ON \
      -DCMAKE_INSTALL_PREFIX="${INSTALL_DIR}" \
      ..
make libcryptominisat5 -j${NPROC}
make install
