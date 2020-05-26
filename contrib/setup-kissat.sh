#!/usr/bin/env bash

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

KISSAT_DIR="${DEPS_DIR}/kissat"
version="sc2020-039805f2"

rm -rf "${KISSAT_DIR}"

# Download and build Kissat
curl -o kissat-$version.tar.xz -L "http://fmv.jku.at/kissat/kissat-$version.tar.xz"
tar xf kissat-$version.tar.xz
rm kissat-$version.tar.xz
mv kissat-$version ${KISSAT_DIR}
cd ${KISSAT_DIR}

./configure -fPIC --quiet
make -j${NPROC}
install_lib build/libkissat.a
install_include src/kissat.h kissat

