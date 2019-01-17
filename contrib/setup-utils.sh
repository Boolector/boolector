#!/bin/bash

# This script defines common utility functions used by the contrib/setup-*.sh
# scripts.

die () {
  echo "*** error: $*" 1>&2
  exit 1
}

[ ! -e src/boolector.c ] && die "$0 not called from Boolector base directory"

DEPS_DIR="$(pwd)/deps"
INSTALL_DIR="${DEPS_DIR}/install"
INSTALL_LIB_DIR="${INSTALL_DIR}/lib"
INSTALL_INCLUDE_DIR="${INSTALL_DIR}/include"
INSTALL_BIN_DIR="${INSTALL_DIR}/bin"

if type nproc > /dev/null 2>&1; then
  NPROC=$(nproc)
elif [ "$(uname -s)" == "Darwin" ]; then
  NPROC=$(sysctl -n hw.physicalcpu)
else
  NPROC=2
fi


mkdir -p "${DEPS_DIR}"
mkdir -p "${INSTALL_LIB_DIR}"
mkdir -p "${INSTALL_INCLUDE_DIR}"
mkdir -p "${INSTALL_BIN_DIR}"

function install_lib
{
  cp "$1" "${INSTALL_DIR}/lib"
}

function install_include
{
  include="$1"
  subdir="$2"
  if [ -n "$subdir" ]; then
    mkdir -p "${INSTALL_INCLUDE_DIR}/$subdir"
  fi
  cp "$include" "${INSTALL_INCLUDE_DIR}/$subdir"
}

function install_bin
{
  cp "$1" "${INSTALL_BIN_DIR}"
}
