#!/usr/bin/env bash

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

CADICAL_DIR=${DEPS_DIR}/cadical

rm -rf ${CADICAL_DIR}

# Download and build CaDiCaL
git clone --depth 1 https://github.com/arminbiere/cadical.git ${CADICAL_DIR}
cd ${CADICAL_DIR}

if is_windows; then
  component="CaDiCaL"
  last_patch_date="20190730"
  test_apply_patch "${component}" "${last_patch_date}"
  EXTRA_FLAGS="-q"
  #
  # CaDiCaL performs configure checks with -Werror, which fails on Windows as
  # fPIC is not valid, so we set CXXFLAGS per-platform
  #
  export CXXFLAGS=""
else
  export CXXFLAGS="-fPIC"
fi

./configure ${EXTRA_FLAGS}
make -j${NPROC}
install_lib build/libcadical.a
install_include src/ccadical.h
