#!/usr/bin/env bash

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

BTOR2TOOLS_DIR=${DEPS_DIR}/btor2tools

rm -rf ${BTOR2TOOLS_DIR}

# Download and build btor2tools
git clone --depth 1 https://github.com/Boolector/btor2tools.git ${BTOR2TOOLS_DIR}
cd ${BTOR2TOOLS_DIR}

if is_windows; then
  component="Btor2Tools"
  last_patch_date="20190110"
  test_apply_patch "${component}" "${last_patch_date}"
fi

./configure.sh -fPIC
make -j${NPROC}
install_lib build/libbtor2parser.a
install_include src/btor2parser/btor2parser.h btor2parser
