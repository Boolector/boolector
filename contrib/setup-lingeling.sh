#!/usr/bin/env bash

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

LINGELING_DIR=${DEPS_DIR}/lingeling

rm -rf ${LINGELING_DIR}

# Download and build Lingeling
git clone --depth 1 https://github.com/arminbiere/lingeling.git ${LINGELING_DIR}
cd ${LINGELING_DIR}

if is_windows; then
  component="Lingeling"
  last_patch_date="20190110"
  test_apply_patch "${component}" "${last_patch_date}"
fi

./configure.sh -fPIC
make -j${NPROC}
install_lib liblgl.a
install_include lglib.h
