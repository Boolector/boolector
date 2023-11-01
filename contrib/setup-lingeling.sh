#!/usr/bin/env bash

# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

set -e -o pipefail

source "$(dirname "$0")/setup-utils.sh"

LINGELING_DIR=${DEPS_DIR}/lingeling
COMMIT_ID="7d5db72420b95ab356c98ca7f7a4681ed2c59c70"

download_github "arminbiere/lingeling" "$COMMIT_ID" "$LINGELING_DIR"
cd "${LINGELING_DIR}"

if is_windows; then
  component="Lingeling"
  last_patch_date="20190110"
  test_apply_patch "${component}" "${last_patch_date}"
elif is_macos; then
  component="Lingeling"
  last_patch_date="20230912"
  test_apply_patch "${component}" "${last_patch_date}"
fi

if is_macos; then
  rm -rf x86_64 arm64
  if test -f makefile; then
    make clean
  fi
  ./configure.sh -fPIC -arch x86_64
  make -j${NPROC}
  mkdir -p x86_64
  cp liblgl.a x86_64

  make clean
  ./configure.sh -fPIC -arch arm64
  make -j${NPROC}
  mkdir -p arm64
  cp liblgl.a arm64

  lipo -create -output liblgl.a x86_64/liblgl.a arm64/liblgl.a
else
  ./configure.sh -fPIC
  make -j${NPROC}
fi
install_lib liblgl.a
install_include lglib.h
