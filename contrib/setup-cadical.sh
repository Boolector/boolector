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

CADICAL_DIR=${DEPS_DIR}/cadical
COMMIT_ID="cb89cbfa16f47cb7bf1ec6ad9855e7b6d5203c18"

TAR_ARGS=""
if is_windows; then
  # Extracting a symlink to a non-existing file fails on Windows, so we exclude it
  TAR_ARGS="--exclude src/makefile"
fi

download_github "arminbiere/cadical" "$COMMIT_ID" "$CADICAL_DIR" "$TAR_ARGS"
cd "${CADICAL_DIR}"

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
elif is_macos; then
  component="CaDiCaL"
  last_patch_date="20230912"
  test_apply_patch "${component}" "${last_patch_date}"
  export CXXFLAGS="-fPIC"
else
  export CXXFLAGS="-fPIC"
fi

if is_macos; then
  rm -rf build.x86_64 build.arm64
  ./configure ${EXTRA_FLAGS} -arch x86_64
  make -j${NPROC}
  mv build build.x86_64
  ./configure ${EXTRA_FLAGS} -arch arm64
  make -j${NPROC}
  mv build build.arm64
  mkdir -p build
  lipo -create -output build/libcadical.a \
    build.x86_64/libcadical.a build.arm64/libcadical.a
else
  ./configure ${EXTRA_FLAGS}
  make -j${NPROC}
fi

install_lib build/libcadical.a
install_include src/ccadical.h
