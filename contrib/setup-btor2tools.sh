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

BTOR2TOOLS_DIR=${DEPS_DIR}/btor2tools
COMMIT_ID="1df768d75adfb13a8f922f5ffdd1d58e80cb1cc2"

download_github "boolector/btor2tools" "$COMMIT_ID" "$BTOR2TOOLS_DIR"
cd "${BTOR2TOOLS_DIR}"

if is_windows; then
  component="Btor2Tools"
  last_patch_date="20190110"
  test_apply_patch "${component}" "${last_patch_date}"
elif is_macos; then
  component="Btor2Tools"
  last_patch_date="20230912"
  test_apply_patch "${component}" "${last_patch_date}"
fi

if is_macos; then
  rm -rf build.x86_64 build.arm64

  ./configure.sh -fPIC -arch x86_64
  make -j${NPROC}
  mv build build.x86_64
  ./configure.sh -fPIC -arch arm64
  make -j${NPROC}
  mv build build.arm64

  mkdir -p build
  lipo -create -output build/libbtor2parser.a \
    build.x86_64/libbtor2parser.a \
    build.arm64/libbtor2parser.a
else
  ./configure.sh -fPIC
  make -j${NPROC}
fi

install_lib build/libbtor2parser.a
install_include src/btor2parser/btor2parser.h
