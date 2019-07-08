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
WINDOWS_PATCHES_DIR="$(pwd)/contrib/windows_patches"

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

function is_windows
{
  #
  # Helper function to check if we're running under Windows, returns false
  # otherwise.
  #
  case "$(uname -s)" in
    CYGWIN*|MINGW32*|MSYS*)
      return
      ;;
  esac
  false
}

function test_apply_patch
{
  #
  # This is a function to help apply a patch, only if the patch applies
  # cleanly.
  #
  # If the patch _does not_ apply cleanly, it prints a warning and exits
  # (and therefore blocks compilation of the feature)!
  #
  local component="$1"
  local last_patch_date="$2"
  local patch_set="${WINDOWS_PATCHES_DIR}/${component}_${last_patch_date}.patch"
  patch -p1 -N --dry-run --silent < "${patch_set}" 2>/dev/null
  if [ $? -eq 0 ]; then
    #
    # Apply patch if the dry-run was successful.
    #
    patch -p1 -N < "${patch_set}"
  else
    #
    # Otherwise, print an error and bomb-out!
    #
    echo "##############################################################"
    echo "# ***Critical error***"
    echo "#"
    echo "#    Failed to patch ${component} to be Windows-compatible!"
    echo "#"
    echo "#    Please create an issue on GitHub.com:"
    echo "#"
    echo "#        https://github.com/Boolector/boolector/issues"
    echo "#"
    echo "#    Compilation *will not* continue!"
    echo "##############################################################"
    exit 1
  fi
}
