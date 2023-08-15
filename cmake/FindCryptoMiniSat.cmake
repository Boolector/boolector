# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#

# Find CryptoMiniSat
# CryptoMiniSat_FOUND - found CryptoMiniSat lib
# CryptoMiniSat_INCLUDE_DIR - the CryptoMiniSat include directory
# CryptoMiniSat_LIBRARIES - Libraries needed to use CryptoMiniSat

find_path(CryptoMiniSat_INCLUDE_DIR NAMES cryptominisat5/cryptominisat.h)
find_library(CryptoMiniSat_LIBRARIES NAMES cryptominisat5)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CryptoMiniSat
  DEFAULT_MSG CryptoMiniSat_INCLUDE_DIR CryptoMiniSat_LIBRARIES)

mark_as_advanced(CryptoMiniSat_INCLUDE_DIR CryptoMiniSat_LIBRARIES)
if(CryptoMiniSat_LIBRARIES)
  message(STATUS "Found CryptoMiniSat library: ${CryptoMiniSat_LIBRARIES}")
endif()
