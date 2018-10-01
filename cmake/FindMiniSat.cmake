# Find MiniSAT
# MiniSat_FOUND - found MiniSat lib
# MiniSat_INCLUDE_DIR - the MiniSat include directory
# MiniSat_LIBRARIES - Libraries needed to use MiniSat

if(MiniSat_ROOT_DIR)
  message(STATUS "MiniSAT root directory: ${MiniSat_ROOT_DIR}")
  set(GIVEN_MiniSat_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/minisat)
  set(MiniSat_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/minisat)
  set(GIVEN_MiniSat_ROOT_DIR FALSE)
else()
  set(MiniSat_ROOT_DIR ${PROJECT_SOURCE_DIR}/../minisat)
  set(GIVEN_MiniSat_ROOT_DIR FALSE)
endif()

find_path(MiniSat_INCLUDE_DIR
  NAMES minisat/simp/SimpSolver.h
  PATHS "${MiniSat_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

find_library(MiniSat_LIBRARIES
  NAMES minisat
  PATHS
    "${MiniSat_ROOT_DIR}/build/dynamic/lib"
    "${MiniSat_ROOT_DIR}/build/release/lib"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MiniSat
  DEFAULT_MSG MiniSat_INCLUDE_DIR MiniSat_LIBRARIES)

mark_as_advanced(MiniSat_INCLUDE_DIR MiniSat_LIBRARIES)
if(MiniSat_LIBRARIES)
  message(STATUS "Found MiniSat library: ${MiniSat_LIBRARIES}")
endif()
