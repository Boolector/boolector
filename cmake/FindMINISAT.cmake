# Find MiniSAT
# MINISAT_FOUND - found MiniSat lib
# MINISAT_INCLUDE_DIR - the MiniSat include directory
# MINISAT_LIBRARIES - Libraries needed to use MiniSat

if(MINISAT_ROOT_DIR)
  message(STATUS "MiniSAT root directory: ${MINISAT_ROOT_DIR}")
  set(GIVEN_MINISAT_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/minisat)
  set(MINISAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/minisat)
  set(GIVEN_MINISAT_ROOT_DIR FALSE)
else()
  set(MINISAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/../minisat)
  set(GIVEN_MINISAT_ROOT_DIR FALSE)
endif()

find_path(MINISAT_INCLUDE_DIR
  NAMES minisat/simp/SimpSolver.h
  PATHS "${MINISAT_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

if(SHARED)
  set(libdir "dynamic/lib")
else()
  set(libdir "release/lib")
endif()

find_library(MINISAT_LIBRARIES
  NAMES minisat libminisat
  PATHS "${MINISAT_ROOT_DIR}/build/${libdir}"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MINISAT MINISAT_INCLUDE_DIR MINISAT_LIBRARIES)

mark_as_advanced(MINISAT_INCLUDE_DIR MINISAT_LIBRARIES)
