# Find MiniSAT

if(MINISAT_ROOT_DIR)
  message(STATUS "MiniSAT root directory: ${MINISAT_ROOT_DIR}")
  set(GIVEN_MINISAT_ROOT_DIR TRUE)
else()
  set(MINISAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/../minisat)
  set(GIVEN_MINISAT_ROOT_DIR FALSE)
endif()

find_path(MINISAT_INCLUDE_DIR
  NAMES SimpSolver.h
  PATHS "${MINISAT_ROOT_DIR}/minisat/simp"
  NO_DEFAULT_PATH
  )

find_library(MINISAT_LIBRARIES
  NAMES minisat libminisat
  PATHS "${MINISAT_ROOT_DIR}/build/release/lib"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MINISAT MINISAT_INCLUDE_DIR MINISAT_LIBRARIES)

mark_as_advanced(MINISAT_INCLUDE_DIR MINISAT_LIBRARIES)
