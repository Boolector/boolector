# Find PicoSAT
# PICOSAT_FOUND - found PicoSAT lib
# PICOSAT_INCLUDE_DIR - the PicoSAT include directory
# PICOSAT_LIBRARIES - Libraries needed to use PicoSAT

if(PICOSAT_ROOT_DIR)
  message(STATUS "PicoSAT root directory: ${PICOSAT_ROOT_DIR}")
  set(GIVEN_PICOSAT_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/picosat)
  set(PICOSAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/picosat)
  set(GIVEN_PICOSAT_ROOT_DIR FALSE)
else()
  set(PICOSAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/../picosat)
  set(GIVEN_PICOSAT_ROOT_DIR FALSE)
endif()

find_path(PICOSAT_INCLUDE_DIR
  NAMES picosat.h
  PATHS "${PICOSAT_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

# Prefer shared libraries if SHARED is enabled
if(SHARED)
  set(libsuffix "so")
else()
  set(libsuffix "a")
endif()

find_library(PICOSAT_LIBRARIES
  NAMES "libpicosat.${libsuffix}" picosat
  PATHS "${PICOSAT_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(PICOSAT PICOSAT_INCLUDE_DIR PICOSAT_LIBRARIES)

mark_as_advanced(PICOSAT_INCLUDE_DIR PICOSAT_LIBRARIES)
