# Find PicoSAT
# PicoSAT_FOUND - found PicoSAT lib
# PicoSAT_INCLUDE_DIR - the PicoSAT include directory
# PicoSAT_LIBRARIES - Libraries needed to use PicoSAT

if(PicoSAT_ROOT_DIR)
  message(STATUS "PicoSAT root directory: ${PicoSAT_ROOT_DIR}")
  set(GIVEN_PicoSAT_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/picosat)
  set(PicoSAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/picosat)
  set(GIVEN_PicoSAT_ROOT_DIR FALSE)
else()
  set(PicoSAT_ROOT_DIR ${PROJECT_SOURCE_DIR}/../picosat)
  set(GIVEN_PicoSAT_ROOT_DIR FALSE)
endif()

find_path(PicoSAT_INCLUDE_DIR
  NAMES picosat.h
  PATHS "${PicoSAT_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

find_library(PicoSAT_LIBRARIES
  NAMES picosat
  PATHS "${PicoSAT_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(PicoSAT
  DEFAULT_MSG PicoSAT_INCLUDE_DIR PicoSAT_LIBRARIES)

mark_as_advanced(PicoSAT_INCLUDE_DIR PicoSAT_LIBRARIES)
if(PicoSAT_LIBRARIES)
  message(STATUS "Found PicoSAT library: ${PicoSAT_LIBRARIES}")
endif()
