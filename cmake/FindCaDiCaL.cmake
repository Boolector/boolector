# Find CaDiCaL
# CaDiCaL_FOUND - found CaDiCaL lib
# CaDiCaL_INCLUDE_DIR - the CaDiCaL include directory
# CaDiCaL_LIBRARIES - Libraries needed to use CaDiCaL

if(CaDiCaL_ROOT_DIR)
  message(STATUS "CaDiCaL root directory: ${CaDiCaL_ROOT_DIR}")
  set(GIVEN_CaDiCaL_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/cadical)
  set(CaDiCaL_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/cadical)
  set(GIVEN_CaDiCaL_ROOT_DIR FALSE)
else()
  set(CaDiCaL_ROOT_DIR ${PROJECT_SOURCE_DIR}/../cadical)
  set(GIVEN_CaDiCaL_ROOT_DIR FALSE)
endif()

find_path(CaDiCaL_INCLUDE_DIR
  NAMES cadical.hpp
  PATHS "${CaDiCaL_ROOT_DIR}/src"
  NO_DEFAULT_PATH
  )

find_library(CaDiCaL_LIBRARIES
  NAMES cadical
  PATHS "${CaDiCaL_ROOT_DIR}/build"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CaDiCaL
  DEFAULT_MSG CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)

mark_as_advanced(CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARIES)
if(CaDiCaL_LIBRARIES)
  message(STATUS "Found CaDiCaL library: ${CaDiCaL_LIBRARIES}")
endif()
