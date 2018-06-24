# Find CaDiCaL
# CADICAL_FOUND - found CaDiCaL lib
# CADICAL_INCLUDE_DIR - the CaDiCaL include directory
# CADICAL_LIBRARIES - Libraries needed to use CaDiCaL

if(CADICAL_ROOT_DIR)
  message(STATUS "CaDiCaL root directory: ${CADICAL_ROOT_DIR}")
  set(GIVEN_CADICAL_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/cadical)
  set(CADICAL_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/cadical)
  set(GIVEN_CADICAL_ROOT_DIR FALSE)
else()
  set(CADICAL_ROOT_DIR ${PROJECT_SOURCE_DIR}/../cadical)
  set(GIVEN_CADICAL_ROOT_DIR FALSE)
endif()

find_path(CADICAL_INCLUDE_DIR
  NAMES cadical.hpp
  PATHS "${CADICAL_ROOT_DIR}/src"
  NO_DEFAULT_PATH
  )

# Prefer shared libraries if SHARED is enabled
if(SHARED)
  set(libsuffix "so")
else()
  set(libsuffix "a")
endif()

find_library(CADICAL_LIBRARIES
  NAMES "libcadical.${libsuffix}" cadical
  PATHS "${CADICAL_ROOT_DIR}/build"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CADICAL CADICAL_INCLUDE_DIR CADICAL_LIBRARIES)

mark_as_advanced(CADICAL_INCLUDE_DIR CADICAL_LIBRARIES)
