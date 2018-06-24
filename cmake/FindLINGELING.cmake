# Find Lingeling
# LINGELING_FOUND - found Lingeling lib
# LINGELING_INCLUDE_DIR - the Lingeling include directory
# LINGELING_LIBRARIES - Libraries needed to use Lingeling

if(LINGELING_ROOT_DIR)
  message(STATUS "Lingeling root directory: ${LINGELING_ROOT_DIR}")
  set(GIVEN_LINGELING_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/lingeling)
  set(LINGELING_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/lingeling)
  set(GIVEN_LINGELING_ROOT_DIR FALSE)
else()
  set(LINGELING_ROOT_DIR ${PROJECT_SOURCE_DIR}/../lingeling)
  set(GIVEN_LINGELING_ROOT_DIR FALSE)
endif()

find_path(LINGELING_INCLUDE_DIR
  NAMES lglib.h
  PATHS "${LINGELING_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

# Prefer shared libraries if SHARED is enabled
if(SHARED)
  set(libsuffix "so")
else()
  set(libsuffix "a")
endif()

find_library(LINGELING_LIBRARIES
  NAMES "liblgl.${libsuffix}" lgl
  PATHS "${LINGELING_ROOT_DIR}"
  NO_DEFAULT_PATH
  )


include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LINGELING LINGELING_INCLUDE_DIR LINGELING_LIBRARIES)

mark_as_advanced(LINGELING_INCLUDE_DIR LINGELING_LIBRARIES)
