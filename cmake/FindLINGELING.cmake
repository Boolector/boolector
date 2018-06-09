# Find Lingeling

if(LINGELING_ROOT_DIR)
  message(STATUS "Lingeling root directory: ${LINGELING_ROOT_DIR}")
  set(GIVEN_LINGELING_ROOT_DIR TRUE)
else()
  set(LINGELING_ROOT_DIR ${PROJECT_SOURCE_DIR}/../lingeling)
  set(GIVEN_LINGELING_ROOT_DIR FALSE)
endif()

find_path(LINGELING_INCLUDE_DIR
  NAMES lglib.h
  PATHS "${LINGELING_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

find_library(LINGELING_LIBRARIES
  NAMES lgl liblgl
  PATHS "${LINGELING_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LINGELING LINGELING_INCLUDE_DIR LINGELING_LIBRARIES)

mark_as_advanced(LINGELING_INCLUDE_DIR LINGELING_LIBRARIES)
