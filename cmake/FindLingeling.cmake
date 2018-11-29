# Find Lingeling
# Lingeling_FOUND - found Lingeling lib
# Lingeling_INCLUDE_DIR - the Lingeling include directory
# Lingeling_LIBRARIES - Libraries needed to use Lingeling

if(Lingeling_ROOT_DIR)
  message(STATUS "Lingeling root directory: ${Lingeling_ROOT_DIR}")
  set(GIVEN_Lingeling_ROOT_DIR TRUE)
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/lingeling)
  set(Lingeling_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/lingeling)
  set(GIVEN_Lingeling_ROOT_DIR FALSE)
else()
  set(Lingeling_ROOT_DIR ${PROJECT_SOURCE_DIR}/../lingeling)
  set(GIVEN_Lingeling_ROOT_DIR FALSE)
endif()

find_path(Lingeling_INCLUDE_DIR
  NAMES lglib.h
  PATHS "${Lingeling_ROOT_DIR}"
  NO_DEFAULT_PATH
  )

find_library(Lingeling_LIBRARIES
  NAMES lgl
  PATHS "${Lingeling_ROOT_DIR}"
  NO_DEFAULT_PATH
  )


include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Lingeling
  DEFAULT_MSG Lingeling_INCLUDE_DIR Lingeling_LIBRARIES)

mark_as_advanced(Lingeling_INCLUDE_DIR Lingeling_LIBRARIES)
if(Lingeling_LIBRARIES)
  message(STATUS "Found Lingeling library: ${Lingeling_LIBRARIES}")
endif()
