# Find Btor2Tools
# BTOR2_FOUND - found Btor2Tools lib
# BTOR2_INCLUDE_DIR - the Btor2Tools include directory
# BTOR2_LIBRARIES - Libraries needed to use Btor2Tools

if(BTOR2_ROOT_DIR)
  message(STATUS "Btor2Tools root directory: ${BTOR2_ROOT_DIR}")
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/btor2tools)
  set(BTOR2_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/btor2tools)
else()
  set(BTOR2_ROOT_DIR ${PROJECT_SOURCE_DIR}/../btor2tools)
endif()

find_path(BTOR2_INCLUDE_DIR
  NAMES btor2parser/btor2parser.h
  PATHS "${BTOR2_ROOT_DIR}/src"
  NO_DEFAULT_PATH
  )

# Prefer shared libraries if SHARED is enabled
if(SHARED)
  set(libsuffix "so")
else()
  set(libsuffix "a")
endif()

find_library(BTOR2_LIBRARIES
  NAMES "libbtor2parser.${libsuffix}" btor2parser
  PATHS "${BTOR2_ROOT_DIR}/build"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Btor2Tools BTOR2_INCLUDE_DIR BTOR2_LIBRARIES)

mark_as_advanced(BTOR2_INCLUDE_DIR BTOR2_LIBRARIES)
