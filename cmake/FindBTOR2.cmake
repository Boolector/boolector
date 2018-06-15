# Find Btor2Tools
# BTOR2_FOUND - found Btor2Tools lib
# BTOR2_INCLUDE_DIR - the Btor2Tools include directory
# BTOR2_LIBRARIES - Libraries needed to use Btor2Tools

if(BTOR2_ROOT_DIR)
  message(STATUS "Btor2Tools root directory: ${BTOR2_ROOT_DIR}")
else()
  set(BTOR2_ROOT_DIR ${PROJECT_SOURCE_DIR}/../btor2tools)
endif()

find_path(BTOR2_INCLUDE_DIR
  NAMES btor2parser/btor2parser.h
  PATHS "${BTOR2_ROOT_DIR}/src"
  NO_DEFAULT_PATH
  )

find_library(BTOR2_LIBRARIES
  NAMES btor2parser libbtor2parser
  PATHS "${BTOR2_ROOT_DIR}/build"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Btor2Tools BTOR2_INCLUDE_DIR BTOR2_LIBRARIES)

mark_as_advanced(BTOR2_INCLUDE_DIR BTOR2_LIBRARIES)
