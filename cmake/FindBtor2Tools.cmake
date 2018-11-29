# Find Btor2Tools
# Btor2Tools_FOUND - found Btor2Tools lib
# Btor2Tools_INCLUDE_DIR - the Btor2Tools include directory
# Btor2Tools_LIBRARIES - Libraries needed to use Btor2Tools

if(Btor2Tools_ROOT_DIR)
  message(STATUS "Btor2Tools root directory: ${Btor2Tools_ROOT_DIR}")
elseif(EXISTS ${PROJECT_SOURCE_DIR}/deps/btor2tools)
  set(Btor2Tools_ROOT_DIR ${PROJECT_SOURCE_DIR}/deps/btor2tools)
else()
  set(Btor2Tools_ROOT_DIR ${PROJECT_SOURCE_DIR}/../btor2tools)
endif()

find_path(Btor2Tools_INCLUDE_DIR
  NAMES btor2parser/btor2parser.h
  PATHS "${Btor2Tools_ROOT_DIR}/src"
  NO_DEFAULT_PATH
  )

find_library(Btor2Tools_LIBRARIES
  NAMES btor2parser
  PATHS "${Btor2Tools_ROOT_DIR}/build"
  NO_DEFAULT_PATH
  )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Btor2Tools
  DEFAULT_MSG Btor2Tools_INCLUDE_DIR Btor2Tools_LIBRARIES)

mark_as_advanced(Btor2Tools_INCLUDE_DIR Btor2Tools_LIBRARIES)
if(Btor2Tools_LIBRARIES)
  message(STATUS "Found Btor2Tools library: ${Btor2Tools_LIBRARIES}")
endif()
