cmake_minimum_required (VERSION 3.3)

project(Boolector)

macro(add_c_flag flag)
  check_cxx_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flagname})
    message(STATUS "Configure with flag '${flag}'")
    set(CMAKE_CC_FLAGS "${CMAKE_CC_FLAGS} ${flag}")
  endif()
endmacro()

macro(add_cxx_flag flag)
  check_cxx_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flagname})
    message(STATUS "Configure with flag '${flag}'")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
  endif()
endmacro()

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

find_package(BTOR2 REQUIRED)
message(STATUS "Found Btor2Tools headers: ${BTOR2_INCLUDE_DIR}")
set(LIBRARIES ${LIBRARIES} ${BTOR2_LIBRARIES})
include_directories(${BTOR2_INCLUDE_DIR})

find_package(LINGELING QUIET)
find_package(CADICAL QUIET)
find_package(PICOSAT QUIET)
find_package(MINISAT QUIET)

if (NOT LINGELING_FOUND
    AND NOT CADICAL_FOUND
    AND NOT PICOSAT_FOUND
    AND NOT MINISAT_FOUND)
  message(SEND_ERROR "No SAT solver found")
endif()

if (LINGELING_FOUND)
  include_directories(${LINGELING_INCLUDE_DIR})
  set(LIBRARIES ${LIBRARIES} ${LINGELING_LIBRARIES})
  message(STATUS "Found Lingeling: ${LINGELING_LIBRARIES}")
  message(STATUS "Found Lingeling headers: ${LINGELING_INCLUDE_DIR}")
elseif(GIVEN_LINGELING_ROOT_DIR)
  message(SEND_ERROR "Lingeling not found")
endif()

if (CADICAL_FOUND)
  include_directories(${CADICAL_INCLUDE_DIR})
  set(LIBRARIES ${LIBRARIES} ${CADICAL_LIBRARIES})
  message(STATUS "Found CaDiCaL: ${CADICAL_LIBRARIES}")
  message(STATUS "Found CaDiCaL headers: ${CADICAL_INCLUDE_DIR}")
elseif(GIVEN_CADICAL_ROOT_DIR)
  message(SEND_ERROR "CaDiCaL not found")
endif()

if(PICOSAT_FOUND)
  include_directories(${PICOSAT_INCLUDE_DIR})
  set(LIBRARIES ${LIBRARIES} ${PICOSAT_LIBRARIES})
  message(STATUS "Found PicoSAT: ${PICOSAT_LIBRARIES}")
  message(STATUS "Found PicoSAT headers: ${PICOSAT_INCLUDE_DIR}")
elseif(GIVEN_PICOSAT_ROOT_DIR)
  message(SEND_ERROR "PicoSAT not found")
endif()

if (MINISAT_FOUND)
  if (${MINISAT_INCLUDE_DIR} STREQUAL "MINISAT_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "MiniSAT headers not found")
  else()
    include_directories(${MINISAT_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${MINISAT_LIBRARIES})
    message(STATUS "Found MiniSAT: ${MINISAT_LIBRARIES}")
    message(STATUS "Found MiniSAT headers: ${MINISAT_INCLUDE_DIR}")
  endif()
elseif(GIVEN_MINISAT_ROOT_DIR)
  message(SEND_ERROR "MiniSAT not found")
endif()

set(CMAKE_C_STANDARD 99)
set(CMAKE_CXX_STANDARD 11)

#add_c_flag("-W")
#add_c_flag("-Wall")
#add_c_flag("-Wextra")
#add_c_flag("-Wredundant-decls")
#
## option static
#add_c_flag("-static")
## option shared
#add_c_flag("-fPIC")
#
## build debug
#add_c_flag("-g3")
#add_c_flag("-ggdb")
## build release
#add_c_flag("-O3")
#
## option individual compiler flags TODO
#
## option check TODO
## add_c_flag("-DNDEBUG")
## cryptominisat:
##if (ENABLE_ASSERTIONS)
##    # NDEBUG was already removed.
##else()
##    # Note this definition doesn't appear in the cache variables.
##    add_definitions(-DNDEBUG)
##    add_cxx_flag_if_supported("-fno-stack-protector")
##    add_definitions(-D_FORTIFY_SOURCE=0)
##endif()
#
## option flto
#add_c_flag("-flto")
#
## option log TODO
## -DNBTORLOG
#
## option asan
#add_c_flag("-fsanitize=address")
#add_c_flag("-fsanitize-recover=address")
#
## option gcov
#add_c_flag("-fprofile-arcs")
#add_c_flag("-ftest-coverage")
#
## option gprof
#add_c_flag("-pg")
#
##message(STATUS "LIB directory is '${CMAKE_INSTALL_LIBDIR}'")
##message(STATUS "BIN directory is '${CMAKE_INSTALL_BINDIR}'")


