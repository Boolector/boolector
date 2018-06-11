cmake_minimum_required (VERSION 3.3)

project(boolector)
set(VERSION "3.0.0-pre")
string(TIMESTAMP TIME)

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

set (CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

#set(CMAKE_C_STANDARD 99)
#set(CMAKE_CXX_STANDARD 11)

macro(add_c_flag flag)
  message(STATUS "Configure with flag '${flag}'")
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
endmacro()

macro(add_check_c_flag flag)
  check_c_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flag})
    add_c_flag(${flag})
  endif()
endmacro()

macro(add_cxx_flag flag)
  message(STATUS "Configure with flag '${flag}'")
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${flag}")
endmacro()

macro(add_check_cxx_flag flag)
  check_cxx_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flag})
    add_cxx_flag(${flag})
  endif()
endmacro()

macro(add_c_cxx_flag flag)
  add_c_flag(${flag})
  add_cxx_flag(${flag})
endmacro()

macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
endmacro()

add_check_c_flag("-std=gnu99")
add_check_cxx_flag("-std=c++11")

add_check_c_cxx_flag("-W")
add_check_c_cxx_flag("-Wall")
add_check_c_cxx_flag("-Wextra")
add_check_c_cxx_flag("-Wredundant-decls")

find_package(BTOR2 REQUIRED)
message(STATUS "Found Btor2Tools headers: ${BTOR2_INCLUDE_DIR}")
set(LIBRARIES ${LIBRARIES} ${BTOR2_LIBRARIES})
include_directories(${BTOR2_INCLUDE_DIR})

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package (Threads REQUIRED)
set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -lpthread")
set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -lpthread")

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
  if (${LINGELING_INCLUDE_DIR} STREQUAL "LINGELING_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "Lingeling headers not found")
  else()
    include_directories(${LINGELING_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${LINGELING_LIBRARIES})
    message(STATUS "Found Lingeling: ${LINGELING_LIBRARIES}")
    message(STATUS "Found Lingeling headers: ${LINGELING_INCLUDE_DIR}")
    add_c_cxx_flag("-DBTOR_USE_LINGELING")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -lm")
  endif()
elseif(GIVEN_LINGELING_ROOT_DIR)
  message(SEND_ERROR "Lingeling not found")
endif()

if (CADICAL_FOUND)
  if (${CADICAL_INCLUDE_DIR} STREQUAL "CADICAL_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "CaDiCaL headers not found")
  else()
    include_directories(${CADICAL_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${CADICAL_LIBRARIES})
    message(STATUS "Found CaDiCaL: ${CADICAL_LIBRARIES}")
    message(STATUS "Found CaDiCaL headers: ${CADICAL_INCLUDE_DIR}")
    add_c_cxx_flag("-DBTOR_USE_CADICAL")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -lm -lstdc++")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -lm -lstdc++")
  endif()
elseif(GIVEN_CADICAL_ROOT_DIR)
  message(SEND_ERROR "CaDiCaL not found")
endif()

if(PICOSAT_FOUND)
  if (${PICOSAT_INCLUDE_DIR} STREQUAL "PICOSAT_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "PicoSAT headers not found")
  else()
    include_directories(${PICOSAT_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${PICOSAT_LIBRARIES})
    message(STATUS "Found PicoSAT: ${PICOSAT_LIBRARIES}")
    message(STATUS "Found PicoSAT headers: ${PICOSAT_INCLUDE_DIR}")
    add_c_cxx_flag("-DBTOR_USE_PICOSAT")
  endif()
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
    add_c_cxx_flag("-DBTOR_USE_MINISAT")
    set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -lm -lz -lstdc++")
    set(CMAKE_SHARED_LINKER_FLAGS "${CMAKE_SHARED_LINKER_FLAGS} -lm -lz -lstdc++")
  endif()
elseif(GIVEN_MINISAT_ROOT_DIR)
  message(SEND_ERROR "MiniSAT not found")
endif()

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

configure_file(${CMAKE_CURRENT_SOURCE_DIR}/src/btorconfig.h.in ${CMAKE_CURRENT_BINARY_DIR}/btorconfig.h)

include_directories(src ${CMAKE_CURRENT_BINARY_DIR})
add_subdirectory(src)

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
##add_c_flag("-DNBTORLOG")
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
## option time stats
#add_c_flag("-DBTOR_TIME_STATISTICS"
##message(STATUS "LIB directory is '${CMAKE_INSTALL_LIBDIR}'")
##message(STATUS "BIN directory is '${CMAKE_INSTALL_BINDIR}'")


