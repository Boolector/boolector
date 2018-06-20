cmake_minimum_required(VERSION 3.3)

#-----------------------------------------------------------------------------#

project(boolector)
set(VERSION "3.0.0-pre")
string(TIMESTAMP TIME)

#-----------------------------------------------------------------------------#

include(CheckCCompilerFlag)
include(CheckCXXCompilerFlag)

set(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

#set(CMAKE_C_STANDARD 99)
#set(CMAKE_CXX_STANDARD 11)

macro(add_c_flag flag)
  set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${flag}")
endmacro()

macro(add_check_c_flag flag)
  check_c_compiler_flag("${flag}" HAVE_FLAG_${flag})
  if(HAVE_FLAG_${flag})
    add_c_flag(${flag})
  endif()
endmacro()

macro(add_cxx_flag flag)
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
  message(STATUS "Configure with flag '${flag}'")
endmacro()

macro(add_check_c_cxx_flag flag)
  add_check_c_flag(${flag})
  add_check_cxx_flag(${flag})
  message(STATUS "Configure with flag '${flag}'")
endmacro()

#-----------------------------------------------------------------------------#

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
message(STATUS "LIB directory is '${CMAKE_BINARY_DIR}/lib'")
message(STATUS "BIN directory is '${CMAKE_BINARY_DIR}/bin'")

#-----------------------------------------------------------------------------#

option(ASAN       "Compile with ASAN support" OFF)
option(CHECK      "Enable assertions even for optimized compilation" OFF)
option(GCOV       "Compile with coverage support" OFF)
option(GPROF      "Compile with profiling support" OFF)
option(LOG        "Compile with logging support (default for Debug builds)" OFF)
option(PYTHON     "Build Python API" OFF)
option(SHARED     "Shared Library" OFF)
option(TIME_STATS "Compile with time statistics" OFF)

option(USE_CADICAL    "Use and link with CaDiCaL" ON)
option(USE_LINGELING  "Use and link with Lingeling (default)" ON)
option(USE_MINISAT    "Use and link with MiniSat" ON)
option(USE_PICOSAT    "Use and link with PicoSAT" ON)

option(ONLY_CADICAL   "Only use CaDiCaL" OFF)
option(ONLY_LINGELING "Only use Lingeling" OFF)
option(ONLY_MINISAT   "Only use MiniSat" OFF)
option(ONLY_PICOSAT   "Only use PicoSAT" OFF)

#-----------------------------------------------------------------------------#

add_check_c_flag("-std=gnu99")
add_check_cxx_flag("-std=gnu++11")

add_check_c_cxx_flag("-W")
add_check_c_cxx_flag("-Wall")
add_check_c_cxx_flag("-Wextra")
add_check_c_cxx_flag("-Wredundant-decls")

if(FLAGS)
  add_check_c_cxx_flag("${FLAGS}")
endif()

#-----------------------------------------------------------------------------#

set(build_types Debug Release)
if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "No build type set, options are: ${build_types}")
    set(CMAKE_BUILD_TYPE Release CACHE STRING "Options are: ${build_types}" FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${build_types})
endif()
message(STATUS "Building ${CMAKE_BUILD_TYPE} build")

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  add_check_c_cxx_flag("-g3")
  add_check_c_cxx_flag("-ggdb")
  set(LOG ON)
  set(TIME_STATS ON)
elseif(CMAKE_BUILD_TYPE STREQUAL "Release")
  add_check_c_cxx_flag("-O3")
  if(NOT CHECK)
    add_c_cxx_flag("-DNDEBUG")
  endif()
  set(LOG OFF)
  set(TIME_STATS OFF)
endif()

#-----------------------------------------------------------------------------#

if(ONLY_CADICAL)
  set(USE_LINGELING OFF)
  set(USE_MINISAT OFF)
  set(USE_PICOSAT OFF)
  set(USE_CADICAL ON)
elseif(ONLY_LINGELING)
  set(USE_CADICAL OFF)
  set(USE_MINISAT OFF)
  set(USE_PICOSAT OFF)
  set(USE_LINGELING ON)
elseif(ONLY_MINISAT)
  set(USE_CADICAL OFF)
  set(USE_LINGELING OFF)
  set(USE_PICOSAT OFF)
  set(USE_MINISAT ON)
elseif(ONLY_PICOSAT)
  set(USE_CADICAL OFF)
  set(USE_LINGELING OFF)
  set(USE_MINISAT OFF)
  set(USE_PICOSAT ON)
endif()

if(ASAN)
  add_check_c_cxx_flag("-fsanitize=addres")
  add_check_c_cxx_flag("-fsanitize-recover=address")
endif()

if(GCOV)
  add_check_c_cxx_flag("-fprofile-arcs")
  add_check_c_cxx_flag("-ftest-coverage")
endif()

if(GPROF)
  add_check_c_cxx_flag("-pg")
endif()

if(NOT LOG)
  add_c_cxx_flag("-DNBTORLOG")
endif()

if(PYTHON OR SHARED)
  add_check_c_cxx_flag("-fPIC")
endif()

if(TIME_STATS)
  add_c_cxx_flag("-DBTOR_TIME_STATISTICS")
endif()

#-----------------------------------------------------------------------------#

find_package(BTOR2 REQUIRED)
message(STATUS "Found Btor2Tools headers: ${BTOR2_INCLUDE_DIR}")
set(LIBRARIES ${LIBRARIES} ${BTOR2_LIBRARIES})
include_directories(${BTOR2_INCLUDE_DIR})

set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads REQUIRED)
set(LIBRARIES ${LIBRARIES} Threads::Threads)

if(USE_LINGELING)
  find_package(LINGELING QUIET)
endif()
if(USE_CADICAL)
  find_package(CADICAL QUIET)
endif()
if(USE_PICOSAT)
  find_package(PICOSAT QUIET)
endif()
if(USE_MINISAT)
  find_package(MINISAT QUIET)
endif()

if(NOT USE_LINGELING
   AND NOT USE_CADICAL
   AND NOT USE_PICOSAT
   AND NOT USE_MINISAT)
  message(SEND_ERROR "No SAT solver configured")
elseif(NOT LINGELING_FOUND
       AND NOT CADICAL_FOUND
       AND NOT PICOSAT_FOUND
       AND NOT MINISAT_FOUND)
  message(SEND_ERROR "No SAT solver found")
endif()

if(LINGELING_FOUND)
  if(${LINGELING_INCLUDE_DIR} STREQUAL "LINGELING_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "Lingeling headers not found")
  else()
    include_directories(${LINGELING_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${LINGELING_LIBRARIES})
    message(STATUS "Found Lingeling: ${LINGELING_LIBRARIES}")
    message(STATUS "Found Lingeling headers: ${LINGELING_INCLUDE_DIR}")
    add_c_cxx_flag("-DBTOR_USE_LINGELING")
  endif()
elseif(GIVEN_LINGELING_ROOT_DIR)
  message(SEND_ERROR "Lingeling not found")
endif()

if(CADICAL_FOUND)
  if(${CADICAL_INCLUDE_DIR} STREQUAL "CADICAL_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "CaDiCaL headers not found")
  else()
    include_directories(${CADICAL_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${CADICAL_LIBRARIES})
    message(STATUS "Found CaDiCaL: ${CADICAL_LIBRARIES}")
    message(STATUS "Found CaDiCaL headers: ${CADICAL_INCLUDE_DIR}")
    add_c_cxx_flag("-DBTOR_USE_CADICAL")
  endif()
elseif(GIVEN_CADICAL_ROOT_DIR)
  message(SEND_ERROR "CaDiCaL not found")
endif()

if(PICOSAT_FOUND)
  if(${PICOSAT_INCLUDE_DIR} STREQUAL "PICOSAT_INCLUDE_DIR-NOTFOUND")
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

if(MINISAT_FOUND)
  if(${MINISAT_INCLUDE_DIR} STREQUAL "MINISAT_INCLUDE_DIR-NOTFOUND")
    message(SEND_ERROR "MiniSAT headers not found")
  else()
    include_directories(${MINISAT_INCLUDE_DIR})
    set(LIBRARIES ${LIBRARIES} ${MINISAT_LIBRARIES})
    message(STATUS "Found MiniSAT: ${MINISAT_LIBRARIES}")
    message(STATUS "Found MiniSAT headers: ${MINISAT_INCLUDE_DIR}")
    add_c_cxx_flag("-DBTOR_USE_MINISAT")
  endif()
elseif(GIVEN_MINISAT_ROOT_DIR)
  message(SEND_ERROR "MiniSAT not found")
endif()

#-----------------------------------------------------------------------------#

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

configure_file(
  ${CMAKE_CURRENT_SOURCE_DIR}/src/btorconfig.h.in
  ${CMAKE_CURRENT_BINARY_DIR}/src/btorconfig.h)

include_directories(src ${CMAKE_CURRENT_BINARY_DIR}/src)
add_subdirectory(src)
add_subdirectory(src/tests)
if(PYTHON)
  add_subdirectory(src/api/python)
endif()
