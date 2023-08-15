# Boolector: Satisfiablity Modulo Theories (SMT) solver.
#
# Copyright (C) 2007-2021 by the authors listed in the AUTHORS file.
#
# This file is part of Boolector.
# See COPYING for more information on using this software.
#
find_package(PythonExtensions REQUIRED)
find_package(Cython REQUIRED)

include_directories(${PYTHON_INCLUDE_DIRS})
include_directories(${CMAKE_CURRENT_LIST_DIR})               # btorapi.pxd
include_directories(${CMAKE_CURRENT_LIST_DIR}/../..) # boolector.h
include_directories(${CMAKE_CURRENT_BINARY_DIR})

set(generated_file "${CMAKE_CURRENT_BINARY_DIR}/pyboolector_enums.pxd")

# Generate pyboolector_enums.pxd from btortypes.h
add_custom_command(
  COMMAND
    "${PYTHON_EXECUTABLE}"
    "${CMAKE_CURRENT_LIST_DIR}/mkenums.py"
    "${CMAKE_CURRENT_LIST_DIR}/../../btortypes.h"
    "${generated_file}"
  OUTPUT
    "${generated_file}"
  DEPENDS
    "${CMAKE_CURRENT_LIST_DIR}/mkenums.py"
    "${CMAKE_CURRENT_LIST_DIR}/../../btortypes.h"
  COMMENT
    "Generate pyboolector_enums.pxd"
)

add_custom_target(
    pyboolector_enums
    DEPENDS
      "${generated_file}"
      "${CMAKE_CURRENT_LIST_DIR}/mkenums.py"
      "${CMAKE_CURRENT_LIST_DIR}/../../btortypes.h"
)
add_cython_target(pyboolector CXX)  # implicitely uses pyboolector.pyx

add_library(pyboolector
            MODULE
            ${pyboolector} boolector_py.c pyboolector_abort.cpp)
add_dependencies(pyboolector pyboolector_enums)

target_link_libraries(pyboolector boolector ${PYTHON_LIBRARIES})

if(IS_WINDOWS_BUILD)
  target_link_libraries(pyboolector -static gcc stdc++ winpthread -dynamic)
endif()

python_extension_module(pyboolector)
install(TARGETS pyboolector DESTINATION lib)
