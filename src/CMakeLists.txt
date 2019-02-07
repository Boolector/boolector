set(libboolector_src_files
  aigprop.c
  boolector.c
  boolectormc.c
  btorabort.c
  btoraig.c
  btoraigvec.c
  btorass.c
  btorbeta.c
  btorbv.c
  btorchkclone.c
  btorclone.c
  btorcore.c
  btordbg.c
  btordcr.c
  btorexp.c
  btormc.c
  btormodel.c
  btormsg.c
  btornode.c
  btoropt.c
  btorparse.c
  btorprintmodel.c
  btorrewrite.c
  btorrwcache.c
  btorsat.c
  btorslvaigprop.c
  btorslvfun.c
  btorslvprop.c
  btorslvpropsls.c
  btorslvquant.c
  btorslvsls.c
  btorsort.c
  btorsynth.c
  btortrapi.c
  dumper/btordumpaig.c
  dumper/btordumpbtor.c
  dumper/btordumpsmt.c
  normalizer/btornormquant.c
  normalizer/btorskolemize.c
  parser/btorbtor.c
  parser/btorbtor2.c
  parser/btorsmt.c
  parser/btorsmt2.c
  sat/btorcadical.c
  sat/btorlgl.c
  sat/btorminisat.cc
  sat/btorpicosat.c
  simplifier/btorack.c
  simplifier/btorder.c
  simplifier/btorelimapplies.c
  simplifier/btorelimslices.c
  simplifier/btorextract.c
  simplifier/btormerge.c
  simplifier/btorminiscope.c
  simplifier/btorskel.c
  simplifier/btorunconstrained.c
  utils/boolectornodemap.c
  utils/btoraigmap.c
  utils/btorhashint.c
  utils/btorhashptr.c
  utils/btormem.c
  utils/btornodeiter.c
  utils/btornodemap.c
  utils/btoroptparse.c
  utils/btorpartgen.c
  utils/btorrng.c
  utils/btorutil.c
)

set(boolector_src_files
  boolectormain.c
  btormain.c
)

#-----------------------------------------------------------------------------#
# boolector library

add_library(boolector ${libboolector_src_files})
target_link_libraries(boolector ${LIBRARIES})
target_include_directories(boolector
  PUBLIC
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
    $<INSTALL_INTERFACE:include/boolector>)

target_include_directories(boolector PRIVATE ${Btor2Tools_INCLUDE_DIR})
target_link_libraries(boolector ${Btor2Tools_LIBRARIES})

if(Lingeling_FOUND)
  target_include_directories(boolector PRIVATE ${Lingeling_INCLUDE_DIR})
  target_link_libraries(boolector ${Lingeling_LIBRARIES})
endif()

if(CaDiCaL_FOUND)
  target_include_directories(boolector PRIVATE ${CaDiCaL_INCLUDE_DIR})
  target_link_libraries(boolector ${CaDiCaL_LIBRARIES})
endif()

if(PicoSAT_FOUND)
  target_include_directories(boolector PRIVATE ${PicoSAT_INCLUDE_DIR})
  target_link_libraries(boolector ${PicoSAT_LIBRARIES})
endif()

if(MiniSat_FOUND)
  target_include_directories(boolector PRIVATE ${MiniSat_INCLUDE_DIR})
  target_link_libraries(boolector ${MiniSat_LIBRARIES})
endif()

install(TARGETS boolector
  EXPORT boolector-export
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib
)

install(EXPORT boolector-export
  FILE BoolectorTargets.cmake
  NAMESPACE Boolector::
  DESTINATION lib/cmake/Boolector)

# Install header files
install(FILES boolector.h btortypes.h DESTINATION include/boolector)

#-----------------------------------------------------------------------------#
# boolector

add_executable (boolector-bin ${boolector_src_files})
target_link_libraries(boolector-bin boolector)
set_target_properties(boolector-bin
  PROPERTIES
    OUTPUT_NAME boolector
    RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)
if(NOT SHARED AND NOT APPLE)
  set_target_properties(boolector-bin
    PROPERTIES
      LINK_FLAGS "-static -Wl,--no-export-dynamic"
      LINK_SEARCH_START_STATIC ON LINK_SEARCH_END_STATIC ON)
endif()
install(TARGETS boolector-bin DESTINATION bin)

#-----------------------------------------------------------------------------#
# btormc

set(btormc_src_files
  btormcmain.c
)
add_executable (btormc ${btormc_src_files})
target_link_libraries(btormc boolector ${Btor2Tools_LIBRARIES})
target_include_directories(btormc PRIVATE ${Btor2Tools_INCLUDE_DIR})
install(TARGETS btormc DESTINATION bin)

#-----------------------------------------------------------------------------#
# btormbt

if(IS_WINDOWS_BUILD)
  message(STATUS "Skipping btormbt for Windows builds")
else()
  set(btormbt_src_files btormbt.c)
  add_executable (btormbt ${btormbt_src_files})
  target_link_libraries(btormbt boolector)
endif()

#-----------------------------------------------------------------------------#
# btoruntrace

set(btoruntrace_src_files btoruntrace.c)
add_executable (btoruntrace ${btoruntrace_src_files})
target_link_libraries(btoruntrace boolector)

#-----------------------------------------------------------------------------#
# btorimc

set(btorimc_src_files
  btoribv.cc
  btorimc.cc
)
add_executable (btorimc ${btorimc_src_files})
target_link_libraries(btorimc boolector)
