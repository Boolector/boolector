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

add_library(boolector STATIC ${libboolector_src_files})
target_link_libraries(boolector ${LIBRARIES})

if(SHARED)
  add_library(boolector-shared SHARED ${libboolector_src_files})
  target_link_libraries(boolector-shared ${LIBRARIES})
  set_target_properties(boolector-shared PROPERTIES OUTPUT_NAME boolector)
endif()

add_executable (boolector-bin ${boolector_src_files})
target_link_libraries(boolector-bin boolector ${LIBRARIES})
set_target_properties(boolector-bin PROPERTIES OUTPUT_NAME boolector)

set(btormc_src_files
  btormcmain.c
)
add_executable (btormc ${btormc_src_files})
target_link_libraries(btormc boolector ${LIBRARIES})

if(IS_WINDOWS_BUILD)
  message(STATUS "Skipping btormbt for Windows builds")
else()
  set(btormbt_src_files btormbt.c)
  add_executable (btormbt ${btormbt_src_files})
  target_link_libraries(btormbt boolector ${LIBRARIES})
endif()

set(btoruntrace_src_files btoruntrace.c)
add_executable (btoruntrace ${btoruntrace_src_files})
target_link_libraries(btoruntrace boolector ${LIBRARIES})

set(btorimc_src_files
  btoribv.cc
  btorimc.cc
)
add_executable (btorimc ${btorimc_src_files})
target_link_libraries(btorimc boolector ${LIBRARIES})

