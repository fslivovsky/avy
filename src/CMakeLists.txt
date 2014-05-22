add_library (ClauseItpSeq STATIC 
  Global.cc SafetyVC.cc Stats.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AigUtils.cc ItpSatSolver.cc ItpMinisat.cc ItpGlucose.cc)
add_library (AvyDebug AvyDebug.cc)

set (EXT_LIBRARIES ${ABC_LIBRARY} ${MINISAT_LIBRARY} ${GLUCOSE_LIBRARY})

add_executable (avy main.cc AvyMain.cc)
target_link_libraries (avy
  ClauseItpSeq 
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread z
  ${RT_LIB})

add_executable (avybmc AvyBmc.cc)
target_link_libraries (avybmc
  ClauseItpSeq 
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread z
  ${RT_LIB})
