add_library (ClauseItpSeq STATIC 
  AbcMcInterface.cc BMCSolver.cc ClsItpSeqMc.cc Global.cc SafetyVC.cc Stats.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AigUtils.cc ItpSatSolver.cc)
add_library (AvyDebug AvyDebug.cc)
add_executable (main main.cc AvyMain.cc)
target_link_libraries (main 
  ClauseItpSeq 
  AbcCpp
  AvyDebug
  ${ABC_LIBRARY} 
  ${MINISAT_LIBRARY}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread z
  ${RT_LIB})
