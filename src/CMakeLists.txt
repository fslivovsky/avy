add_library (ClauseItpSeq STATIC 
  AbcMcInterface.cc BMCSolver.cc ClsItpSeqMc.cc Global.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AigUtils.cc )
add_library (AvyDebug AvyDebug.cc)
add_executable (main main.cc)
target_link_libraries (main 
  ClauseItpSeq 
  AbcCpp
  AvyDebug
  ${ABC_LIBRARY} 
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  readline m dl pthread 
  ${RT_LIB})
