add_library (ClauseItpSeq STATIC 
  AbcMcInterface.cc ClsItpSeqMc.cc Global.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AbcUtils.cpp AigUtils.cc)
add_library (AvyDebug AvyDebug.cpp)
add_executable (main main.cc)
target_link_libraries (main
  ClauseItpSeq 
  AbcCpp
  AvyDebug
  ${ABC_LIBRARY} 
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  readline m dl pthread 
  ${RT_LIB})
