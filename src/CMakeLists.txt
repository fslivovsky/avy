add_library (ClauseItpSeq STATIC 
  AbcMcInterface.cc ClsItpSeqMc.cc AbcUtils.cpp Pdr.cc)
add_library (AvyDebug AvyDebug.cpp)
add_executable (main main.cc)
target_link_libraries (main 
  ClauseItpSeq 
  AvyDebug
  ${ABC_LIBRARY} 
  readline m dl pthread 
  ${RT_LIB})
