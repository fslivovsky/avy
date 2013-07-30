add_library (ClauseItpSeq STATIC AbcMcInterface.cc ClsItpSeqMc.cc)
add_executable (main main.cc)
target_link_libraries (main 
  ClauseItpSeq 
  ${ABC_LIBRARY} 
  readline m dl pthread 
  ${RT_LIB})
