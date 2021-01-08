add_library (ClauseItpSeq STATIC 
  Global.cc SafetyVC.cc Stats.cc SafetyAigVC.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AigUtils.cc ItpMinisat.cc)
add_library (AvyDebug AvyDebug.cc)
