add_library (ClauseItpSeq STATIC 
  Global.cc SafetyVC.cc Stats.cc)
add_library (AbcCpp Pdr.cc AigPrint.cc AigUtils.cc ItpMinisat.cc ItpGlucose.cc)
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

add_executable(abcpdr AbcPdr.cc)
target_link_libraries (abcpdr
  ClauseItpSeq
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread z
  ${RT_LIB})

add_executable(avypdr AvyPdr.cc)
target_link_libraries (avypdr
  ClauseItpSeq
  AbcCpp
  AvyDebug
  ${EXT_LIBRARIES}
  ${Boost_PROGRAM_OPTIONS_LIBRARY}
  m dl pthread z
  ${RT_LIB})

if (AVY_STATIC_EXE)
    set (CMAKE_EXE_LINKER_FLAGS "-static -static-libgcc -static-libstdc++")
    set_target_properties (avy PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avy PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (avybmc PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avybmc PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (abcpdr PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (abcpdr PROPERTIES LINK_SEARCH_END_STATIC ON)
    set_target_properties (avypdr PROPERTIES LINK_SEARCH_START_STATIC ON)
    set_target_properties (avypdr PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

