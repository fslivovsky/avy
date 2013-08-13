project(ClauseItpSeq)
cmake_minimum_required(VERSION 2.8)

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

# Add path for custom modules
set(CMAKE_MODULE_PATH
  ${CMAKE_MODULE_PATH}
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake"
  )


set (CUSTOM_BOOST_ROOT "" CACHE PATH "Path to custom boost installation.")
if (CUSTOM_BOOST_ROOT)
  set (BOOST_ROOT ${CUSTOM_BOOST_ROOT})
  set (Boost_NO_SYSTEM_PATHS "ON")
endif()

set (Boost_USE_STATIC_LIBS ON)
find_package (Boost 1.46.1 REQUIRED)
IF (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
endif ()


# check for rt lib. Not needed on OSX.
find_library(RT_LIB NAMES rt)
if (NOT RT_LIB)
  set(RT_LIB "")
endif()
mark_as_advanced(RT_LIB)

# prefer linking with static libraries
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

find_package(Abc REQUIRED)
if (ABC_FOUND)
  include_directories(${ABC_INCLUDE_DIR})
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${ABC_CXXFLAGS}")
else()
  set(ABC_LIBRARY "")
endif ()

find_package (Periplo)
if (PERIPLO_FOUND)
  include_directories(${PERIPLO_INCLUDE_DIR})
else()
  set(PERIPLO_LIBRARY "")
endif ()


include_directories(
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/include
  )

add_subdirectory(src)