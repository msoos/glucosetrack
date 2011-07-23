cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

IF(DEFINED CMAKE_BUILD_TYPE)
    SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ELSE()
  SET(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ENDIF()

PROJECT(gluecosebetter)
#SET(CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/m4-extra) #m4-extra contains some library search cmake stuff

SET(CMAKE_C_FLAGS_RELWITHDEBINFO "-O3 -g -fno-omit-frame-pointer -mtune=native")
SET(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O3 -g -fno-omit-frame-pointer -mtune=native")

SET(CMAKE_C_FLAGS_DEBUG "-O0 -g")
SET(CMAKE_CXX_FLAGS_DEBUG "-O0 -g")

find_package(ZLIB  REQUIRED)
link_directories( ${ZLIB_LIBRARY} )
include_directories( ${ZLIB_INCLUDE_DIR} )

add_subdirectory(src)
add_subdirectory(SatELite)

add_custom_target(copy ALL
    COMMENT "Copying binaries from subdirs to build directory")

add_custom_command(
    TARGET copy
    COMMAND ${CMAKE_COMMAND} -E copy src/glucose .
    COMMAND ${CMAKE_COMMAND} -E copy SatELite/satelite .
)

add_dependencies(copy
    glucose
    satelite
)

