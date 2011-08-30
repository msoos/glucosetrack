cmake_minimum_required(VERSION 2.6 FATAL_ERROR)

IF(DEFINED CMAKE_BUILD_TYPE)
    SET(CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE} CACHE STRING "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ELSE()
  SET(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING "Choose the type of build, options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release RelWithDebInfo MinSizeRel.")
ENDIF()

PROJECT(glucosetrack)
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
    COMMAND ${CMAKE_COMMAND} -E copy src/glucose_track .
    COMMAND ${CMAKE_COMMAND} -E copy SatELite/satelite .
)

add_dependencies(copy
    glucose_track
    satelite
)

#general setup
SET(CPACK_PACKAGE_DESCRIPTION_SUMMARY "Glucose with usefulness measure")
SET(CPACK_PACKAGE_MAINTAINER "Mate Soos (mate@srlabs.de)")
SET(CPACK_PACKAGE_DESCRIPTION_FILE "${CMAKE_CURRENT_SOURCE_DIR}/README")
SET(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/LICENSE")
SET(CPACK_PACKAGE_VERSION_MAJOR "1")
SET(CPACK_PACKAGE_VERSION_MINOR "0")
SET(CPACK_PACKAGE_VERSION_PATCH "0")


#tarball generators
set(CPACK_GENERATOR TGZ)
set(CPACK_SOURCE_GENERATOR TGZ)
set(CPACK_SOURCE_IGNORE_FILES
"~$"
"^${PROJECT_SOURCE_DIR}/build/"
"${PROJECT_SOURCE_DIR}/.git/"
"${PROJECT_SOURCE_DIR}/.kdev4/"
)

SET(CPACK_SOURCE_PACKAGE_FILE_NAME
    "glucosetrack-${CPACK_PACKAGE_VERSION_MAJOR}.${CPACK_PACKAGE_VERSION_MINOR}.${CPACK_PACKAGE_VERSION_PATCH}")

SET(CPACK_PACKAGE_EXECUTABLES "satelite" "glucose")
set(CPACK_SOURCE_STRIP_FILES 1)
#INSTALL_TARGETS(/bin glucose)
#INSTALL_TARGETS(/bin satelite)

INCLUDE(CPack)


