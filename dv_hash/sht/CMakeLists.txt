cmake_minimum_required(VERSION 2.8)
project(ShiftingHashTable17)

set(CMAKE_CXX_STANDARD 11)

if(CMAKE_COMPILER_IS_GNUCXX)
    message(STATUS "G++ detected, adding compile flags")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pedantic -Wall -Wextra -Wredundant-decls")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -msse2 -mssse3 -msse4.1 -msse4.2 -mavx -mbmi -mavx2 -march=native")
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pg")
    ADD_DEFINITIONS(-DUNIX)
endif(CMAKE_COMPILER_IS_GNUCXX)

add_definitions(-DPROJECT_ROOT="${CMAKE_SOURCE_DIR}")

set(CMAKE_RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/bin")

set(SOURCE_FILES src/simple_hash.h src/sht.h src/BOB_hash.h src/cuckoo_hashing.h src/cuckoo2.h)
add_executable(sht src/main.cpp src/algo_exp.h ${SOURCE_FILES})
add_executable(data_generator src/data_generater.cpp)