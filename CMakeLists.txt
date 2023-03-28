cmake_minimum_required(VERSION 3.8)
project(nextbdd CXX)
add_compile_options(-g -Wall -Wextra -Wpedantic -O3)

add_library(nextbdd INTERFACE)
target_include_directories(nextbdd INTERFACE ${CMAKE_CURRENT_SOURCE_DIR})

add_executable(test ${CMAKE_CURRENT_SOURCE_DIR}/test.cpp)
target_link_libraries(test nextbdd)
