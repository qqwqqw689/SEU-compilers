cmake_minimum_required(VERSION 3.0)
project(your_project_name)  # Change "your_project_name" to the actual name of your project

# Add the executable
add_executable(your_executable_name main.cpp Lex.cpp)

# Include the directory containing Lex.h
target_include_directories(your_executable_name PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})

# Optionally, you can set C++ standard
set(CMAKE_CXX_STANDARD 11) # Or any other version you want

# Optionally, you can specify additional compile options
# For example, to enable warnings:
# set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra")