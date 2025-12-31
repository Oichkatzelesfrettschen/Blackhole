cmake_minimum_required(VERSION 3.21)

project(imgui LANGUAGES CXX)

option(IMGUI_BUILD_DEMO "Build imgui_demo.cpp" ON)

set(IMGUI_SOURCES
  imgui.cpp
  imgui_draw.cpp
  imgui_tables.cpp
  imgui_widgets.cpp
)

if(IMGUI_BUILD_DEMO)
  list(APPEND IMGUI_SOURCES imgui_demo.cpp)
endif()

add_library(imgui ${IMGUI_SOURCES})
set_target_properties(imgui PROPERTIES POSITION_INDEPENDENT_CODE ON)

target_include_directories(imgui PUBLIC
  $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}>
  $<INSTALL_INTERFACE:include>
)

target_compile_features(imgui PUBLIC cxx_std_11)

install(TARGETS imgui
  ARCHIVE DESTINATION lib
  LIBRARY DESTINATION lib
  RUNTIME DESTINATION bin
)

install(FILES
  imgui.h
  imconfig.h
  imgui_internal.h
  imstb_rectpack.h
  imstb_textedit.h
  imstb_truetype.h
  DESTINATION include
)
