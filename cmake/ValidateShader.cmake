if(NOT DEFINED GLSLANG_VALIDATOR)
  message(FATAL_ERROR "GLSLANG_VALIDATOR is not set")
endif()
if(NOT DEFINED SHADER)
  message(FATAL_ERROR "SHADER is not set")
endif()
if(NOT DEFINED STAGE)
  message(FATAL_ERROR "STAGE is not set")
endif()

if(NOT DEFINED GLSL_VERSION)
  set(GLSL_VERSION "460")
endif()
if(NOT DEFINED INCLUDE_DIR)
  set(INCLUDE_DIR "")
endif()

execute_process(
  COMMAND "${GLSLANG_VALIDATOR}"
    -S "${STAGE}"
    -l
    --glsl-version "${GLSL_VERSION}"
    "-I${INCLUDE_DIR}"
    "-P#extension GL_GOOGLE_include_directive : enable"
    "${SHADER}"
  RESULT_VARIABLE result
  OUTPUT_VARIABLE stdout
  ERROR_VARIABLE stderr
)

if(NOT result EQUAL 0)
  message(FATAL_ERROR "glslangValidator failed for ${SHADER}:\n${stdout}\n${stderr}")
endif()

string(TOLOWER "${stdout}${stderr}" combined)
if(combined MATCHES "warning")
  if(DEFINED WARN_AS_ERROR AND WARN_AS_ERROR)
    message(FATAL_ERROR "glslangValidator warnings for ${SHADER}:\n${stdout}\n${stderr}")
  else()
    message(WARNING "glslangValidator warnings for ${SHADER}:\n${stdout}\n${stderr}")
  endif()
endif()

message(STATUS "Validated ${SHADER}")
