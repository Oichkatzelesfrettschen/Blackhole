# Runs a determinism sim and its generic-ISA twin with the same arguments and
# fails unless their stdout is byte-identical. Invoked by ctest with
# -DNATIVE_SIM=<path> -DGENERIC_SIM=<path> -DSIM_ARGS=<args>.
foreach(required IN ITEMS NATIVE_SIM GENERIC_SIM)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "CompareSimDigests: ${required} is not set")
  endif()
endforeach()
separate_arguments(sim_args UNIX_COMMAND "${SIM_ARGS}")

execute_process(COMMAND "${NATIVE_SIM}" ${sim_args}
  OUTPUT_VARIABLE native_out RESULT_VARIABLE native_rc)
execute_process(COMMAND "${GENERIC_SIM}" ${sim_args}
  OUTPUT_VARIABLE generic_out RESULT_VARIABLE generic_rc)

if(NOT native_rc EQUAL 0 OR NOT generic_rc EQUAL 0)
  message(FATAL_ERROR "CompareSimDigests: sim exit codes ${native_rc} / ${generic_rc}")
endif()
if(native_out STREQUAL "")
  message(FATAL_ERROR "CompareSimDigests: ${NATIVE_SIM} printed nothing")
endif()
if(NOT native_out STREQUAL generic_out)
  message(FATAL_ERROR "CompareSimDigests: ISA-dependent output\n"
    "native:\n${native_out}\ngeneric:\n${generic_out}")
endif()
message(STATUS "CompareSimDigests: identical\n${native_out}")
