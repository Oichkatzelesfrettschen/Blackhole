# Runs a determinism sim and its generic-ISA twin with the same arguments and
# fails unless their stdout is byte-identical. Invoked by ctest with
# -DNATIVE_SIM=<path> -DGENERIC_SIM=<path> and either -DSIM_ARGC=<n> with
# -DSIM_ARG0..-DSIM_ARG<n-1> (one definition per argument, whitespace kept)
# or -DSIM_ARGS=<args> (split on whitespace).
foreach(required IN ITEMS NATIVE_SIM GENERIC_SIM)
  if(NOT DEFINED ${required})
    message(FATAL_ERROR "CompareSimDigests: ${required} is not set")
  endif()
endforeach()
if(DEFINED SIM_ARGC)
  set(sim_args "")
  if(SIM_ARGC GREATER 0)
    math(EXPR last_arg "${SIM_ARGC} - 1")
    foreach(index RANGE ${last_arg})
      list(APPEND sim_args "${SIM_ARG${index}}")
    endforeach()
  endif()
else()
  separate_arguments(sim_args UNIX_COMMAND "${SIM_ARGS}")
endif()

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
