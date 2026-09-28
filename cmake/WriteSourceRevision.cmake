# Writes the capture source revision TU, touching OUTPUT only when the text
# changes so an unchanged revision recompiles nothing. The revision is HEAD with
# a -dirty suffix when tracked files differ from it, since a capture built from
# an edited tree is not reproducible from the commit alone.
execute_process(COMMAND git -C "${SOURCE_DIR}" rev-parse HEAD
  OUTPUT_VARIABLE BLACKHOLE_CAPTURE_REVISION OUTPUT_STRIP_TRAILING_WHITESPACE
  ERROR_QUIET RESULT_VARIABLE revision_result)
if(NOT revision_result EQUAL 0)
  set(BLACKHOLE_CAPTURE_REVISION "unknown")
else()
  execute_process(COMMAND git -C "${SOURCE_DIR}" status --porcelain --untracked-files=no
    OUTPUT_VARIABLE tracked_changes ERROR_QUIET RESULT_VARIABLE status_result)
  if(status_result EQUAL 0 AND NOT tracked_changes STREQUAL "")
    string(APPEND BLACKHOLE_CAPTURE_REVISION "-dirty")
  endif()
endif()
configure_file("${TEMPLATE}" "${OUTPUT}.tmp" @ONLY)
file(COPY_FILE "${OUTPUT}.tmp" "${OUTPUT}" ONLY_IF_DIFFERENT)
file(REMOVE "${OUTPUT}.tmp")
