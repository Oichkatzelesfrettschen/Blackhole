/**
 * @file crash_handler.cpp
 * @brief Signal handlers that print a raw stack trace with only
 *        async-signal-safe primitives.
 *
 * The handler body may run on a corrupted heap, so it formats frame
 * addresses with hand-rolled decimal/hex writers over write(2) and
 * unwinds through cpptrace::safe_generate_raw_trace, which is the only
 * cpptrace entry point documented as signal-safe.
 */

#include "crash_handler.h"

#ifndef BLACKHOLE_HAS_CPPTRACE
#if __has_include(<cpptrace/cpptrace.hpp>)
#define BLACKHOLE_HAS_CPPTRACE 1
#else
#define BLACKHOLE_HAS_CPPTRACE 0
#endif
#endif

#if BLACKHOLE_HAS_CPPTRACE

#include <csignal>
#include <cstdio>
#include <cstddef>
#include <cstdint>
#include <sys/types.h>
#include <unistd.h>

#include <cpptrace/basic.hpp>
#include <cpptrace/forward.hpp>
#include <cpptrace/utils.hpp>

namespace platform {
namespace {

constexpr std::size_t K_TRACE_MAX_FRAMES = 64;
volatile sig_atomic_t gHandlingSignal = 0;
bool gCanSignalSafeUnwind = false;
bool gCanSafeObjectInfo = false;

std::size_t cstrLength(const char *str) {
  std::size_t length = 0;
  while (str[length] != '\0') {
    ++length;
  }
  return length;
}

void writeStderr(const char *str) {
  ssize_t const rc = write(STDERR_FILENO, str, cstrLength(str));
  (void)rc;
}

void writeDec(std::size_t value) {
  char buf[32];
  std::size_t i = 0;
  do { // NOLINT(cppcoreguidelines-avoid-do-while) -- digit extraction requires do-while
    buf[i++] = static_cast<char>('0' + (value % 10));
    value /= 10;
  } while (value != 0 && i < sizeof(buf));
  for (std::size_t j = 0; j < i / 2; ++j) {
    char const tmp = buf[j];
    buf[j] = buf[i - 1 - j];
    buf[i - 1 - j] = tmp;
  }
  ssize_t const rc = write(STDERR_FILENO, buf, i);
  (void)rc;
}

void writeHex(uintptr_t value) {
  static constexpr char kHex[] = "0123456789abcdef";
  char buf[2 + (sizeof(uintptr_t) * 2)];
  buf[0] = '0';
  buf[1] = 'x';
  for (std::size_t i = 0; i < sizeof(uintptr_t) * 2; ++i) {
    buf[2 + (sizeof(uintptr_t) * 2) - 1 - i] = kHex[value & 0xF];
    value >>= 4;
  }
  ssize_t const rc = write(STDERR_FILENO, buf, sizeof(buf));
  (void)rc;
}

const char *signalName(int sig) {
  switch (sig) {
  case SIGSEGV:
    return "SIGSEGV";
  case SIGABRT:
    return "SIGABRT";
  case SIGFPE:
    return "SIGFPE";
  case SIGILL:
    return "SIGILL";
  case SIGBUS: // NOLINT(misc-include-cleaner) -- SIGBUS is POSIX, provided via <csignal> on
               // Linux/glibc
    return "SIGBUS";
  case SIGTERM:
    return "SIGTERM";
  default:
    return "SIGNAL";
  }
}

void crashSignalHandler(int sig) {
  if (gHandlingSignal != 0) {
    _Exit(128 + sig);
  }
  gHandlingSignal = 1;

  writeStderr("\n==== Blackhole crash signal: ");
  writeStderr(signalName(sig));
  writeStderr(" ====\n");

  if (!gCanSignalSafeUnwind) {
    writeStderr("cpptrace: signal-safe unwind unavailable\n");
    std::signal(sig, SIG_DFL); // NOLINT(cert-err33-c) -- signal handler, cannot check return
    std::raise(sig);           // NOLINT(cert-err33-c) -- signal handler, cannot check return
    _Exit(128 + sig);
  }

  cpptrace::frame_ptr frames[K_TRACE_MAX_FRAMES];
  std::size_t const count = cpptrace::safe_generate_raw_trace(frames, K_TRACE_MAX_FRAMES, 1);
  for (std::size_t i = 0; i < count; ++i) {
    writeStderr("#");
    writeDec(i);
    writeStderr(" ");
    writeHex(reinterpret_cast<uintptr_t>(frames[i]));
    if (gCanSafeObjectInfo) {
      cpptrace::safe_object_frame objectFrame{};
      cpptrace::get_safe_object_frame(frames[i], &objectFrame);
      if (objectFrame.object_path[0] != '\0') {
        writeStderr(" ");
        writeStderr(objectFrame.object_path);
        writeStderr(" +");
        writeHex(reinterpret_cast<uintptr_t>(objectFrame.address_relative_to_object_start));
      }
    }
    writeStderr("\n");
  }

  std::signal(sig, SIG_DFL); // NOLINT(cert-err33-c) -- signal handler, cannot check return
  std::raise(sig);           // NOLINT(cert-err33-c) -- signal handler, cannot check return
  _Exit(128 + sig);
}

} // namespace

void installCrashHandlers() {
  cpptrace::use_default_stderr_logger();
  cpptrace::register_terminate_handler();
  gCanSignalSafeUnwind = cpptrace::can_signal_safe_unwind();
  gCanSafeObjectInfo = cpptrace::can_get_safe_object_frame();
  if (!gCanSignalSafeUnwind) {
    std::fprintf(stderr, // NOLINT(cert-err33-c) -- informational message, return unused
                 "cpptrace: signal-safe unwinding unavailable; signal crashes will be limited\n");
  }

  // The prior disposition returned by signal() carries no recovery path
  // during startup registration.
  (void)std::signal(SIGSEGV, crashSignalHandler); // NOLINT(cert-err33-c)
  (void)std::signal(SIGABRT, crashSignalHandler); // NOLINT(cert-err33-c)
  (void)std::signal(SIGFPE, crashSignalHandler);  // NOLINT(cert-err33-c)
  (void)std::signal(SIGILL, crashSignalHandler);  // NOLINT(cert-err33-c)
  (void)std::signal(SIGBUS, crashSignalHandler);  // NOLINT(cert-err33-c)
  (void)std::signal(SIGTERM, crashSignalHandler); // NOLINT(cert-err33-c)
}

} // namespace platform

#else

namespace platform {
void installCrashHandlers() {}
} // namespace platform

#endif // BLACKHOLE_HAS_CPPTRACE
