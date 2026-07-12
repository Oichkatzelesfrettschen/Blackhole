/**
 * @file crash_handler.h
 * @brief Signal-safe crash reporting for fatal signals.
 *
 * installCrashHandlers() registers handlers for SIGSEGV, SIGABRT, SIGFPE,
 * SIGILL, SIGBUS, and SIGTERM that print a raw stack trace through
 * cpptrace's signal-safe unwinder using only async-signal-safe writes,
 * then re-raise the signal with the default disposition. Built without
 * cpptrace, the call is a no-op.
 */

#ifndef BLACKHOLE_PLATFORM_CRASH_HANDLER_H
#define BLACKHOLE_PLATFORM_CRASH_HANDLER_H

namespace platform {

void installCrashHandlers();

} // namespace platform

#endif // BLACKHOLE_PLATFORM_CRASH_HANDLER_H
