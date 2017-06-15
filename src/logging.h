#pragma once

#include <iostream>
#include <chrono>
#include <ctime>
#include <cstdarg>

const int ASSERT_EXIT_CODE = -400;
const int CHECK_EXIT_CODE = 10;

#define stringize(s) #s
#define XSTR(s) stringize(s)
#define CHECK1(condition) \
if (0 == (condition)) { \
  std::cerr << "assertion '" << XSTR(condition) << "' failed [" << __FILE__ << ":" << __LINE__ << "]\n"; \
  throw ASSERT_EXIT_CODE; \
}
#define CHECK2(condition, message) \
  CHECK3(condition, message, CHECK_EXIT_CODE)
#define CHECK3(condition, message, exitCode) \
if (0 == (condition)) { \
  std::cerr << "\033[91m" << message << "\033[0m" << " [" << __FILE__ << ":" << __LINE__ << "]\n"; \
  throw exitCode; \
}
#define GET_MACRO(_1,_2,_3,NAME,...) NAME
#define CHECK(...) GET_MACRO(__VA_ARGS__, CHECK3, CHECK2, CHECK1)(__VA_ARGS__)

#define ERROR(message) \
{ \
  std::cerr << "\033[91m" << message << "\033[0m" << " [" << __FILE__ << ":" << __LINE__ << "]\n"; \
  throw ASSERT_EXIT_CODE; \
}

inline void LOG(const char* message, va_list args) {
  auto end = std::chrono::system_clock::now();
  auto time = std::chrono::system_clock::to_time_t(end);
  auto stime = std::string(std::ctime(&time));
  stime.erase(stime.find_last_not_of(" \n\r\t") + 1);
  stime = "\033[90m" + stime + ":\033[0m";

  char* buffer = new char[1024];

  std::vsprintf(buffer, message, args);

  std::cerr << stime << " " << std::string(buffer) << "\n";
  delete[] buffer;
}

inline void LOG_IF(bool condition, const char* message, ...) {
  if (!condition) return;

  va_list args;
  va_start(args, message);
  LOG(message, args);
  va_end(args);
}

inline void LOG(const char* message, ...) {
  va_list args;
  va_start(args, message);
  LOG(message, args);
  va_end(args);
}
