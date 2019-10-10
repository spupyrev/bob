#pragma once

#include <iostream>
#include <string>
#include <chrono>
#include <ctime>
#include <cstdarg>
#include <unordered_map>

// assertion (wild server error)
const int ERROR_EXIT_CODE = 99;
// application error
const int CHECK_EXIT_CODE = 40;
// user validation
const int VERIFICATION_EXIT_CODE = 10;

#define stringize(s) #s
#define XSTR(s) stringize(s)
#define CHECK1(condition) \
if (0 == (condition)) { \
  std::cerr << "\033[91m" << "assertion '" << XSTR(condition) << "' failed" << "\033[0m" << " [" << __FILE__ << ":" << __LINE__ << "]\n"; \
  throw CHECK_EXIT_CODE; \
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
  throw ERROR_EXIT_CODE; \
}
#define VERIFY(condition, message) \
  CHECK3(condition, message, VERIFICATION_EXIT_CODE)

enum class TextColor {
  none,
  red,
  blue
};

inline void LOG(TextColor color, const char* message, va_list args) {
  auto end = std::chrono::system_clock::now();
  auto time = std::chrono::system_clock::to_time_t(end);
  auto stime = std::string(std::ctime(&time));
  stime.erase(stime.find_last_not_of(" \n\r\t") + 1);
  stime = "\033[90m" + stime + ":\033[0m";

  char* buffer = new char[1024];

  setlocale(LC_NUMERIC, "");
  std::vsprintf(buffer, message, args);

  std::cerr << stime << " ";
  switch (color) {
    case TextColor::none: std::cerr << std::string(buffer); break;
    case TextColor::red : std::cerr << "\033[91m" << std::string(buffer) << "\033[0m"; break;
    case TextColor::blue: std::cerr << "\e[38;5;12m" << std::string(buffer) << "\e[0m"; break;
  };
  std::cerr << "\n";
  delete[] buffer;

  // for (int i = 0; i < 255; i++) {
  //   string label = "ABC012";
  //   cout << i << ": " <<  "\e[38;5;" << i << "m" << label << "\e[0m\n";
  // }
}

inline void LOG(const std::string& message) {
  va_list args;
  LOG(TextColor::none, message.c_str(), args);
}

inline void LOG(const char* message, ...) {
  va_list args;
  va_start(args, message);
  LOG(TextColor::none, message, args);
  va_end(args);
}

inline void LOG(TextColor color, const char* message, ...) {
  va_list args;
  va_start(args, message);
  LOG(color, message, args);
  va_end(args);
}

inline void LOG_IF(bool condition, const char* message, ...) {
  if (!condition) return;

  va_list args;
  va_start(args, message);
  LOG(TextColor::none, message, args);
  va_end(args);
}

inline void LOG_EVERY_MS(int period, const char* message, ...) {
  static std::unordered_map<std::string, std::chrono::time_point<std::chrono::steady_clock>> LastLogTime;

  std::string msg = std::string(message);

  auto time = std::chrono::steady_clock::now();
  auto it = LastLogTime.find(msg);
  if (it != LastLogTime.end()) {
    auto lastTime = it->second;
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(time - lastTime).count();
    if (duration <= period) {
      return;
    }
  }

  va_list args;
  va_start(args, message);
  LOG(TextColor::none, message, args);
  va_end(args);

  LastLogTime[msg] = time;
}
