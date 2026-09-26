#pragma once

#include <chrono>
#include <clocale>
#include <cstdio>
#include <cstdarg>
#include <cstring>
#include <ctime>
#include <iostream>
#include <string>
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
    CHECK_LOG_EMPTY(XSTR(condition), __FILE__, __LINE__); \
    throw CHECK_EXIT_CODE; \
  }
#define CHECK2(condition, ...) \
  if (0 == (condition)) { \
    CHECK_LOG(XSTR(condition), __FILE__, __LINE__, __VA_ARGS__); \
    throw CHECK_EXIT_CODE; \
  }
#define GET_MACRO(_0,_1,_2,_3,_4,_5,_6,_7,_8,_9,NAME,...) NAME
#define CHECK(...) GET_MACRO(__VA_ARGS__, CHECK2, CHECK2, CHECK2, CHECK2, CHECK2, CHECK2, CHECK2, CHECK2, CHECK2, CHECK1)(__VA_ARGS__)

#define ERROR(message) \
  { \
    std::cerr << ansi_prefix(TextColor::red) << message << ansi_suffix(TextColor::red) \
              << " [" << __FILE__ << ":" << __LINE__ << "]\n"; \
    throw ERROR_EXIT_CODE; \
  }
#define VERIFY(condition, ...) \
  if (0 == (condition)) { \
    CHECK_LOG(XSTR(condition), __FILE__, __LINE__, __VA_ARGS__); \
    throw VERIFICATION_EXIT_CODE; \
  }

inline bool LOGGER_USE_COLORS = true;

enum class TextColor {
  none,
  red,
  blue,
  green,
  pink,
  grey,
};

inline const char* ansi_prefix(TextColor color) {
  if (!LOGGER_USE_COLORS || color == TextColor::none)
    return "";

  switch (color) {
    case TextColor::none:  return "";
    case TextColor::red:   return "\033[91m";
    case TextColor::blue:  return "\033[38;5;12m";
    case TextColor::green: return "\033[38;5;34m";
    case TextColor::pink:  return "\033[38;5;13m";
    case TextColor::grey:  return "\033[90m";
  }
  return "";
}

inline const char* ansi_suffix(TextColor color) {
  if (!LOGGER_USE_COLORS || color == TextColor::none)
    return "";
  return "\033[0m";
}

inline std::string vformat_to_string(const char* format, va_list args) {
  char buffer[16384];
  va_list copy;
  va_copy(copy, args);
  std::vsnprintf(buffer, sizeof(buffer), format, copy);
  va_end(copy);
  return std::string(buffer);
}

inline void CHECK_LOG(const char* desc, const char* file, int line, const char* message, va_list args) {
  char buffer[16384];
  std::vsnprintf(buffer, sizeof(buffer), message, args);
  std::cerr << ansi_prefix(TextColor::red) << "assertion '" << desc << "' failed: " << buffer
            << ansi_suffix(TextColor::red) << " [" << file << ":" << line << "]\n";
}

inline void CHECK_LOG(const char* desc, const char* file, int line, ...) {
  va_list args;
  va_start(args, line);
  const char* message = va_arg(args, const char*);
  CHECK_LOG(desc, file, line, message, args);
  va_end(args);
}

inline void CHECK_LOG_EMPTY(const char* desc, const char* file, int line) {
  std::cerr << ansi_prefix(TextColor::red) << "assertion '" << desc << "' failed"
            << ansi_suffix(TextColor::red) << " [" << file << ":" << line << "]\n";
}

inline std::string timestamp_prefix() {
  const auto now = std::chrono::system_clock::now();
  const auto time = std::chrono::system_clock::to_time_t(now);
  std::string timestamp = std::ctime(&time);
  timestamp.erase(timestamp.find_last_not_of(" \n\r\t") + 1);
  return std::string(ansi_prefix(TextColor::grey)) + timestamp + ":" + ansi_suffix(TextColor::grey);
}

inline void LOG_line(TextColor color, const std::string& line) {
  std::cerr << timestamp_prefix() << " " << ansi_prefix(color) << line << ansi_suffix(color) << "\n";

  // for (int i = 0; i < 255; i++) {
  //   std::string label = "ABC012";
  //   std::cout << i << ": " <<  "\033[38;5;" << i << "m" << label << "\033[0m\n";
  // }
}

inline void LOG(TextColor color, const char* message, va_list& args) {
  LOG_line(color, vformat_to_string(message, args));
}

struct ColoredStr {
  std::string value;
  const char* c_str() const noexcept { return value.c_str(); }
};

inline ColoredStr colored_str(TextColor color, const char* format, ...) {
  char buffer[4096];
  va_list args;
  va_start(args, format);
  std::vsnprintf(buffer, sizeof(buffer), format, args);
  va_end(args);

  ColoredStr result;
  result.value.reserve(
      std::strlen(ansi_prefix(color)) + std::strlen(buffer) + std::strlen(ansi_suffix(color)));
  result.value += ansi_prefix(color);
  result.value += buffer;
  result.value += ansi_suffix(color);
  return result;
}

inline void LOG(const std::string& message) {
  LOG_line(TextColor::none, message);
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
  if (!condition) {
    return;
  }

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

inline void initLogger(bool useColors) {
  std::setlocale(LC_NUMERIC, "");
  LOGGER_USE_COLORS = useColors;
}
