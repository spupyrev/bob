#pragma once

#include <sstream>
#include <string>
#include <vector>

template <typename T>
std::string to_string(const T& n) {
  std::ostringstream ss;
  ss << n;
  return ss.str();
}

inline int to_int(const std::string& s) {
  int n;
  std::istringstream(s) >> n;
  return n;
}

inline double to_double(const std::string& s) {
  double n;
  std::istringstream(s) >> n;
  return n;
}

std::vector<std::string> SplitNotNull(const std::string& s, const std::string& c);
