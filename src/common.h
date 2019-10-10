#pragma once

#include <vector>
#include <string>
#include <iostream>
#include <sstream>

const double EPS = 1e-8;
const double PI = 3.14159265358979323846;

template<class T>
T Abs(const T& t) {
	if ( t > 0 ) return t;
	return -t;
}

template<class T>
T Sgn(const T& t) {
	if ( t > 0 ) return 1;
	if ( t < 0 ) return -1;
	return 0;
}

template<class T>
T Sqr2(const T& t) {
	return ((t) * (t));
}

template <typename T>
std::string to_string(const T& n) {
	std::ostringstream ss;
  ss << n;
  return ss.str();
}

template <typename T>
std::string to_string(const std::vector<T>& vec) {
  std::string desc = "";
  for (auto p : vec) {
    if (desc.length() > 0) desc += " ";
    desc += to_string(p);
  }
  return desc;
}

inline int to_int(const std::string& s) {
	int n;
	std::istringstream (s) >> n;
	return n;
}

inline double to_double(const std::string& s) {
	double n;
	std::istringstream (s) >> n;
	return n;
}

struct Rand {
  static size_t setSeed();
  static size_t setSeed(size_t seed);

  static double nextDouble();
  static bool check(double probability);
  static int next();
  static int next(int bound);
  static int next(int lower, int upper);
  static void shuffle(std::vector<size_t>& vec);
  static void shuffle(std::vector<int>& vec);
  static std::vector<int> permutation(size_t n);
};

std::vector<std::string> SplitNotNull(const std::string& s, const std::string& c);
std::vector<int> SplitNotNullInt(const std::string& s, const std::string& c);

double Average(const std::vector<double>& v);
double Median(const std::vector<double>& v);
double Maximum(const std::vector<double>& v);
double Minimum(const std::vector<double>& v);
double Sum(const std::vector<double>& v);
double Percentile(const std::vector<double>& v, int value);

int Compare(double numberA, double numberB);
bool Equal(double a, double b);
bool GreaterOrEqual(double numberA, double numberB);
bool Greater(double numberA, double numberB);
bool LessOrEqual(double numberA, double numberB);
bool Less(double numberA, double numberB);
