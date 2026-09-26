#include "common.h"

#include <cctype>
#include <random>
#include <limits>
#include <cassert>

using namespace std;

string trim(const string& s) {
  size_t first = 0;
  while (first < s.size() && isspace(static_cast<unsigned char>(s[first])))
    first++;

  size_t last = s.size();
  while (last > first && isspace(static_cast<unsigned char>(s[last - 1])))
    last--;

  return s.substr(first, last - first);
}

std::vector<string> SplitNotNull(const std::string& ss, const std::string& c) {
  std::string s = ss + c;
  std::vector<std::string> result;
  std::string cur = "";

  for (size_t i = 0; i < s.length(); i++) {
    if (c.find(s[i]) != std::string::npos) {
      if (cur.length() > 0)
        result.push_back(cur);
      cur = "";
    } else {
      cur += s[i];
    }
  }
  return result;
}

std::vector<int> SplitNotNullInt(const string& ss, const string& c) {
  auto tmp = SplitNotNull(ss, c);
  vector<int> res;
  for (auto v : tmp) {
    res.push_back(to_int(v));
  }
  return res;
}

double percentile(const std::vector<double>& vec, int p) {
  if (vec.empty())
    return 0;

  const size_t n = vec.size();
  const size_t pos = std::min(p * n / 100, n - 1);
  return vec[pos];
}

double confidence_interval(const std::vector<uint64_t>& vec) {
  const size_t size = vec.size();
  if (size == 0)
    return 0;
  double mean = std::accumulate(vec.begin(), vec.end(), 0.0) / double(size);
  auto variance_func = [&mean, &size](double accumulator, const double val) {
      return accumulator + ((val - mean) * (val - mean) / double(size));
  };
  double variance = std::accumulate(vec.begin(), vec.end(), 0.0, variance_func);
  const double sd = sqrt(variance);
  const double se = sd / sqrt(double(size));
  return 1.96 * se;
}

std::mt19937 RNG;

size_t Rand::setSeed() {
  return setSeed(static_cast<size_t>(time(0)));
}

size_t Rand::setSeed(size_t seed) {
  RNG.seed(seed);
  return seed;
}

double Rand::nextDouble() {
  return std::uniform_real_distribution<double>(0.0, 1.0)(RNG);
}

bool Rand::nextBool() {
  return nextDouble() <= 0.5;
}

bool Rand::check(double probability) {
  return nextDouble() <= probability;
}

int Rand::next() {
  return RNG();
}

int Rand::next(int bound) {
  return Abs(RNG()) % bound;
}

int Rand::next(int lower, int upper) {
  assert(0 <= lower && lower < upper);
  return lower + Abs(RNG()) % (upper - lower);
}

std::vector<int> Rand::permutation(size_t n) {
  std::vector<int> p(n, 0);
  for (size_t i = 0; i < n; i++) {
    p[i] = i;
  }
  Rand::shuffle(p.begin(), p.end());
  return p;
}

std::vector<int> identity(size_t n) {
  return identity(0, n);
}

std::vector<int> identity(size_t start, size_t n) {
  std::vector<int> r(n);
  for (size_t i = 0; i < n; i++) {
    r[i] = i + start;
  }
  return r;
}

std::vector<int> inverse(const std::vector<int>& p) {
  std::vector<int> r(p.size(), -1);
  for (size_t i = 0; i < p.size(); i++) {
    assert(r[p[i]] == -1 && "incorrect permutation for inversion");
    r[p[i]] = i;
  }
  return r;
}

std::vector<int> reverse(const std::vector<int>& p) {
  std::vector<int> r(p.begin(), p.end());
  std::reverse(r.begin(), r.end());
  return r;
}

std::string ms_to_str(uint64_t duration_ms) {
  // < 5 sec
  if (duration_ms < 5 * 1000)
    return to_string(duration_ms) + " ms";
  // < 5 min
  const uint64_t duration_sec = duration_ms / 1000;
  if (duration_sec < 5 * 60)
    return to_string(duration_sec) + " seconds";
  // < 1 hour
  const uint64_t duration_min = duration_sec / 60;
  if (duration_min < 60)
    return to_string(duration_min) + " minutes";
  // hh:mm
  const uint64_t hh = duration_min / 60;
  const uint64_t mm = duration_min % 60;
  return to_string(hh) + " hours and " + to_string(mm) + " minutes";
}

std::string ms_to_str(std::chrono::time_point<chrono::steady_clock> startTime,
                      std::chrono::time_point<chrono::steady_clock> endTime) {
  const auto duration_ms = chrono::duration_cast<chrono::milliseconds>(endTime - startTime).count();
  return ms_to_str(duration_ms);
}

bool cross(const int l1, const int r1, const int l2, const int r2) {
  assert(l1 < r1 && l2 < r2);

  if (l1 < l2 && l2 < r1 && r1 < r2)
    return true;
  if (l2 < l1 && l1 < r2 && r2 < r1)
    return true;
  return false;
}

bool nest(const int l1, const int r1, const int l2, const int r2) {
  assert(l1 < r1 && l2 < r2);

  if (l1 < l2 && l2 < r2 && r2 < r1)
    return true;
  if (l2 < l1 && l1 < r1 && r1 < r2)
    return true;
  return false;
}
