#include "common.h"

#include <algorithm>
#include <random>
#include <limits>
#include <cassert>

using namespace std;

std::vector<string> SplitNotNull(const string& ss, const string& c) {
  string s = ss + c;
  vector<string> result;
  string cur = "";

  for (size_t i = 0; i < s.length(); i++) {
    if (c.find(s[i]) != string::npos) {
      if (cur.length() > 0) {
        result.push_back(cur);
      }

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

  for (size_t i = 0; i < tmp.size(); i++) {
    res.push_back(to_int(tmp[i]));
  }

  return res;
}

double Sum(const vector<double>& v) {
  double sum = 0;

  for (int i = 0; i < (int)v.size(); i++) {
    sum += v[i];
  }

  return sum;
}

double Average(const vector<double>& v) {
  double av = Sum(v);

  if (!v.empty()) {
    av /= (double)v.size();
  }

  return av;
}

double Median(const vector<double>& v) {
  if (v.empty()) {
    return 0;
  }

  if (v.size() == 1) {
    return v[0];
  }

  vector<double> tmp = v;
  sort(tmp.begin(), tmp.end());
  int sz = (int)tmp.size();

  if (sz % 2 == 0) {
    return (tmp[sz / 2 - 1] + tmp[sz / 2]) / 2.0;
  } else {
    return tmp[sz / 2];
  }
}

double Maximum(const vector<double>& v) {
  if (v.empty()) {
    return 0;
  }

  double res = v[0];

  for (int i = 0; i < (int)v.size(); i++) {
    res = max(res, v[i]);
  }

  return res;
}

double Minimum(const vector<double>& v) {
  if (v.empty()) {
    return 0;
  }

  double res = v[0];

  for (int i = 0; i < (int)v.size(); i++) {
    res = min(res, v[i]);
  }

  return res;
}

double Percentile(const vector<double>& v, int p) {
  if (v.empty()) {
    return 0;
  }

  int n = (int)v.size();
  int pos = p * n / 100;

  if (pos >= n) {
    pos = n - 1;
  }

  return v[pos];
}

int Compare(double numberA, double numberB) {
  double c = numberA - numberB;

  if (c <= -EPS) {
    return -1;
  }

  if (c >= EPS) {
    return 1;
  }

  return 0;
}

bool Equal(double a, double b) {
  return Abs(a - b) <= EPS;
}

bool Greater(double numberA, double numberB) {
  return Compare(numberA, numberB) > 0;
}

bool GreaterOrEqual(double numberA, double numberB) {
  return Compare(numberA, numberB) >= 0;
}

bool LessOrEqual(double numberA, double numberB) {
  return Compare(numberA, numberB) <= 0;
}

bool Less(double numberA, double numberB) {
  return Compare(numberA, numberB) < 0;
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
  auto p = std::vector<int>(n, 0);
  for (size_t i = 0; i < n; i++) {
    p[i] = i;
  }
  Rand::shuffle(p.begin(), p.end());
  return p;
}

std::vector<int> identity(size_t n) {
  auto r = std::vector<int>(n, -1);
  for (size_t i = 0; i < n; i++) {
    r[i] = i;
  }
  return r;
}

