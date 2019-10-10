#include "common.h"

#include <algorithm>
#include <random>
#include <limits>
#include <cassert>

using namespace std;

vector<string> SplitNotNull(const string& ss, const string& c) {
	string s = ss + c;
	vector<string> result;
	string tec = "";
	for (int i = 0; i < (int)s.length(); i++)
	{
		if (c.find(s[i]) != string::npos)
		{
			if ((int)tec.length() > 0) result.push_back(tec);
			tec = "";
		}
		else tec += s[i];
	}

	return result;
}

vector<int> SplitNotNullInt(const string& ss, const string& c) {
	vector<string> tmp = SplitNotNull(ss, c);
	vector<int> res;
	for (size_t i = 0; i < tmp.size(); i++) {
		res.push_back(to_int(tmp[i]));
	}
	return res;
}

double Sum(const vector<double>& v) {
	double sum = 0;
	for (int i = 0; i < (int)v.size(); i++)
		sum += v[i];
	return sum;
}

double Average(const vector<double>& v) {
	double av = Sum(v);
	if (!v.empty())
		av /= (double)v.size();
	return av;
}

double Median(const vector<double>& v) {
	if ( v.empty() ) return 0;
	if ( v.size() == 1 ) return v[0];

	vector<double> tmp = v;
	sort(tmp.begin(), tmp.end());
	int sz = (int)tmp.size();

	if ( sz % 2 == 0 )
		return (tmp[sz / 2 - 1] + tmp[sz / 2]) / 2.0;
	else
		return tmp[sz / 2];
}

double Maximum(const vector<double>& v) {
	if ( v.empty() ) return 0;

	double res = v[0];
	for (int i = 0; i < (int)v.size(); i++)
		res = max(res, v[i]);
	return res;
}

double Minimum(const vector<double>& v) {
	if (v.empty()) return 0;

	double res = v[0];
	for (int i = 0; i < (int)v.size(); i++)
		res = min(res, v[i]);
	return res;
}

double Percentile(const vector<double>& v, int p) {
	if (v.empty()) return 0;

	int n = (int)v.size();
	int pos = p * n / 100;
	if (pos >= n) pos = n - 1;
	return v[pos];
}

int Compare(double numberA, double numberB) {
    double c = numberA - numberB;
    if (c <= -EPS)
        return -1;
    if (c >= EPS)
        return 1;
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

//std::default_random_engine RNG;
std::mt19937 RNG;

size_t Rand::setSeed() {
  return setSeed(static_cast<size_t>(time(0)));
}

size_t Rand::setSeed(size_t seed) {
  RNG.seed(seed);
  next();
  return seed;
}

double Rand::nextDouble() { 
	return std::uniform_real_distribution<double>(0.0, 1.0)(RNG); 
}

bool Rand::check(double probability) {
	return nextDouble() <= probability; 
}

int Rand::next() {
	return next(0, std::numeric_limits<int>::max());
}

int Rand::next(int bound) {
	return next(0, bound);
}

int Rand::next(int lower, int upper) {
  assert(lower < upper);
  return std::uniform_int_distribution<int>(lower, upper - 1)(RNG);
}

void Rand::shuffle(vector<size_t>& vec) {
  std::shuffle(vec.begin(), vec.end(), RNG);
}

void Rand::shuffle(vector<int>& vec) {
  std::shuffle(vec.begin(), vec.end(), RNG);
}

vector<int> Rand::permutation(size_t n) {
  vector<int> p = vector<int>(n, 0);
  for (size_t i = 0; i < n; i++) {
    p[i] = i;
  }
  std::shuffle(p.begin(), p.end(), RNG);
  return p;
}
