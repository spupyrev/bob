#include "common.h"

using namespace std;

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
