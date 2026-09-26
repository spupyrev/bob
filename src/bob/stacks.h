#pragma once

#include <string>
#include <utility>
#include <vector>

int countTwist(const std::vector<std::pair<int, int>>& edges, const std::vector<int>& order);
int checkTwist(const std::vector<std::pair<int, int>>& edges, const std::vector<int>& order, const std::string& name, int maxPages, int verbose = 0);
