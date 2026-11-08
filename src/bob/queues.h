#pragma once

#include <string>
#include <utility>
#include <vector>

int countRainbow(const std::vector<std::pair<int, int>>& edges, const std::vector<int>& order);
int checkRainbow(const std::vector<std::pair<int, int>>& edges, const std::vector<int>& order, const std::string& name, int maxPages, int verbose = 0);
std::vector<std::pair<int, int>> getMaxRainbow(const std::vector<std::pair<int, int>>& edges, const std::vector<int>& order);

// Minimum queue colors, aligned with the input edges.
std::vector<int> colorQueueEdges(const std::vector<std::pair<int, int>>& edges, const std::vector<int>& order);
