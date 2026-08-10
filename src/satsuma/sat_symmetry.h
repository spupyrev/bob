#pragma once

#include <vector>

std::pair<int, std::vector<std::vector<int>>> applySatsumaSymmetry(
    int verbose, int numVars, std::vector<std::vector<int>> &clauses);
