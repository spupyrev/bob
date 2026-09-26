#pragma once

#include "adjacency.h"

#include <vector>

/// Returns depth for every vertex
std::vector<int> bfs(const int n, const std::vector<EdgeTy>& edges, const std::vector<int>& seeds);

int minDegree(int n, const std::vector<EdgeTy>& edges);
int maxDegree(int n, const std::vector<EdgeTy>& edges);
int computeGirth(int n, const std::vector<EdgeTy>& edges);
bool isConnected(int n, const std::vector<EdgeTy>& edges);
int computeDiameter(int n, const std::vector<EdgeTy>& edges);
int computeRadius(int n, const std::vector<EdgeTy>& edges);
