#pragma once

#include "adjacency.h"

#include <vector>
#include <set>

/// Returns depth for every vertex
std::vector<int> bfs(const int n, const std::vector<EdgeTy>& edges, const std::vector<int>& seeds);

int minDegree(int n, const std::vector<EdgeTy>& edges);
int maxDegree(int n, const std::vector<EdgeTy>& edges);
int computeGirth(int n, const std::vector<EdgeTy>& edges);
bool isConnected(int n, const std::vector<EdgeTy>& edges);
int computeDiameter(int n, const std::vector<EdgeTy>& edges);
int computeRadius(int n, const std::vector<EdgeTy>& edges);

/// Check if the graph remains connected after removing some vertices
bool isConnected(const std::vector<int>& vList, const std::vector<std::vector<int>>& adj, std::set<int>& removed);

/// Return sets of nodes, one set for each biconnected component of the graph
std::vector<std::vector<EdgeTy>> biconnectedComponents(const int n, const std::vector<EdgeTy>& edges);

/// Check if the graph is 2-(vertex)-connected
bool is2Connected(int n, const std::vector<EdgeTy>& edges);

/// Check if the graph is 3-(vertex)-connected
bool is3Connected(int n, const std::vector<EdgeTy>& edges);

/// Check if the graph is bipartite
bool isBipartite(int n, const std::vector<EdgeTy>& edges);

/// Check if the graph is a (possibly disconnected) tree (forest)
bool isTree(const int n, const std::vector<EdgeTy>& edges);
