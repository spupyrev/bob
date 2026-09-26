#include "graph_algorithms.h"

#include <algorithm>
#include <limits>
#include <queue>
#include <set>
#include <vector>

using std::queue;
using std::vector;

static void validateSimpleGraph(const int n, const std::vector<EdgeTy>& edges) {
  CHECK(n >= 0, "negative vertex count");
  std::set<EdgeTy> uniqueEdges;
  for (auto [u, v] : edges) {
    CHECK(0 <= u && u < n && 0 <= v && v < n, "edge endpoint out of range");
    CHECK(u != v, "self-edges are not supported");
    if (u > v)
      std::swap(u, v);
    CHECK(uniqueEdges.insert({u, v}).second, "parallel edges are not supported");
    }
  }

std::vector<int> bfs(const int n, const std::vector<EdgeTy>& edges, const std::vector<int>& seeds) {
  validateSimpleGraph(n, edges);
  CHECK(!seeds.empty());
  for (int seed : seeds)
    CHECK(0 <= seed && seed < n, "BFS seed out of range");
  vector<int> depth(n, -1);
  queue<int> q;
  for (int seed : seeds) {
    depth[seed] = 0;
    q.push(seed);
  }

  Adjacency adj(n);
  adj.from_edges(edges);

  while (!q.empty()) {
    int now = q.front();
    q.pop();

    adj.forEach(now, [&](int next) {
      CHECK(now != next);
      if (depth[next] == -1) {
        depth[next] = depth[now] + 1;
        q.push(next);
      }
    });
  }

  return depth;
}

int minDegree(const int n, const std::vector<EdgeTy>& edges) {
  validateSimpleGraph(n, edges);
  std::vector<int> degree(n, 0);
  for (auto& [u, v] : edges) {
    degree[u]++;
    degree[v]++;
  }
  return degree.empty() ? 0 : *std::min_element(degree.begin(), degree.end());
}

int maxDegree(const int n, const std::vector<EdgeTy>& edges) {
  validateSimpleGraph(n, edges);
  std::vector<int> degree(n, 0);
  for (auto& [u, v] : edges) {
    degree[u]++;
    degree[v]++;
  }
  return degree.empty() ? 0 : *std::max_element(degree.begin(), degree.end());
}

int computeGirth(int n, const std::vector<EdgeTy>& edges) {
  validateSimpleGraph(n, edges);
  Adjacency adj(n);
  adj.from_edges(edges);
  int girth = std::numeric_limits<int>::max();
  for (int source = 0; source < n; ++source) {
    std::vector<int> distance(n, -1);
    std::vector<int> parent(n, -1);
    std::queue<int> queue;
    distance[source] = 0;
    queue.push(source);
    while (!queue.empty()) {
      const int u = queue.front();
      queue.pop();
      adj.forEach(u, [&](int v) {
        CHECK(u != v, "self-edges are not supported");
        if (distance[v] == -1) {
          distance[v] = distance[u] + 1;
          parent[v] = u;
          queue.push(v);
        } else if (parent[u] != v) {
          girth = std::min(girth, distance[u] + distance[v] + 1);
        }
      });
    }
  }
  return girth == std::numeric_limits<int>::max() ? -1 : girth;
}

bool isConnected(int n, const std::vector<EdgeTy>& edges) {
  validateSimpleGraph(n, edges);
  if (n == 0)
    return true;
  auto color = bfs(n, edges, {0});
  for (int i = 0; i < n; i++) {
    if (color[i] == -1)
      return false;
  }
  return true;
}

void shortestPaths(int n, const std::vector<EdgeTy>& edges, std::vector<std::vector<int>>& dist) {
  validateSimpleGraph(n, edges);
  dist = std::vector<std::vector<int>>(n, std::vector<int>(n, n + 1));
  for (int i = 0; i < n; i++) {
    dist[i][i] = 0;
  }
  for (auto e : edges) {
    int u = e.first;
    int v = e.second;
    dist[u][v] = dist[v][u] = 1;
  }
  for (int k = 0; k < n; k++) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (dist[i][j] > dist[i][k] + dist[k][j])
          dist[i][j] = dist[i][k] + dist[k][j];
      }
    }
  }
}

int computeDiameter(int n, const std::vector<EdgeTy>& edges) {
  std::vector<std::vector<int>> dist;
  shortestPaths(n, edges, dist);
  int mx = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      if (dist[i][j] > n)
        return -1;
      mx = std::max(mx, dist[i][j]);
    }
  }
  return mx;
}

int computeRadius(int n, const std::vector<EdgeTy>& edges) {
  validateSimpleGraph(n, edges);
  if (n == 0)
    return 0;
  std::vector<std::vector<int>> dist;
  shortestPaths(n, edges, dist);
  int mn = n + 1;
  for (int i = 0; i < n; i++) {
    int mx = 0;
    for (int j = 0; j < n; j++) {
      if (dist[i][j] > n)
        return -1;
      mx = std::max(mx, dist[i][j]);
    }
    mn = std::min(mn, mx);
  }
  return mn;
}
