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

bool isBipartite(int n, const std::vector<EdgeTy>& edges, vector<int>& part1, vector<int>& part2) {
  vector<int> depth(n, -1);
  Adjacency adj(n);
  adj.from_edges(edges);

  for (int i = 0; i < n; i++) {
    if (depth[i] != -1) continue;
    int now = i;
    depth[now] = 0;
    queue<int> q;
    q.push(now);

    while (!q.empty()) {
      now = q.front();
      q.pop();

      adj.forEach(now, [&](int next) {
        CHECK(now != next);
        if (depth[next] == -1) {
          depth[next] = depth[now] + 1;
          q.push(next);
        }
      });
    }
  }

  for (auto& edge : edges) {
    int color1 = depth[edge.first] % 2;
    int color2 = depth[edge.second] % 2;

    if (color1 == color2)
      return false;
  }

  for (int i = 0; i < n; i++) {
    if (depth[i] % 2 == 0)
      part1.push_back(i);
    else
      part2.push_back(i);
  }

  return true;
}

bool isBipartite(int n, const std::vector<EdgeTy>& edges) {
  vector<int> part1;
  vector<int> part2;
  return isBipartite(n, edges, part1, part2);
}

bool isConnected(const vector<int>& vList, const vector<vector<int>>& adj, std::set<int>& removed) {
  queue<int> q;
  std::set<int> processed;

  for (size_t i = 0; i < vList.size(); i++) {
    if (!removed.count(vList[i])) {
      q.push(vList[i]);
      processed.insert(vList[i]);
      break;
    }
  }

  while (!q.empty()) {
    int now = q.front();
    q.pop();

    for (size_t i = 0; i < adj[now].size(); i++) {
      int next = adj[now][i];

      if (removed.count(next)) {
        continue;
      }

      if (processed.find(next) != processed.end()) {
        continue;
      }

      q.push(next);
      processed.insert(next);
    }
  }

  return (processed.size() + removed.size() == vList.size());
}

/// Depth-first search algorithm to generate articulation points and biconnected components
std::vector<std::vector<EdgeTy>> biconnectedComponents(const int n, const std::vector<EdgeTy>& edges) {
  // Initialize disc and low, and parent arrays
  std::vector<int> discovery(n, -1);
  std::vector<int> low(n, -1);
  std::vector<int> parent(n, -1);
  std::vector<EdgeTy> edge_stack;
  int cur_time = 0;

  Adjacency adj(n);
  adj.from_edges(edges);

  std::vector<std::vector<EdgeTy>> bicomponents;
  bicomponents.push_back({});

  struct Frame {
    int vertex;
    size_t nextNeighbor;
    int children;
  };
  std::vector<Frame> dfsStack;
  dfsStack.reserve(n);

  for (int i = 0; i < n; i++) {
    if (discovery[i] == -1) {
      discovery[i] = low[i] = ++cur_time;
      dfsStack.push_back({i, 0, 0});
      while (!dfsStack.empty()) {
        Frame& frame = dfsStack.back();
        const int now = frame.vertex;
        if (frame.nextNeighbor < adj.degree(now)) {
          const int next = adj.get(now, frame.nextNeighbor++);
          CHECK(now != next);
          if (discovery[next] == -1) {
            frame.children++;
            parent[next] = now;
            edge_stack.push_back({now, next});
            discovery[next] = low[next] = ++cur_time;
            dfsStack.push_back({next, 0, 0});
          } else if (next != parent[now]) {
            low[now] = std::min(low[now], discovery[next]);
            if (discovery[next] < discovery[now]) {
              edge_stack.push_back({now, next});
            }
          }
          continue;
        }

        dfsStack.pop_back();
        if (parent[now] == -1) {
          continue;
        }
        const int p = parent[now];
        low[p] = std::min(low[p], low[now]);
        const Frame& parentFrame = dfsStack.back();
        if ((parent[p] == -1 && parentFrame.children > 1) ||
            (parent[p] != -1 && low[now] >= discovery[p])) {
          CHECK(!edge_stack.empty());
          while (edge_stack.back().first != p || edge_stack.back().second != now) {
            bicomponents.back().push_back(make_edge(
                edge_stack.back().first, edge_stack.back().second));
            edge_stack.pop_back();
            CHECK(!edge_stack.empty());
          }
          bicomponents.back().push_back(make_edge(
              edge_stack.back().first, edge_stack.back().second));
          edge_stack.pop_back();
          bicomponents.push_back({});
        }
      }
    }

    // If the edge stack is not empty, pop all edges from the stack
    while (!edge_stack.empty()) {
      const int u = std::min(edge_stack.back().first, edge_stack.back().second);
      const int v = std::max(edge_stack.back().first, edge_stack.back().second);
      bicomponents.back().push_back({u, v});
      edge_stack.pop_back();
    }
    if (!bicomponents.back().empty()) {
      bicomponents.push_back({});
    }
  }

  CHECK(bicomponents.back().empty());
  bicomponents.pop_back();
  return bicomponents;
}

bool is2Connected(int n, const std::vector<EdgeTy>& edges) {
  CHECK(n > 0);
  // Edge components omit isolated vertices, so check connectivity first.
  if (!isConnected(n, edges)) {
    return false;
  }
  auto biComponents = biconnectedComponents(n, edges);
  return biComponents.size() == 1;
}

bool is3Connected(int n, const std::vector<EdgeTy>& edges) {
  CHECK(n >= 3);
  if (!is2Connected(n, edges)) {
    return false;
  }

  for (int removed = 0; removed < n; removed++) {
    vector<int> label(n, -1);
    for (int v = 0, next = 0; v < n; v++) {
      if (v != removed) {
        label[v] = next++;
      }
    }

    vector<EdgeTy> remainingEdges;
    remainingEdges.reserve(edges.size());
    for (EdgeTy edge : edges) {
      if (edge.first == removed || edge.second == removed) {
        continue;
      }
      const int u = label[edge.first], v = label[edge.second];
      remainingEdges.push_back({std::min(u, v), std::max(u, v)});
    }
    if (!is2Connected(n - 1, remainingEdges)) {
      return false;
    }
  }
  return true;
}

bool isTree(const int n, const std::vector<EdgeTy>& edges) {
  if (edges.empty()) {
    return true;
  }

  Adjacency adj(n);
  adj.from_edges(edges);
  std::vector<int> degree(n, 0);
  for (int i = 0; i < n; i++) {
    degree[i] = adj.degree(i);
  }

  std::vector<bool> alive(n, true);
  int numAlive = n;
  while (numAlive > 0) {
    bool progress = false;
    for (int i = 0; i < n; i++) {
      if (!alive[i]) continue;
      if (degree[i] > 1) continue;

      progress = true;
      alive[i] = false;
      numAlive--;
      adj.forEach(i, [&](int j) {
        if (alive[j]) {
          CHECK(degree[j] >= 1);
          degree[j]--;
        }
      });
    }

    if (!progress)
      return false;
  }

  return true;
}
