#include "bob/logging.h"
#include "bob/common.h"
#include "queue_orders.h"
#include "augmentation.h"

#include <algorithm>
#include <functional>
#include <iostream>
#include <queue>
#include <vector>

using namespace std;

// run BFS and extract the bags
void TreePartition::build(const Adjacency& adj, const vector<int>& sources) {
  auto vertices = vector<int>(adj.size(), 0);

  for (int i = 0; i < (int)adj.size(); i++) {
    vertices[i] = i;
  }

  build(adj, sources, vertices);
}

// run BFS and extract the bags
void TreePartition::build(const Adjacency& adjAll, const vector<int>& sources, const vector<int>& vertices) {
  if (verbose >= 3) {
    cerr << "Building TreePartition for\n";
    cerr << "  vertices: " << to_string(vertices) << "\n";
    cerr << "  sources: " << to_string(sources) << "\n";
  }

  int n = (int)adjAll.size();
  Adjacency adj(n);
  adjAll.init_slice(adj, vertices);

  // find tree-partition
  vertex2depth = vector<int>(n, -1);
  vertex2parent = vector<int>(n, -1);
  queue<int> q;

  for (int s : sources) {
    CHECK(find(vertices.begin(), vertices.end(), s) != vertices.end());
    q.push(s);
    vertex2depth[s] = 0;
  }

  while (!q.empty()) {
    int now = q.front();
    q.pop();

    adj.forEach(now, [&](int next) {
      if (vertex2depth[next] == -1) {
        vertex2depth[next] = vertex2depth[now] + 1;
        vertex2parent[next] = now;
        q.push(next);
      }
    });
  }

  maxDepth = *std::max_element(vertex2depth.begin(), vertex2depth.end());
  vertex2bag = vector<int>(n, -1);
  numBags = 0;

  for (int d = 0; d <= maxDepth; d++) {
    LOG_IF(verbose >= 3, "  processing depth-%d vertices", d);
    // collect vertices at depth d
    vector<int> vertD;

    for (int v : vertices) {
      if (vertex2depth[v] == d) {
        vertD.push_back(v);
      }
    }

    if (vertD.empty()) {
      continue;
    }

    // get connected components of depth-D vertices
    for (size_t i = 0; i < vertD.size(); i++) {
      CHECK(vertex2depth[vertD[i]] == d);

      if (vertex2bag[vertD[i]] == -1) {
        auto cc = getConnectedComponent(adj, {vertD[i]}, vertD);
        sort(cc.begin(), cc.end());

        for (int v : cc) {
          vertex2bag[v] = numBags;
        }

        if (verbose >= 3) {
          cerr << "  bag[" << numBags << "] = " << to_string(cc) << "\n";
        }

        bags.push_back(cc);
        bag2depth.push_back(d);
        numBags++;
      }
    }
  }

  // verify correctness of the tree-partition
  CHECK(numBags > 0);

  for (int i = 0; i < numBags; i++) {
    // collect parents of the i-th bag
    vector<int> parents;

    for (int j : vertices) {
      bool isNeighbor = false;

      for (size_t k = 0; k < bags[i].size(); k++) {
        int u = bags[i][k];
        CHECK(vertex2bag[u] == i);

        if (vertex2bag[j] != i && vertex2depth[j] < vertex2depth[u] && adj.test(j, u)) {
          isNeighbor = true;
          break;
        }
      }

      if (isNeighbor) {
        parents.push_back(j);
      }
    }

    sort(parents.begin(), parents.end());
    bag2parents.push_back(parents);

    if (verbose >= 3) {
      cerr << "  parents of bag[" << i << "] = " << to_string(parents) << "\n";
    }
  }

  CHECK((int) bag2parents.size() == numBags);
  size_t numAssigned = 0;

  for (int i = 0; i < n; i++) {
    if (vertex2depth[i] != -1) {
      numAssigned++;
    }
  }

  CHECK(numAssigned == vertices.size(), "numAssigned = %d", numAssigned);
}

// returns the connected component
vector<int> TreePartition::getConnectedComponent(const Adjacency& adj, const vector<int>& sources, const vector<int>& vertices) {
  CHECK(!vertices.empty());
  CHECK(!sources.empty());

  if (vertices.size() == 1) {
    CHECK(vertices == sources);
    return {vertices[0]};
  }

  for (size_t i = 0; i < sources.size(); i++) {
    CHECK(find(vertices.begin(), vertices.end(), sources[i]) != vertices.end());
    for (size_t j = i + 1; j < sources.size(); j++) {
      CHECK(adj.test(sources[i], sources[j]));
    }
  }

  adj.init_slice(vertices);
  auto used = vector<bool>(adj.size(), false);
  auto cc = vector<int>();
  queue<int> q;

  for (int s : sources) {
    q.push(s);
    used[s] = true;
    cc.push_back(s);
  }

  while (!q.empty()) {
    int now = q.front();
    q.pop();

    adj.forEachSliced(now, [&](int next) {
      if (!used[next]) {
        q.push(next);
        used[next] = true;
        cc.push_back(next);
      }
    });
  }

  adj.clear_slice();
  return cc;
}

// Coordinate arrays are indexed by vertex ID; vertices outside the slice stay -1.
static void publishOuterplanarCoordinates(
    const vector<int>& vertices,
    const vector<EdgeTy>& supportEdges,
    const vector<int>& x,
    const vector<int>& y,
    vector<int>* resX,
    vector<int>* resY) {
  if (resX == nullptr && resY == nullptr) {
    return;
  }

  CHECK(x.size() == y.size());
  vector<bool> usedX(vertices.size(), false);
  for (int v : vertices) {
    CHECK(0 <= v && v < (int)x.size());
    CHECK(0 <= x[v] && x[v] < (int)vertices.size() && y[v] >= 0,
          "invalid outerplanar coordinates for vertex %d: x=%d y=%d", v, x[v], y[v]);
    CHECK(!usedX[x[v]], "duplicate outerplanar x coordinate %d", x[v]);
    usedX[x[v]] = true;
  }
  for (const EdgeTy& edge : supportEdges) {
    CHECK(0 <= edge.first && edge.first < (int)x.size());
    CHECK(0 <= edge.second && edge.second < (int)x.size());
    CHECK(x[edge.first] >= 0 && x[edge.second] >= 0);
    CHECK(y[edge.first] >= 0 && y[edge.second] >= 0);
    const int span = abs(y[edge.first] - y[edge.second]);
    CHECK(span == 1 || span == 2,
          "incorrect support span %d for edge (%d,%d)", span, edge.first, edge.second);
  }

  if (resX != nullptr) {
    *resX = x;
  }
  if (resY != nullptr) {
    *resY = y;
  }
}

vector<int> buildOuterplanarOrder(
    const Adjacency& adjAll,
    const vector<int>& vertices,
    map<EdgeTy, int>& resEdgeQueue,
    vector<int>* resX,
    vector<int>* resY, int verbose) {
  CHECK(!vertices.empty());
  CHECK(resEdgeQueue.empty());
  CHECK(resX == nullptr || resY == nullptr || resX != resY);

  const int n = (int)vertices.size();
  const int nAll = (int)adjAll.size();
  if (resX != nullptr || resY != nullptr) {
    for (int v : vertices) {
      CHECK(0 <= v && v < nAll);
    }
  }
  if (n <= 2) {
    if (n == 2) {
      CHECK(adjAll.test(vertices[0], vertices[1]));
      resEdgeQueue[make_edge(vertices[0], vertices[1])] = 0;
    }
    if (resX != nullptr || resY != nullptr) {
      vector<int> x(nAll, -1);
      vector<int> y(nAll, -1);
      for (int i = 0; i < n; i++) {
        x[vertices[i]] = i;
        y[vertices[i]] = i;
      }
      vector<EdgeTy> supportEdges;
      if (n == 2) {
        supportEdges.push_back(make_edge(vertices[0], vertices[1]));
      }
      publishOuterplanarCoordinates(vertices, supportEdges, x, y, resX, resY);
    }
    return vertices;
  }

  LOG_IF(verbose, "buildOuterplanarOrder: n = %d", n);

  const int maximalEdgeCount = 2 * n - 3;
  const auto originalEdges = filter_edges(nAll, adjAll.to_edges(), vertices);
  CHECK((int)originalEdges.size() <= maximalEdgeCount,
        "outerplanar slice has too many edges: n=%d m=%d vertices=%s",
        n, (int)originalEdges.size(), to_string(vertices).c_str());

  // augment to a maximal outerplanar
  vector<EdgeTy> edges = originalEdges;
  if ((int)originalEdges.size() < maximalEdgeCount) {
    vector<int> oldToNew(nAll, -1);
    for (int i = 0; i < n; i++) {
      oldToNew[vertices[i]] = i;
    }
    const vector<EdgeTy> compactEdges = relabel_edges(edges, oldToNew);
    vector<EdgeTy> compactAugmentedEdges;
    augmentOuterplanar(n, compactEdges, compactAugmentedEdges, verbose);
    edges = relabel_edges(compactAugmentedEdges, vertices);
  }

  Adjacency adj(nAll);
  adj.from_edges(edges);

  CHECK((int)edges.size() == maximalEdgeCount,
        "input outerplanar graph is not maximal: n=%d m=%d", n, (int)edges.size());

  // Find an outer-face edge (s,t).  In a maximal outerplanar graph, every edge
  // incident to a degree-2 vertex is on the outer face.
  int s = -1;
  int t = -1;
  for (int v : vertices) {
    if (adj.degree(v) == 2) {
      s = v;
      t = adj.get(s, 0);
      break;
    }
  }
  CHECK(s != -1 && t != -1);

  map<EdgeTy, int> splitVertex;
  vector<bool> processed(nAll, false);
  processed[s] = true;
  processed[t] = true;
  int processedCount = 2;

  function<void(int, int)> buildSplitTree = [&](int u, int w) {
    // The apex of the triangle on (u, w): the unprocessed common neighbor.
    // Scan the neighbors of the endpoint with the smaller degree.
    int x = -1;
    const int scan = adj.degree(u) <= adj.degree(w) ? u : w;
    const int other = scan == u ? w : u;
    adj.forEach(scan, [&](int candidate) {
      if (processed[candidate] || !adj.test(other, candidate)) {
        return;
      }
      CHECK(x == -1,
            "edge (%d,%d) has multiple unprocessed common neighbors",
            u, w);
      x = candidate;
    });

    if (x == -1) {
      return;
    }

    const EdgeTy edge = make_edge(u, w);
    CHECK(!splitVertex.count(edge), "edge (%d,%d) is split twice", edge.first, edge.second);
    splitVertex[edge] = x;
    processed[x] = true;
    processedCount++;
    buildSplitTree(u, x);
    buildSplitTree(x, w);
  };
  buildSplitTree(s, t);
  CHECK(processedCount == n, "split tree processed %d vertices, expected %d", processedCount, n);

  map<EdgeTy, int> widthMemo;
  function<int(EdgeTy)> width = [&](EdgeTy edge) {
    auto memoIt = widthMemo.find(edge);
    if (memoIt != widthMemo.end()) {
      return memoIt->second;
    }

    auto splitIt = splitVertex.find(edge);
    if (splitIt == splitVertex.end()) {
      widthMemo[edge] = 1;
      return 1;
    }

    const int v = splitIt->second;
    const int res = width(make_edge(edge.first, v)) + width(make_edge(v, edge.second));
    widthMemo[edge] = res;
    return res;
  };

  vector<int> x(nAll, -1);
  vector<int> y(nAll, -1);
  x[s] = 0;
  y[s] = 0;
  x[t] = width(make_edge(s, t));
  // The starting outer edge has span one.
  y[t] = 1;

  function<void(int, int)> assignY = [&](int u, int w) {
    const EdgeTy edge = make_edge(u, w);
    auto splitIt = splitVertex.find(edge);
    if (splitIt == splitVertex.end()) {
      return;
    }

    const int v = splitIt->second;
    const int span = abs(y[u] - y[w]);
    CHECK(span == 1 || span == 2,
          "incorrect parent span %d for vertex %d between %d and %d", span, v, u, w);
    if (span == 1) {
      y[v] = max(y[u], y[w]) + 1;
    } else {
      y[v] = (y[u] + y[w]) / 2;
    }
    assignY(u, v);
    assignY(v, w);
  };
  assignY(s, t);

  function<void(int, int)> assignX = [&](int left, int right) {
    const EdgeTy edge = make_edge(left, right);
    auto splitIt = splitVertex.find(edge);
    if (splitIt == splitVertex.end()) {
      return;
    }

    const int v = splitIt->second;
    x[v] = x[left] + width(make_edge(left, v));
    assignX(left, v);
    assignX(v, right);
  };
  assignX(s, t);

  if (verbose >= 3) {
    LOG("  outerplanar coordinates:");
    for (int v : vertices) {
      CHECK(x[v] != -1 && y[v] != -1);
      LOG("    v=%d x=%d y=%d", v, x[v], y[v]);
    }
  }

  // Track by track from bottom to top, left to right within a track.
  vector<int> order = vertices;
  stable_sort(order.begin(), order.end(), [&](int l, int r) {
    CHECK(x[l] != -1 && x[r] != -1 && y[l] != -1 && y[r] != -1);
    return make_pair(y[l], x[l]) < make_pair(y[r], x[r]);
  });

  for (const EdgeTy& edge : originalEdges) {
    const int span = abs(y[edge.first] - y[edge.second]);
    CHECK(span == 1 || span == 2,
          "incorrect edge span %d for edge (%d,%d)", span, edge.first, edge.second);
    resEdgeQueue[make_edge(edge.first, edge.second)] = span - 1;
  }

  LOG_IF(verbose, "completed buildOuterplanarOrder; order: %s", to_string(order).c_str());

  publishOuterplanarCoordinates(vertices, edges, x, y, resX, resY);
  return order;
}
