#include "logging.h"
#include "common.h"
#include "queues.h"

#include <algorithm>
#include <iostream>
#include <vector>

using namespace std;

// Assign edges to queues using the right endpoints of earlier edges.
// If colors is null, only count the queues.
static int countAndColorQueues(const vector<pair<int, int>>& edges, const vector<int>& order, vector<int>* colors) {
  if (colors != nullptr) {
    colors->assign(edges.size(), -1);
  }
  if (edges.empty()) {
    return 0;
  }

  int n = (int) order.size();
  CHECK(n > 0);
  int mx = *std::max_element(order.begin(), order.end());
  CHECK(mx >= 0);
  // Make everything indexed on 1..n.
  auto index = vector<int>(mx + 1, -1);

  for (int i = 0; i < n; i++) {
    CHECK(0 <= order[i] && order[i] <= mx);
    CHECK(index[order[i]] == -1);
    index[order[i]] = i + 1;
  }

  // left -> (right, position in the input edge list)
  auto adjList = vector<vector<pair<int, int>>>(n + 1);

  for (int edgeIdx = 0; edgeIdx < (int)edges.size(); edgeIdx++) {
    const auto& edge = edges[edgeIdx];
    CHECK(0 <= edge.first && edge.first <= mx);
    CHECK(0 <= edge.second && edge.second <= mx);
    CHECK(index[edge.first] != -1, "vertex %d is not present in the order", edge.first);
    CHECK(index[edge.second] != -1, "vertex %d is not present in the order", edge.second);
    int u = index[edge.first];
    int v = index[edge.second];

    if (u > v) {
      swap(u, v);
    }

    CHECK(u < v && (1 <= u && u <= n) && (1 <= v && v <= n));
    adjList[u].push_back({v, edgeIdx});
  }

  // R[q] is the rightmost endpoint of an edge in queue q from an earlier left vertex.
  auto R = vector<int>(1, n + 1);

  for (int i = 0; i < n; i++) {
    int s = index[order[i]];
    CHECK(s == i + 1);
    // Select all queues before updating R: edges sharing s cannot nest each other.
    auto qst = vector<int>(adjList[s].size(), -1);

    for (int j = 0; j < (int)adjList[s].size(); j++) {
      int t = adjList[s][j].first;
      CHECK(s < t);
      auto lb = std::lower_bound(R.begin(), R.end(), t, std::greater<int>());
      int q = int(lb - R.begin());
      CHECK(q > 0 && q <= n);
      qst[j] = q;
      if (colors != nullptr) {
        (*colors)[adjList[s][j].second] = q - 1;
      }
    }

    for (int j = 0; j < (int)adjList[s].size(); j++) {
      int t = adjList[s][j].first;
      int q = qst[j];

      if (q >= (int)R.size()) {
        R.push_back(t);
      }

      R[q] = max(R[q], t);
    }

    // Only touched entries can break the descending invariant.
    for (int q : qst) {
      CHECK(R[q - 1] > R[q]);
      if (q + 1 < (int)R.size()) {
        CHECK(R[q] > R[q + 1]);
      }
    }
  }

  CHECK(R.size() >= 2);
  return int(R.size() - 1);
}

// Compute max rainbow (u1, v1, v2, u2) in O(|E| log |V|) time.
int countRainbow(const vector<pair<int, int>>& edges, const vector<int>& order) {
  return countAndColorQueues(edges, order, nullptr);
}

vector<int> colorQueueEdges(const vector<pair<int, int>>& edges, const vector<int>& order) {
  vector<int> colors;
  int pages = countAndColorQueues(edges, order, &colors);
  if (edges.empty()) {
    CHECK(pages == countRainbow(edges, order));
    return colors;
  }

  // Independently verify that no queue has a pair of nested independent edges.
  vector<int> index(*max_element(order.begin(), order.end()) + 1, -1);
  for (int i = 0; i < (int)order.size(); i++) {
    index[order[i]] = i;
  }
  vector<vector<pair<int, int>>> edgesByLeft(order.size());
  for (int i = 0; i < (int)edges.size(); i++) {
    int u = index[edges[i].first];
    int v = index[edges[i].second];
    if (u > v) {
      swap(u, v);
    }
    CHECK(0 <= colors[i] && colors[i] < pages);
    edgesByLeft[u].push_back({v, colors[i]});
  }
  vector<int> maxRight(pages, -1);
  // Hold the maximum from earlier left vertices while checking all edges of one left vertex.
  vector<int> priorRight(pages, -1);
  vector<int> lastLeft(pages, -1);
  for (int u = 0; u < (int)edgesByLeft.size(); u++) {
    for (const auto& edge : edgesByLeft[u]) {
      int v = edge.first, q = edge.second;
      if (lastLeft[q] != u) {
        priorRight[q] = maxRight[q];
      }
      CHECK(priorRight[q] <= v, "queue %d has nested independent edges", q);
      maxRight[q] = max(maxRight[q], v);
      lastLeft[q] = u;
    }
  }
  for (int q = 0; q < pages; q++) {
    CHECK(lastLeft[q] != -1);
  }
  CHECK(pages == countRainbow(edges, order));
  return colors;
}

// Compute max rainbow (u1, v1, v2, u2) in the ordering (slow DP version)
int countRainbowDP(const vector<pair<int, int>>& edges, const vector<int>& order, vector<pair<int, int>>& maxRainbow, int verbose) {
  if (edges.size() == 0) {
    return 0;
  }

  int n = (int) order.size();
  auto hasEdge = vector<vector<bool>>(n, vector<bool>(n, false));
  int mx = 0;

  for (auto o : order) {
    mx = max(mx, o + 1);
  }

  auto index = vector<int>(mx, -1);

  for (int i = 0; i < n; i++) {
    CHECK(order[i] >= 0 && order[i] < mx);
    index[order[i]] = i;
  }

  for (auto edge : edges) {
    CHECK(index[edge.first] != -1, "vertex %d is not present in the order", edge.first);
    CHECK(index[edge.second] != -1, "vertex %d is not present in the order", edge.second);
    int u = index[edge.first];
    int v = index[edge.second];
    hasEdge[u][v] = hasEdge[v][u] = true;
  }

  auto dp = vector<vector<int>>(n, vector<int>(n, -1));

  for (int i = 0; i < n; i++) {
    dp[i][i] = 0;
  }

  for (int d = 1; d < n; d++) {
    for (int i = 0; i + d < n; i++) {
      dp[i][i + d] = hasEdge[i][i + d] ? 1 : 0;
      dp[i][i + d] = max(dp[i][i + d], dp[i][i + d - 1]);
      dp[i][i + d] = max(dp[i][i + d], dp[i + 1][i + d]);

      if (d >= 2 && hasEdge[i][i + d]) {
        dp[i][i + d] = max(dp[i][i + d], 1 + dp[i + 1][i + d - 1]);
      }
    }
  }

  CHECK(dp[0][n - 1] >= 1);
  int res = dp[0][n - 1];
  int l = 0, r = n - 1;

  maxRainbow.clear();
  while (res > 0) {
    bool found = false;

    for (int i = l; i < n && !found; i++) {
      for (int j = r; j > i; j--) {
        if (hasEdge[i][j] && (res == 1 || dp[i + 1][j - 1] == res - 1)) {
          l = i + 1;
          r = j - 1;
          res--;
          found = true;

          maxRainbow.push_back(make_pair(order[i], order[j]));

          if (verbose) {
            cerr << "edge (" << order[i] << ", " << order[j] << ")\n";
          }

          break;
        }
      }
    }
  }

  return dp[0][n - 1];
}

std::vector<pair<int, int>> getMaxRainbow(const vector<pair<int, int>>& edges, const vector<int>& order) {
  vector<pair<int, int>> maxRainbow;
  int pages = countRainbowDP(edges, order, maxRainbow, 0);
  CHECK(pages == (int)maxRainbow.size());
  return maxRainbow;
}

// Compute max rainbow (u1, v1, v2, u2) in the ordering (faster O(|E| log |V|) version)

int checkRainbow(const vector<pair<int, int>>& edges, const vector<int>& order, const string& name, int maxPages, int verbose) {
  int pages = countRainbow(edges, order);
  if (verbose >= 2 && pages > maxPages) {
    vector<pair<int, int>> maxRainbow;
    countRainbowDP(edges, order, maxRainbow, 1);
  }
  VERIFY(pages <= maxPages, "max-rainbow violated for %s: %d > %d", name.c_str(), pages, maxPages);
  LOG_IF(verbose, "max-rainbow for %12s is %2d (<= %2d)", name.c_str(), pages, maxPages);
  return pages;
}

