#include "logging.h"
#include "common.h"
#include "queues.h"

#include <algorithm>
#include <iostream>
#include <vector>

using namespace std;

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
int countRainbow(const vector<pair<int, int>>& edges, const vector<int>& order) {
  if (edges.empty()) {
    return 0;
  }

  // prepare data
  int n = (int) order.size();
  int mx = *std::max_element(order.begin(), order.end());
  // make everything indexed on 1..n
  auto index = vector<int>(mx + 1, -1);

  for (int i = 0; i < n; i++) {
    CHECK(0 <= order[i] && order[i] <= mx);
    CHECK(index[order[i]] == -1);
    index[order[i]] = i + 1;
  }

  // left -> rights
  auto adjList = vector<vector<int>>(n + 1, vector<int>());

  for (auto edge : edges) {
    CHECK(index[edge.first] != -1, "vertex %d is not present in the order", edge.first);
    CHECK(index[edge.second] != -1, "vertex %d is not present in the order", edge.second);
    int u = index[edge.first];
    int v = index[edge.second];

    if (u > v) {
      swap(u, v);
    }

    CHECK(u < v && (1 <= u && u <= n) && (1 <= v && v <= n));
    adjList[u].push_back(v);
  }

  // R[i] is the rightmost vertex of an edge assigned to queue Qi
  auto R = vector<int>();
  R.push_back(n + 1);

  for (int i = 0; i < n; i++) {
    // check R
    for (size_t j = 0; j + 1 < R.size(); j++) {
      CHECK(R[j] > R[j + 1]);
    }

    int s = index[order[i]];
    CHECK(s == i + 1);
    // queue for edge (s, adjList[s][j])
    auto qst = vector<int>(adjList[s].size(), -1);

    // first pass, find queues
    for (int j = 0; j < (int)adjList[s].size(); j++) {
      int t = adjList[s][j];
      CHECK(s < t);
      auto lb = std::lower_bound(R.begin(), R.end(), t, std::greater<int>());
      int q = int(lb - R.begin());
      CHECK(q > 0 && q <= n);
      qst[j] = q;
    }

    // second pass, update R
    for (int j = 0; j < (int)adjList[s].size(); j++) {
      int t = adjList[s][j];
      int q = qst[j];

      if (q >= (int)R.size()) {
        R.push_back(t);
      }

      R[q] = max(R[q], t);
    }
  }

  //cerr << "done countRainbowFast2\n";
  CHECK(R.size() >= 2);
  return int(R.size() - 1);
}

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

