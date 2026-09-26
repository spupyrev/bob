#include "stacks.h"

#include "common.h"
#include "logging.h"
#include "queues.h"

#include <algorithm>
#include <vector>

using namespace std;

// Compute max twist (u1, v1, u2, v2) in the ordering
int countTwist(const vector<pair<int, int>>& edges, const vector<int>& order) {
  if (edges.empty())
    return 0;
  CHECK(!order.empty(), "cannot count twists on an empty order");

  int n = (int) order.size();
  int mx = 0;

  for (auto o : order) {
    mx = max(mx, o + 1);
  }

  vector<int> index(mx, -1);

  for (int i = 0; i < n; i++) {
    CHECK(order[i] >= 0 && order[i] < mx);
    index[order[i]] = i;
  }

  for (auto edge : edges) {
    CHECK(index[edge.first] != -1, "vertex %d is not present in the order", edge.first);
    CHECK(index[edge.second] != -1, "vertex %d is not present in the order", edge.second);
  }

  int res = 0;

  // iterate over mid point
  for (int i = 0; i + 1 < n; i++) {
    // filtering out edges
    vector<pair<int, int>> filteredEdges;

    for (auto& edge : edges) {
      int u = index[edge.first];
      int v = index[edge.second];

      if (u > v) {
        swap(u, v);
      }

      if (u <= i && v >= i + 1) {
        filteredEdges.push_back(edge);
      }
    }

    // reversing order after index i
    vector<int> filteredOrder;
    filteredOrder.reserve(order.size());

    for (int j = 0; j <= i; j++) {
      filteredOrder.push_back(order[j]);
    }

    for (int j = n - 1; j >= i + 1; j--) {
      filteredOrder.push_back(order[j]);
    }

    res = max(res, countRainbow(filteredEdges, filteredOrder));
  }

  return res;
}

int checkTwist(const vector<pair<int, int>>& edges, const vector<int>& order, const string& name, int maxPages, int verbose) {
  int pages = countTwist(edges, order);
  if (verbose >= 2 && pages > maxPages) {
    LOG("violated order: %s", to_string(order).c_str());
    LOG("violated edges: ");
    for (auto e : edges) {
      LOG("  (%d, %d)", e.first, e.second);
    }
  }
  VERIFY(pages <= maxPages, "max-twist violated for %s: %d", name.c_str(), pages);
  string msg = "max-twist for " + name + " is " + to_string(pages) + " (<= " + to_string(maxPages) + ")";
  LOG_IF(verbose, msg.c_str());
  return pages;
}
