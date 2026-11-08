#include "bob/graph_algorithms.h"

#include <iostream>
#include <vector>

static void checkBiconnected(int n, const std::vector<EdgeTy>& edges, bool expected) {
  CHECK(is2Connected(n, edges) == expected,
        "incorrect biconnectivity for n=%d m=%d", n, (int)edges.size());
}

int main() {
  try {
    const std::vector<EdgeTy> triangle = {{0, 1}, {1, 2}, {0, 2}};
    checkBiconnected(3, triangle, true);
    // The triangle is one edge block, but the fourth vertex is isolated.
    checkBiconnected(4, triangle, false);
    checkBiconnected(3, {{0, 1}}, false);
    checkBiconnected(1, {}, false);
    checkBiconnected(4, {{0, 1}, {1, 2}, {2, 3}, {0, 3}}, true);
    checkBiconnected(4, {{0, 1}, {1, 2}, {2, 3}}, false);
    checkBiconnected(5, {{0, 1}, {1, 2}, {0, 2}, {2, 3}, {3, 4}, {2, 4}}, false);
    checkBiconnected(6, {{0, 1}, {1, 2}, {0, 2}, {3, 4}, {4, 5}, {3, 5}}, false);
    const std::vector<EdgeTy> k4 = {{0, 1}, {0, 2}, {0, 3}, {1, 2}, {1, 3}, {2, 3}};
    CHECK(is3Connected(4, k4));
    CHECK(!is3Connected(5, k4));
    std::cout << "Graph connectivity tests passed.\n";
  } catch (int code) {
    return code;
  }
  return 0;
}
