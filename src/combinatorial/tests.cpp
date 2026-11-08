#include "bob/logging.h"
#include "bob/cmd_options.h"
#include "bob/common.h"
#include "graph_generator.h"
#include "bob/graph_algorithms.h"
#include "queue_orders.h"

#include <algorithm>
#include <array>
#include <limits>
#include <map>
#include <numeric>
#include <set>
#include <vector>

namespace {

void verifyOuterplanarLayout(
    const Adjacency& adj,
    const std::vector<int>& order,
    const std::map<EdgeTy, int>& edgeQueue,
    int verbose) {
  const int n = (int)adj.size();
  const std::vector<EdgeTy> edges = adj.to_edges();

  CHECK((int)order.size() == n, "order has %d vertices, expected %d", (int)order.size(), n);
  for (int v : order) {
    CHECK(0 <= v && v < n, "order contains invalid vertex %d", v);
  }
  inverse(order);

  // Check 1: every graph edge must be assigned exactly once to one of the two
  // queues used for the outerplanar layout.
  CHECK(edgeQueue.size() == edges.size(),
        "queue map has %d edges, expected %d", (int)edgeQueue.size(), (int)edges.size());

  std::array<std::vector<EdgeTy>, 2> queueEdges;
  for (const EdgeTy& rawEdge : edges) {
    const EdgeTy edge = make_edge(rawEdge.first, rawEdge.second);
    auto it = edgeQueue.find(edge);
    CHECK(it != edgeQueue.end(), "edge (%d,%d) has no assigned queue", edge.first, edge.second);
    const int q = it->second;
    CHECK(q == 0 || q == 1, "edge (%d,%d) has invalid queue %d", edge.first, edge.second, q);
    queueEdges[q].push_back(edge);
  }

  // Check 2: each page must be a valid queue, so no two independent edges in
  // the same queue are nested in the returned vertex order.
  for (int q = 0; q < 2; q++) {
    CHECK(countRainbow(queueEdges[q], order) <= 1,
          "queue Q%d contains a 2-rainbow", q);
  }

  // Check 3: span-one edges (Q0) form a bipartite graph, and span-two
  // edges (Q1) form a forest.
  CHECK(isBipartite(n, queueEdges[0]), "queue Q0 is not bipartite");
  CHECK(isTree(n, queueEdges[1]), "queue Q1 is not a forest");

  LOG_IF(verbose >= 2,
         "verified outerplanar layout: n=%d m=%d queues=[%d,%d]",
         n, (int)edges.size(), (int)queueEdges[0].size(), (int)queueEdges[1].size());
}

}  // namespace

static void testOP(CMDOptions& options) {
  const int n = options.getInt("-n");
  const int graphCount = options.getInt("-graphs");
  const int seed = options.getInt("-seed");
  const int verbose = options.getInt("-verbose");

  CHECK(n >= 3, "-n must be at least 3");
  CHECK(graphCount >= 1, "-graphs must be positive");

  for (int graphIdx = 0; graphIdx < graphCount; graphIdx++) {
    Rand::setSeed(seed + graphIdx);

    PlanarGraph graph;
    genOuterplanar(graph, n, 0.5);

    CHECK(graph.numberOfVertices() == n);
    CHECK(n - 1 <= graph.numberOfEdges() && graph.numberOfEdges() <= 2 * n - 3);

    Adjacency adj(n, adj_to_edges(graph.adjacencyList()));
    std::vector<int> vertices = identity(n);
    std::vector<int> order;
    std::map<EdgeTy, int> edgeQueue;

    order = buildOuterplanarOrder(adj, vertices, edgeQueue, nullptr, nullptr, verbose);
    verifyOuterplanarLayout(adj, order, edgeQueue, verbose);

    LOG_IF(verbose,
           "test-op graph %d/%d passed: |V|=%d |E|=%d seed=%d",
           graphIdx + 1, graphCount, graph.numberOfVertices(), graph.numberOfEdges(), seed + graphIdx);
  }

  LOG("test-op passed for %d graph(s) with |V|=%d", graphCount, n);
}

void testLayouts(CMDOptions& options) {
  CHECK(options.getInt("-n") >= 4, "-n must be at least 4");
  const int graphCount = options.getInt("-graphs");
  const int seed = options.getInt("-seed");
  CHECK(graphCount >= 1, "-graphs must be positive");

  // Validate the whole range before any component test adds graphIdx to an int seed.
  const long long lastSeed = static_cast<long long>(seed) + graphCount - 1;
  CHECK(lastSeed >= std::numeric_limits<int>::min() &&
        lastSeed <= std::numeric_limits<int>::max(),
        "seed range overflows a signed int");

  testOP(options);
}
