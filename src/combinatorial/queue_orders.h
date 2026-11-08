#pragma once

#include "bob/logging.h"
#include "bob/queues.h"
#include "bob/adjacency.h"

#include <vector>
#include <map>

struct TreePartition {
  int verbose;

  std::vector<int> vertex2depth;
  std::vector<int> vertex2parent;
  std::vector<int> vertex2bag;

  int numBags;
  int maxDepth;
  std::vector<std::vector<int>> bags;
  std::vector<int> bag2depth;
  std::vector<std::vector<int>> bag2parents;

  explicit TreePartition(int verbose = 0) : verbose(verbose) {}

  void build(const Adjacency& adj, const std::vector<int>& sources);
  void build(const Adjacency& adj, const std::vector<int>& sources,
             const std::vector<int>& vertices);
  std::vector<int> getConnectedComponent(
      const Adjacency& adj, const std::vector<int>& sources,
      const std::vector<int>& vertices);
};

class PlanarGraph;

// Construct and verify a 48- or 33-queue layout of a simple plane graph.
// The connected input may be enlarged to a triangulation with an
// outer BFS root; outputs refer only to its original vertices and edges.
// Input rotations are clockwise; the graph may be modified in place.
void buildPPSLayout(
    PlanarGraph& graph,
    int queueBound,
    std::vector<int>& resultOrder,
    std::map<EdgeTy, int>& resultEdgeQueue,
    int verbose = 0);

// queue orderings
// Optional coordinates are indexed by vertex ID (size adjAll.size(), -1 outside vertices).
std::vector<int> buildOuterplanarOrder(
    const Adjacency& adjAll,
    const std::vector<int>& vertices,
    std::map<EdgeTy, int>& resEdgeQueue,
    std::vector<int>* resX = nullptr,
    std::vector<int>* resY = nullptr,
    int verbose = 0);
