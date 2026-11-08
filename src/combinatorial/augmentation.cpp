#include "augmentation.h"
#include "planar_graph.h"
#include "bob/adjacency.h"

#include <algorithm>
#include <functional>
#include <vector>
#include <set>
#include <queue>
#include <unordered_map>

void augmentOuterplanar(const int n,
                        const std::vector<EdgeTy>& edges,
                        std::vector<EdgeTy>& augmentedEdges, int verbose) {
  CHECK(n >= 3);
  CHECK(isConnected(n, edges), "input outerplanar graph is not connected");
  CHECK((int)edges.size() < 2 * n - 3,
        "input outerplanar graph has nothing to augment");

  auto addEdge = [](Adjacency& adj, int u, int v) {
    if (!adj.test(u, v)) {
      adj.set(u, v);
      adj.set(v, u);
    }
  };

  Adjacency augmentedAdj(n);
  augmentedAdj.from_edges(edges);

  // Triangulate a single biconnected outerplanar block by repeatedly removing
  // an ear. The reverse removal order recovers the block's outer boundary.
  auto triangulateBlock = [&](const std::vector<int>& blockVertices) {
    if (blockVertices.size() <= 3) {
      return blockVertices;
    }

    std::vector<bool> active(n, false);
    for (int v : blockVertices) {
      active[v] = true;
    }

    auto collectActiveNeighbors = [&](int v, std::vector<int>& neighbors) {
      neighbors.clear();
      augmentedAdj.forEach(v, [&](int u) {
        if (active[u]) {
          neighbors.push_back(u);
        }
      });
    };

    struct Ear {
      int v;
      int u;
      int w;
    };

    std::vector<Ear> ears;
    std::vector<int> neighbors;
    neighbors.reserve(blockVertices.size());
    int activeCount = (int)blockVertices.size();
    while (activeCount > 2) {
      int v = -1;
      for (int candidate : blockVertices) {
        if (!active[candidate]) {
          continue;
        }
        collectActiveNeighbors(candidate, neighbors);
        if (neighbors.size() == 2) {
          v = candidate;
          break;
        }
      }
      CHECK(v != -1, "failed to find a degree-2 vertex while augmenting a block");

      const int u = neighbors[0];
      const int w = neighbors[1];
      addEdge(augmentedAdj, u, w);
      ears.push_back({v, u, w});

      active[v] = false;
      activeCount--;
    }

    std::vector<int> cycle;
    for (int v : blockVertices) {
      if (active[v]) {
        cycle.push_back(v);
      }
    }
    CHECK(cycle.size() == 2);
    CHECK(augmentedAdj.test(cycle[0], cycle[1]));

    for (auto it = ears.rbegin(); it != ears.rend(); ++it) {
      bool inserted = false;
      for (int i = 0; i < (int)cycle.size(); i++) {
        const int j = (i + 1) % (int)cycle.size();
        if ((cycle[i] == it->u && cycle[j] == it->w) ||
            (cycle[i] == it->w && cycle[j] == it->u)) {
          cycle.insert(cycle.begin() + j, it->v);
          inserted = true;
          break;
        }
      }
      CHECK(inserted, "failed to replay an ear in the block outer cycle");
    }

    return cycle;
  };

  auto rotateToFront = [](std::vector<int> cycle, int v) {
    auto it = std::find(cycle.begin(), cycle.end(), v);
    CHECK(it != cycle.end());
    std::rotate(cycle.begin(), it, cycle.end());
    return cycle;
  };

  const auto components = biconnectedComponents(n, edges);
  CHECK(!components.empty());

  const int numBlocks = (int)components.size();
  std::vector<std::vector<int>> blockCycle(numBlocks);
  std::vector<std::vector<int>> incidentBlocks(n);
  for (int b = 0; b < numBlocks; b++) {
    const auto vertices = vertices_of(components[b]);
    blockCycle[b] = triangulateBlock(vertices);
    CHECK(blockCycle[b].size() == vertices.size());
    for (int v : vertices) {
      CHECK(0 <= v && v < n);
      incidentBlocks[v].push_back(b);
    }
  }

  int rootBlock = 0;
  for (int b = 0; b < numBlocks; b++) {
    int blockDegree = 0;
    for (int v : blockCycle[b]) {
      blockDegree += (int)incidentBlocks[v].size() - 1;
    }
    if (blockDegree <= 1) {
      rootBlock = b;
      break;
    }
  }

  std::vector<EdgeTy> spliceEdges;
  std::vector<bool> usedBlock(numBlocks, false);
  std::function<std::vector<int>(int, int)> emitCycle = [&](int b, int parentArticulation) {
    CHECK(!usedBlock[b]);
    usedBlock[b] = true;

    std::vector<int> result;
    const std::vector<int>& cycle = blockCycle[b];
    for (int i = 0; i < (int)cycle.size(); i++) {
      const int v = cycle[i];
      result.push_back(v);
      if (v == parentArticulation) {
        continue;
      }

      std::vector<std::vector<int>> childCycles;
      int curSucc = cycle[(i + 1) % (int)cycle.size()];
      for (int childBlock : incidentBlocks[v]) {
        if (!usedBlock[childBlock]) {
          std::vector<int> childCycle = rotateToFront(emitCycle(childBlock, v), v);
          CHECK(childCycle.size() >= 2);
          spliceEdges.push_back(make_edge(childCycle[1], curSucc));
          curSucc = childCycle.back();
          childCycles.push_back(std::move(childCycle));
        }
      }
      for (int c = (int)childCycles.size() - 1; c >= 0; c--) {
        for (int j = (int)childCycles[c].size() - 1; j >= 1; j--) {
          result.push_back(childCycles[c][j]);
        }
      }
    }
    return result;
  };

  const std::vector<int> globalCycle = emitCycle(rootBlock, -1);

  for (int b = 0; b < numBlocks; b++) {
    CHECK(usedBlock[b], "block %d was not emitted", b);
  }
  CHECK(globalCycle.size() == (size_t)n);
  std::set<int> seen(globalCycle.begin(), globalCycle.end());
  CHECK(seen.size() == (size_t)n);

  for (const EdgeTy& edge : spliceEdges) {
    addEdge(augmentedAdj, edge.first, edge.second);
  }
  for (int i = 0; i < n; i++) {
    const int u = globalCycle[i];
    const int v = globalCycle[(i + 1) % n];
    addEdge(augmentedAdj, u, v);
  }

  augmentedEdges = augmentedAdj.to_edges();
  CHECK(augmentedEdges.size() == (size_t)(2 * n - 3),
        "outerplanar augmentation produced %d edges, expected %d",
        (int)augmentedEdges.size(), 2 * n - 3);

  LOG_IF(verbose,
         "augmented outerplanar graph: n=%d m=%d -> %d",
         n, (int)edges.size(), (int)augmentedEdges.size());
}

namespace {

// Enumerate oriented face walks, including both sides of a bridge. The
// designated outer face can revisit vertices, so a vertex-set face key is
// insufficient here.
void checkOuterplaneFaces(const PlanarGraph& graph) {
  const Face& outer = graph.outerFace;
  CHECK(outer.length() >= 3 && outer.edges.size() == outer.vertices.size(),
        "the designated outer face must be a face walk");
  for (int i = 0; i < outer.length(); i++) {
    Vertex* v = outer.vertices[i];
    Vertex* next = outer.vertices[(i + 1) % outer.length()];
    CHECK(0 <= v->index && v->index < graph.numberOfVertices() &&
          graph.vertices[v->index] == v);
    CHECK(outer.edges[i]->incident(v) && outer.edges[i]->other(v) == next,
          "the designated outer-face walk has an incorrect edge at vertex %d",
          v->index);
  }
  CHECK(graph.extractRightFace(outer.vertices[0], outer.edges[0]) == outer,
        "the designated outer face does not match the oriented embedding");

  std::vector<bool> onOuter(graph.numberOfVertices(), false);
  for (Vertex* v : outer.vertices) {
    onOuter[v->index] = true;
  }
  for (int v = 0; v < graph.numberOfVertices(); v++) {
    CHECK(onOuter[v], "vertex %d is not incident to the designated outer face", v);
  }

  std::set<EdgeTy> seenDarts;
  const std::vector<Edge*> edges = graph.extractEdges();
  for (Edge* edge : edges) {
    for (Vertex* start : {edge->source, edge->target}) {
      if (seenDarts.count({start->index, edge->other(start)->index})) {
        continue;
      }
      const Face face = graph.extractRightFace(start, edge);
      if (!(face == outer)) {
        CHECK(face.length() == 3,
              "bounded face at edge (%d,%d) has length %d, expected 3",
              edge->source->index, edge->target->index, face.length());
      }
      CHECK(face.vertices.size() == face.edges.size());
      for (int i = 0; i < face.length(); i++) {
        Vertex* v = face.vertices[i];
        CHECK(seenDarts.insert({v->index, face.edges[i]->other(v)->index}).second,
              "face walks overlap in the oriented embedding");
      }
    }
  }
  CHECK(seenDarts.size() == 2 * edges.size(),
        "the oriented embedding does not cover every edge side");
}

}  // namespace

void augmentOuterplanar(PlanarGraph& graph, int verbose) {
  const int n = graph.numberOfVertices();
  CHECK(n >= 3,
        "embedded outerplane augmentation requires at least 3 existing vertices; "
        "n=1 or n=2 needs auxiliary vertices to reach a triangulated polygon");
  CHECK(!graph.directed, "embedded outerplane augmentation requires an undirected graph");
  CHECK(graph.checkConsistency(false), "input embedding is inconsistent");

  const std::vector<Edge*> originalEdges = graph.extractEdges();
  std::vector<EdgeTy> originalEndpoints;
  const int originalEdgeCount = (int)originalEdges.size();
  CHECK(originalEdgeCount == graph.numberOfEdges());
  std::set<EdgeTy> originalPairs;
  for (Edge* edge : originalEdges) {
    const EdgeTy endpoints = make_edge(edge->source->index, edge->target->index);
    CHECK(endpoints.first != endpoints.second, "input contains a loop");
    CHECK(originalPairs.insert(endpoints).second,
          "input contains parallel edges (%d,%d)", endpoints.first, endpoints.second);
    originalEndpoints.push_back(endpoints);
  }
  CHECK(isConnected(n, graph.extractEdgesId()), "input graph is not connected");
  CHECK(originalEdgeCount <= 2 * n - 3, "input has too many edges for an outerplane graph");
  checkOuterplaneFaces(graph);

  std::vector<std::vector<Edge*>> originalRotations(n);
  for (int v = 0; v < n; v++) {
    originalRotations[v] = graph.vertices[v]->edges;
  }

  int previousBlockCount = n;
  while (true) {
    const auto blocks = biconnectedComponents(n, graph.extractEdgesId());
    CHECK(!blocks.empty());
    CHECK((int)blocks.size() < previousBlockCount,
          "outer-face collar insertion did not reduce the number of blocks");
    previousBlockCount = (int)blocks.size();
    if (blocks.size() == 1) {
      break;
    }

    // Count distinct blocks incident with each vertex. A leaf block has one
    // cutvertex; all its other vertices occur in no other block.
    std::vector<int> incidentBlocks(n, 0);
    std::vector<int> lastSeen(n, -1);
    for (int b = 0; b < (int)blocks.size(); b++) {
      for (const EdgeTy& edge : blocks[b]) {
        for (int v : {edge.first, edge.second}) {
          if (lastSeen[v] != b) {
            lastSeen[v] = b;
            incidentBlocks[v]++;
          }
        }
      }
    }

    int leafBlock = -1;
    int cutvertex = -1;
    for (int b = 0; b < (int)blocks.size(); b++) {
      int candidate = -1;
      for (const EdgeTy& edge : blocks[b]) {
        for (int v : {edge.first, edge.second}) {
          if (incidentBlocks[v] > 1) {
            if (candidate == -1) {
              candidate = v;
            } else if (candidate != v) {
              candidate = -2;
              break;
            }
          }
        }
        if (candidate == -2) {
          break;
        }
      }
      if (candidate >= 0) {
        leafBlock = b;
        cutvertex = candidate;
        break;
      }
    }
    CHECK(leafBlock >= 0, "block decomposition has no leaf block");
    std::vector<bool> inBlock(n, false);
    for (const EdgeTy& edge : blocks[leafBlock]) {
      inBlock[edge.first] = true;
      inBlock[edge.second] = true;
    }

    bool inserted = false;
    Face& outer = graph.outerFace;
    const int length = outer.length();
    for (int i = 0; i < length; i++) {
      if (outer.vertices[i]->index != cutvertex) {
        continue;
      }
      const int previous = (i + length - 1) % length;
      Vertex* p = outer.vertices[previous];
      Vertex* u = outer.vertices[i];
      Vertex* q = outer.vertices[(i + 1) % length];
      if (!inBlock[p->index] || inBlock[q->index]) {
        continue;
      }

      Edge* pu = outer.edges[previous];
      Edge* uq = outer.edges[i];
      CHECK(pu->other(u) == p && uq->other(u) == q,
            "the designated outer-face corner is inconsistent");
      CHECK(p != q, "leaf-block collar has the same endpoint on both sides");
      CHECK(!p->adjacent(q),
            "leaf-block collar edge (%d,%d) already exists", p->index, q->index);

      // The outer walk before insertion contains ... p--u--q ... at this exposed
      // occurrence. In clockwise rotations, these slots cut off puq.
      Edge* pq = graph.newEdge(p, q);
      p->addEdgeAfter(pq, pu);
      q->addEdgeBefore(pq, uq);
      CHECK(graph.extractRightFace(p, pu).length() == 3,
            "collar insertion did not create the triangle puq");

      // Replace only this occurrence of p--u--q by p--q. Other
      // occurrences of a cutvertex remain on the designated outer face.
      outer.edges[previous] = pq;
      outer.vertices.erase(outer.vertices.begin() + i);
      outer.edges.erase(outer.edges.begin() + i);
      inserted = true;
      break;
    }
    CHECK(inserted, "no exposed leaf-block corner on the designated outer face");
    CHECK(graph.numberOfEdges() <= 2 * n - 3,
          "collar insertion exceeded the maximal outerplane edge count");
  }

  const std::vector<Edge*> finalEdges = graph.extractEdges();
  const std::set<Edge*> finalEdgeSet(finalEdges.begin(), finalEdges.end());
  for (int i = 0; i < originalEdgeCount; i++) {
    Edge* edge = originalEdges[i];
    CHECK(finalEdgeSet.count(edge), "an original edge did not survive augmentation");
    CHECK(make_edge(edge->source->index, edge->target->index) == originalEndpoints[i],
          "an original edge changed endpoints");
  }
  for (int v = 0; v < n; v++) {
    const auto& oldRotation = originalRotations[v];
    std::set<Edge*> oldAtVertex(oldRotation.begin(), oldRotation.end());
    std::vector<Edge*> retained;
    for (Edge* edge : graph.vertices[v]->edges) {
      if (oldAtVertex.count(edge)) {
        retained.push_back(edge);
      }
    }
    CHECK(retained.size() == oldRotation.size(),
          "original rotation at vertex %d lost an edge", v);
    const auto first = std::find(retained.begin(), retained.end(), oldRotation[0]);
    CHECK(first != retained.end());
    for (int i = 0; i < (int)oldRotation.size(); i++) {
      CHECK(retained[((first - retained.begin()) + i) % retained.size()] == oldRotation[i],
            "original cyclic rotation changed at vertex %d", v);
    }
  }

  CHECK(graph.checkConsistency(false), "augmented embedding is inconsistent");
  checkOuterplaneFaces(graph);
  CHECK(is2Connected(n, graph.extractEdgesId()), "augmented graph is not 2-connected");
  CHECK(graph.numberOfEdges() == 2 * n - 3,
        "augmented graph has %d edges, expected %d",
        graph.numberOfEdges(), 2 * n - 3);
  LOG_IF(verbose, "augmented embedded outerplane graph: n=%d m=%d -> %d",
         n, originalEdgeCount, graph.numberOfEdges());
}

// Complete a connected plane graph to a triangulation while preserving all
// input vertices and edges. Select an outer face if none is designated.
void triangulateInput(PlanarGraph& graph) {
  if (graph.outerFace.empty()) {
    CHECK(!graph.vertices.empty() &&
          !graph.vertices[0]->edges.empty(),
          "input plane graph has no designated outer face or usable dart");
    graph.outerFace = graph.extractRightFace(
        graph.vertices[0], graph.vertices[0]->edges[0]);
    CHECK(!graph.outerFace.empty() &&
          graph.outerFace == graph.extractRightFace(
              graph.outerFace.vertices[0], graph.outerFace.edges[0]),
          "could not designate an outer face from the input rotation");
  }
  CHECK(graph.checkConsistency(false));
  const bool maximalTriangulation =
      graph.outerFace.length() == 3 &&
      graph.numberOfEdges() == 3 * graph.numberOfVertices() - 6 &&
      graph.isTriangulated();
  if (!maximalTriangulation) {
    CHECK(graph.isConnected(),
          "component preprocessing requires a connected plane embedding");
    graph.triangulateByAddingEdges();
    CHECK(graph.isMaximal() && graph.outerFace.length() == 3,
          "triangulation did not produce a maximal plane graph");
  }
}
