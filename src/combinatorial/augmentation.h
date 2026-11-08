#pragma once

#include "bob/graph_algorithms.h"

#include <vector>

class PlanarGraph;

/// Augment a connected outerplanar graph to a maximal outerplanar graph.
void augmentOuterplanar(
    const int n,
    const std::vector<EdgeTy>& edges,
    std::vector<EdgeTy>& resEdges, int verbose = 0);

/// Complete a connected simple outerplane embedding with triangular bounded
/// faces, preserving its rotations and designated outer face. Requires n >= 3.
/// Inserts only edges in exposed outer-face corners; adds no vertices.
void augmentOuterplanar(PlanarGraph& graph, int verbose = 0);

// Triangulate a connected simple plane graph with at least three vertices,
// adding edges only. Choose an outer face if none is designated.
void triangulateInput(PlanarGraph& graph);
