#pragma once

#include "planar_graph.h"

// planar graphs
void genTriangle(PlanarGraph& g);
void genMaxPlanar(PlanarGraph& g, int n);
// Add a degree-three BFS root in the triangular outer face of a triangulation.
// The original outer triangle becomes a separating cycle; returns the new root.
Vertex* addOuterBFSRoot(PlanarGraph& g);
void genRandomPlanar3Tree(PlanarGraph& g, int n);
void genPartialPlanar3Tree(PlanarGraph& g, int n, double p, int connectivity = 1);
void genCompletePlanar3Tree(PlanarGraph& g, int n, int verbose = 0);
void genMaximalOuterplanar(PlanarGraph& g, int n);
void genOuterplanar(PlanarGraph& g, int n, double p);
void genQuadrang(PlanarGraph& g, int n, bool useVertexSplitting, bool useCycleAddition);
void genPlanarCubic(PlanarGraph& g, int n);
// Approximate target size n >= 10: quadrangulation steps may add four vertices.
void genPlanar4Connected(PlanarGraph& g, int n);
