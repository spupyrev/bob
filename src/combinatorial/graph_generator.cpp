#include "graph_generator.h"
#include "bob/adjacency.h"
#include "bob/graph_algorithms.h"
#include "bob/logging.h"

#include <algorithm>
#include <vector>
#include <queue>
#include <set>

namespace {

bool hasVertexConnectivity(const PlanarGraph& graph, int connectivity) {
  if (connectivity == 1) {
    return graph.isConnected();
  }
  if (connectivity == 2) {
    return graph.is2Connected();
  }
  CHECK(connectivity == 3);
  return graph.is3Connected();
}

void restoreRemovedEdge(PlanarGraph& graph,
                        Vertex* u,
                        Vertex* v,
                        Edge* prevU,
                        Edge* prevV) {
  Edge* edge = graph.newEdge(u, v);
  u->addEdgeAfter(edge, prevU);
  v->addEdgeAfter(edge, prevV);
}

}  // namespace

/// Generate a triangle graph, K_3
void genTriangle(PlanarGraph& g) {
  //K_3
  auto v0 = g.newVertex();
  auto v1 = g.newVertex();
  auto v2 = g.newVertex();
  auto e01 = g.newEdge(v0, v1);
  auto e02 = g.newEdge(v0, v2);
  auto e12 = g.newEdge(v1, v2);
  v0->addEdgeAfter(e01, nullptr);
  v0->addEdgeAfter(e02, e01);
  v1->addEdgeAfter(e12, nullptr);
  v1->addEdgeAfter(e01, e12);
  v2->addEdgeAfter(e02, nullptr);
  v2->addEdgeAfter(e12, e02);
  g.outerFace = g.extractRightFace(v0, e01);
}

/// Add a vertex inside a face and connect it to every boundary vertex.
Vertex* subdivideFace(PlanarGraph& g, Face& f, double prob) {
  Vertex* v = g.newVertex();
  Edge* prev = nullptr;

  for (int i = 0; i < f.length(); i++) {
    double th = Rand::nextDouble();

    if (i >= 2 && th >= prob)
      continue;

    Vertex* u = f.vertices[i];
    Edge* uv = g.newEdge(u, v);
    v->addEdgeAfter(uv, prev);
    u->addEdgeAfter(uv, f.edges[i]);
    prev = uv;
  }

  return v;
}

/// Flip a randomly chosen edge
bool flipEdge(PlanarGraph& g, Edge* e) {
  Vertex* v = e->source;
  Vertex* u = e->target;

  if (u->degree() <= 2 || v->degree() <= 2) {
    return false;
  }

  Face fl = g.extractLeftFace(v, e);
  Face fr = g.extractRightFace(v, e);
  int vIndexLeft = fl.getIndex(v);
  CHECK(v == fl[vIndexLeft]);
  int vPrevLeft = (vIndexLeft - 1 + fl.length()) % fl.length();
  int vNextLeft = (vIndexLeft + 1 + fl.length()) % fl.length();
  Vertex* a = fl[vNextLeft];
  CHECK(u == fl[vPrevLeft]);
  int vIndexRight = fr.getIndex(v);
  CHECK(v == fr[vIndexRight]);
  int vPrevRight = (vIndexRight - 1 + fr.length()) % fr.length();
  int vNextRight = (vIndexRight + 1 + fr.length()) % fr.length();
  Vertex* b = fr[vPrevRight];
  CHECK(u == fr[vNextRight]);
  CHECK(a != b);

  if (a->adjacent(b)) {
    return false;
  }

  Edge* ab = g.newEdge(a, b);
  a->addEdgeBefore(ab, fl.edges[vIndexLeft]);
  b->addEdgeAfter(ab, fr.edges[vPrevRight]);
  v->removeEdge(e);
  u->removeEdge(e);
  delete e;
  return true;
}

void adjustLevels(PlanarGraph& g, int maxIters) {
  // source vertex for bfs
  int source = 0;
  // Compute BFS depths from the selected root.
  auto depth = vector<int>(g.numberOfVertices(), -1);
  queue<int> q;
  depth[source] = 0;
  q.push(source);

  while (!q.empty()) {
    int now = q.front();
    q.pop();
    auto v = g.vertices[now];

    for (size_t i = 0; i < v->edges.size(); i++) {
      int u = v->edges[i]->other(v)->index;

      if (depth[u] == -1) {
        depth[u] = depth[now] + 1;
        q.push(u);
      }
    }
  }

  for (int i = 0; i < maxIters; i++) {
    auto e = g.randomEdge();

    if (depth[e->source->index] != depth[e->target->index]) {
      continue;
    }

    // Find the opposite vertices of the two triangular faces incident to e.
    Vertex* v = e->source;
    Vertex* u = e->target;
    CHECK(u->degree() >= 3 && v->degree() >= 3);
    Face fl = g.extractLeftFace(v, e);
    Face fr = g.extractRightFace(v, e);
    int vIndexLeft = fl.getIndex(v);
    CHECK(v == fl[vIndexLeft]);
    int vPrevLeft = (vIndexLeft - 1 + fl.length()) % fl.length();
    int vNextLeft = (vIndexLeft + 1 + fl.length()) % fl.length();
    Vertex* a = fl[vNextLeft];
    CHECK(u == fl[vPrevLeft]);
    int vIndexRight = fr.getIndex(v);
    CHECK(v == fr[vIndexRight]);
    int vPrevRight = (vIndexRight - 1 + fr.length()) % fr.length();
    int vNextRight = (vIndexRight + 1 + fr.length()) % fr.length();
    Vertex* b = fr[vPrevRight];
    CHECK(u == fr[vNextRight]);
    CHECK(a != b);

    if (a->adjacent(b)) {
      continue;
    }

    if (depth[a->index] != depth[e->source->index] && depth[b->index] != depth[e->source->index]) {
      continue;
    }

    if (depth[a->index] == depth[e->source->index] - 1 || depth[b->index] == depth[e->source->index] - 1) {
      continue;
    }

    // flip the edge
    Edge* ab = g.newEdge(a, b);
    a->addEdgeBefore(ab, fl.edges[vIndexLeft]);
    b->addEdgeAfter(ab, fr.edges[vPrevRight]);
    v->removeEdge(e);
    u->removeEdge(e);
    delete e;
  }

  g.outerFace = g.randomFace();
}

/// Generate a plane triangulation with n >= 3 vertices.
void genMaxPlanar(PlanarGraph& g, int n) {
  CHECK(n >= 3);
  // K_4
  genTriangle(g);

  if (n == 3)
    return;

  Face f = g.randomFace();
  subdivideFace(g, f, 1.0);

  for (int i = 0; i < n - 4; i++) {
    auto v = g.randomVertex();
    int len = v->edges.size();
    CHECK(len >= 3);
    int iu = Rand::next(len);
    int iw = Rand::next(len);

    while (iu == iw) {
      iw = Rand::next(len);
    }

    if (iu > iw) {
      swap(iu, iw);
    }

    auto u = v->edges[iu]->other(v);
    auto w = v->edges[iw]->other(v);
    auto x = g.newVertex();
    auto vx = g.newEdge(v, x);
    auto ux = g.newEdge(u, x);
    auto wx = g.newEdge(w, x);
    x->addEdges({wx, vx, ux});
    u->addEdgeBefore(ux, v->edges[iu]);
    w->addEdgeAfter(wx, v->edges[iw]);
    Edge* prev = ux;

    for (int i = iu + 1; i <= iw - 1; i++) {
      auto e = v->edges[i];
      e->changeEndpoint(v, x);
      x->addEdgeAfter(e, prev);
      prev = e;
    }

    v->edges.erase(v->edges.begin() + iu + 1, v->edges.begin() + iw);
    v->addEdgeAfter(vx, v->edges[iu]);
  }

  int MAX_FLIPS = std::min(10000, 10 * g.numberOfVertices());
  for (int i = 0; i < MAX_FLIPS; i++) {
    flipEdge(g, g.randomEdge());
  }

  g.outerFace = g.randomFace();

  int MAX_ADJUSTMENTS = std::min(10000, 10 * g.numberOfVertices());
  adjustLevels(g, MAX_ADJUSTMENTS);

  CHECK(g.isMaximal());
  CHECK(g.checkConsistency(), "generated graph not consistent");
}

Vertex* addOuterBFSRoot(PlanarGraph& g) {
  CHECK(g.outerFace.length() == 3 && g.outerFace.edges.size() == 3,
        "BFS root requires a triangular outer face");
  // extractFaces coalesces K_3's two sides, so its full face check rejects K_3.
  CHECK(g.checkConsistency(g.numberOfVertices() > 3));
  CHECK(g.isTriangulated() && g.isMaximal(),
        "BFS root requires a maximal plane triangulation");

  const int originalVertexCount = g.numberOfVertices();
  const int originalEdgeCount = g.numberOfEdges();
  const auto originalVertices = g.vertices;
  const auto originalEdges = g.extractEdges();
  std::vector<std::pair<Vertex*, Vertex*>> originalEndpoints;
  for (Edge* edge : originalEdges) {
    originalEndpoints.emplace_back(edge->source, edge->target);
  }
  const Face oldOuter = g.outerFace;
  CHECK(g.extractRightFace(oldOuter[0], oldOuter.edges[0]) == oldOuter,
        "designated outer face must follow the embedding");

  // These are the faces on the original graph's side of its outer cycle.
  std::vector<Face> originalInnerFaces;
  for (int i = 0; i < 3; ++i) {
    Vertex* next = oldOuter[(i + 1) % 3];
    CHECK(oldOuter.edges[i]->other(oldOuter[i]) == next);
    originalInnerFaces.push_back(g.extractRightFace(next, oldOuter.edges[i]));
  }

  Face faceToSubdivide = oldOuter;
  Vertex* root = subdivideFace(g, faceToSubdivide, 1.0);
  CHECK(root == g.vertices[originalVertexCount] && root->index == originalVertexCount);
  CHECK(root->degree() == 3);
  CHECK(g.numberOfVertices() == originalVertexCount + 1);
  CHECK(g.numberOfEdges() == originalEdgeCount + 3);

  for (int i = 0; i < originalVertexCount; ++i) {
    CHECK(g.vertices[i] == originalVertices[i] && g.vertices[i]->index == i,
          "original vertex changed during BFS root insertion");
  }
  const auto currentEdges = g.extractEdges();
  const std::set<Edge*> currentEdgeSet(currentEdges.begin(), currentEdges.end());
  for (size_t i = 0; i < originalEdges.size(); ++i) {
    Edge* edge = originalEdges[i];
    CHECK(currentEdgeSet.count(edge) == 1,
          "original edge identity changed during BFS root insertion");
    CHECK(edge->source == originalEndpoints[i].first &&
          edge->target == originalEndpoints[i].second,
          "original edge endpoint changed during BFS root insertion");
  }

  for (int i = 0; i < 3; ++i) {
    Vertex* corner = oldOuter[i];
    Vertex* next = oldOuter[(i + 1) % 3];
    CHECK(root->adjacent(corner));
    const Face rootSide = g.extractRightFace(corner, oldOuter.edges[i]);
    CHECK(rootSide.length() == 3 && rootSide.contains(root) &&
          rootSide.contains(corner) && rootSide.contains(next),
          "root is not on the former outer side of the triangle");
    CHECK(g.extractRightFace(next, oldOuter.edges[i]) == originalInnerFaces[i],
          "an original inner face of the outer triangle changed");
  }

  g.outerFace = g.extractRightFace(oldOuter[0], oldOuter.edges[0]);
  CHECK(g.outerFace.length() == 3 && g.outerFace.contains(root));
  CHECK(g.isMaximal());
  CHECK(g.checkConsistency());
  return root;
}

/// Generate a random planar 3-tree by repeatedly stellating an inner face.
void genRandomPlanar3Tree(PlanarGraph& g, int n) {
  CHECK(n >= 3);

  genTriangle(g);
  g.outerFace = g.extractFace({0, 1, 2});
  for (int i = 0; i < n - 3; i++) {
    Face f = g.randomFace();
    while (f == g.outerFace) {
      f = g.randomFace();
    }
    subdivideFace(g, f, 1.0);
  }

  CHECK(g.checkConsistency(), "generated graph not consistent");
}

/// Connected partial planar 3-tree with n vertices in which each non-tree
/// non-outer-triangle edge is kept with probability p.
void genPartialPlanar3Tree(PlanarGraph& g, int n, double p, int connectivity) {
  CHECK(n >= 3);
  CHECK(0.0 <= p && p <= 1.0);
  CHECK(1 <= connectivity && connectivity <= 3);
  CHECK(g.vertices.empty(), "output graph is not empty");

  genRandomPlanar3Tree(g, n);

  set<EdgeTy> keptEdges;
  set<EdgeTy> protectedEdges;
  protectedEdges.insert(make_edge(0, 1));
  protectedEdges.insert(make_edge(0, 2));
  protectedEdges.insert(make_edge(1, 2));

  if (connectivity == 1) {
    vector<bool> used(n, false);
    queue<Vertex*> q;
    used[0] = true;
    q.push(g.vertices[0]);

    while (!q.empty()) {
      Vertex* v = q.front();
      q.pop();

      for (Edge* edge : v->edges) {
        Vertex* u = edge->other(v);
        if (used[u->index]) {
          continue;
        }
        used[u->index] = true;
        keptEdges.insert(make_edge(v->index, u->index));
        q.push(u);
      }
    }

    CHECK((int)keptEdges.size() == n - 1);

    // Keep the source triangle so the inherited outer face remains valid.
    keptEdges.insert(protectedEdges.begin(), protectedEdges.end());
  } else {
    vector<EdgeTy> candidates;
    for (Edge* edge : g.extractEdges()) {
      const EdgeTy id = make_edge(edge->source->index, edge->target->index);
      if (!protectedEdges.count(id)) {
        candidates.push_back(id);
      }
    }

    int currentEdges = g.numberOfEdges();
    const int minEdges =
        connectivity == 2 ? n : (3 * n + 1) / 2;
    Rand::shuffle(candidates.begin(), candidates.end());
    for (EdgeTy id : candidates) {
      if (Rand::check(p)) {
        continue;
      }
      if (currentEdges <= minEdges) {
        continue;
      }

      Vertex* u = g.vertices[id.first];
      Vertex* v = g.vertices[id.second];
      Edge* edge = g.extractEdge(u, v);
      if (edge == nullptr) {
        continue;
      }
      if (u->degree() <= connectivity || v->degree() <= connectivity) {
        continue;
      }

      Edge* prevU = u->findEdgeBefore(edge);
      Edge* prevV = v->findEdgeBefore(edge);
      g.removeEdge(edge);
      currentEdges--;

      if (!hasVertexConnectivity(g, connectivity)) {
        restoreRemovedEdge(g, u, v, prevU, prevV);
        currentEdges++;
      }
    }
  }

  if (connectivity == 1) {
    auto edges = g.extractEdges();
    for (Edge* edge : edges) {
      const EdgeTy id = make_edge(edge->source->index, edge->target->index);
      if (!keptEdges.count(id) && !Rand::check(p)) {
        g.removeEdge(edge);
      }
    }
  }

  Rand::shuffle(g.vertices.begin() + 3, g.vertices.end());
  for (int i = 0; i < g.numberOfVertices(); i++) {
    g.vertices[i]->index = i;
    g.vertices[i]->label = to_string(i);
  }

  CHECK(g.isConnected(), "generated graph is not connected");
  if (connectivity >= 2) {
    CHECK(is2Connected(g.numberOfVertices(), g.extractEdgesId()),
          "generated graph is not 2-connected");
  }
  if (connectivity >= 3) {
    CHECK(is3Connected(g.numberOfVertices(), g.extractEdgesId()),
          "generated graph is not 3-connected");
  }
  CHECK(g.checkConsistency(false), "generated graph is not consistent");
  CHECK(n - 1 <= g.numberOfEdges() && g.numberOfEdges() <= 3 * n - 6);
}

/// Generate a complete-by-level planar 3-tree.
void genCompletePlanar3Tree(PlanarGraph& g, int n, int verbose) {
  CHECK(n >= 3);

  genTriangle(g);
  g.outerFace = g.extractFace({0, 1, 2});
  std::vector<Face> faces = g.extractFaces(false);

  int level = 1;
  while (g.numberOfVertices() < n) {
    LOG_IF(verbose, "level %d:  n = %d; active faces = %d", level, g.numberOfVertices(), faces.size());
    // Adding the next level
    std::vector<Face> newFaces;
    int remainingVertices = faces.size();
    for (size_t i = 0; i < faces.size(); i++) {
      Vertex* v = subdivideFace(g, faces[i], 1);
      auto vFaces = g.extractFaces(v);
      CHECK(vFaces.size() == 3);
      newFaces.insert(newFaces.end(), vFaces.begin(), vFaces.end());

      remainingVertices--;
      if (g.numberOfVertices() >= n && remainingVertices > 0) {
        LOG_IF(verbose, "  terminated generation at depth %d; remaining vertices: %d", level + 1, remainingVertices);
        break;
      }
    }
    faces = newFaces;
    level++;
  }

  CHECK(g.checkConsistency(), "generated graph not consistent");
}

void genMaximalOuterplanar(PlanarGraph& g2, int n) {
  CHECK(n >= 3);
  PlanarGraph g;
  genTriangle(g);
  Face outerFace = g.outerFace;

  for (int k = 3; k < n; k++) {
    CHECK(outerFace.length() == k);
    int i = Rand::next(outerFace.length());
    int i1 = (i + 1) % outerFace.length();
    auto v = g.newVertex();
    auto u = outerFace.vertices[i];
    auto w = outerFace.vertices[i1];
    auto vu = g.newEdge(v, u);
    auto vw = g.newEdge(v, w);
    v->addEdge(vu);
    v->addEdge(vw);
    u->addEdgeBefore(vu, outerFace.edges[i]);
    w->addEdgeAfter(vw, outerFace.edges[i]);
    outerFace = g.extractLeftFace(u, vu);
    outerFace.reverse();
  }

  outerFace.reverse();
  g.outerFace = outerFace;
  CHECK(g.checkConsistency(), "generated graph is not consistent");
  CHECK(g.outerFace.length() == n, "generated graph is not outerplanar");
  CHECK(2 * g.numberOfVertices() - 3 == g.numberOfEdges(), "generated graph is not outerplanar");

  // re-index to make sure outerface is numbered consecutively
  map<Vertex*, int> v2i;
  map<int, Vertex*> i2v;
  for (int i = 0; i < n; i++) {
    v2i[g.outerFace.vertices[i]] = i;
    i2v[i] = g.outerFace.vertices[i];
  }
  for (int i = 0; i < n; i++) {
    g2.newVertex();
  }

  map<Edge*, Edge*> e2e; // source edge -> copied edge

  for (auto edge : g.extractEdges()) {
    auto nv = g2.vertices[v2i[edge->source]];
    auto nu = g2.vertices[v2i[edge->target]];
    auto ne = g.newEdge(nv, nu);
    e2e[edge] = ne;
  }

  for (int i = 0; i < n; i++) {
    auto v = g.vertices[i];
    auto nv = g2.vertices[v2i[v]];
    Edge* prevEdge = nullptr;

    for (auto edge : v->edges) {
      auto ne = e2e[edge];
      nv->addEdgeAfter(ne, prevEdge);
      prevEdge = ne;
    }
  }

  g2.outerFace = g2.extractLongestFace();

  if (g2.outerFace[0]->index > g2.outerFace[1]->index || g2.outerFace[1]->index > g2.outerFace[2]->index) {
    g2.outerFace.reverse();
  }

  CHECK(g2.checkConsistency(), "generated graph is not consistent");
}

/// Generate a connected outerplanar graph on n vertices by retaining a
/// spanning tree and keeping each remaining edge independently with probability p.
void genOuterplanar(PlanarGraph& g2, int n, double p) {
  CHECK(n >= 4);
  CHECK(0.0 <= p && p <= 1.0);
  CHECK(g2.vertices.empty(), "output graph is not empty");

  genTriangle(g2);
  Face outerFace = g2.outerFace;

  for (int k = 3; k < n; k++) {
    CHECK(outerFace.length() == k);
    const int i = Rand::next(outerFace.length());
    const int i1 = (i + 1) % outerFace.length();
    auto v = g2.newVertex();
    auto u = outerFace.vertices[i];
    auto w = outerFace.vertices[i1];
    auto vu = g2.newEdge(v, u);
    auto vw = g2.newEdge(v, w);
    v->addEdge(vu);
    v->addEdge(vw);
    u->addEdgeBefore(vu, outerFace.edges[i]);
    w->addEdgeAfter(vw, outerFace.edges[i]);
    outerFace = g2.extractLeftFace(u, vu);
    outerFace.reverse();
  }

  outerFace.reverse();
  g2.outerFace = outerFace;
  CHECK(g2.checkConsistency(), "generated graph is not consistent");
  CHECK(g2.outerFace.length() == n, "generated graph is not outerplanar");
  CHECK(2 * g2.numberOfVertices() - 3 == g2.numberOfEdges(), "generated graph is not outerplanar");

  set<EdgeTy> treeEdges;
  vector<bool> used(n, false);
  queue<Vertex*> queue;
  used[0] = true;
  queue.push(g2.vertices[0]);

  while (!queue.empty()) {
    auto v = queue.front();
    queue.pop();

    for (auto edge : v->edges) {
      auto u = edge->other(v);
      if (used[u->index]) {
        continue;
      }
      used[u->index] = true;
      treeEdges.insert(make_edge(v->index, u->index));
      queue.push(u);
    }
  }
  CHECK((int)treeEdges.size() == n - 1);

  auto edges = g2.extractEdges();
  for (auto edge : edges) {
    const EdgeTy id = make_edge(edge->source->index, edge->target->index);
    if (!treeEdges.count(id) && !Rand::check(p)) {
      g2.removeEdge(edge);
    }
  }

  CHECK(g2.isConnected(), "generated graph is not connected");
  CHECK(n - 1 <= g2.numberOfEdges() && g2.numberOfEdges() <= 2 * n - 3);
}

void genPlanar4Connected(PlanarGraph& g, int n) {
  CHECK(n >= 10, "4connected generator requires a target of at least 10 vertices");
  genQuadrang(g, (n + 2) / 2, true, true);
  g.triangulateByStellation(false);
  CHECK(g.is4Connected(), "generated graph is not 4-connected");
}

void genDoubleWheel(PlanarGraph& g, int k) {
  CHECK(k % 2 == 0);

  for (int i = 0; i < k + 2; i++) {
    g.newVertex();
  }

  vector<Edge*> outEdges = vector<Edge*>(k + 2, nullptr);
  // internal vertex
  Edge* prev = nullptr;

  for (int i = 2; i < k + 2; i += 2) {
    Edge* e = g.newEdge(g.vertices[0], g.vertices[i]);
    g.vertices[0]->addEdgeAfter(e, prev);
    g.vertices[i]->addEdge(e);
    prev = e;
    outEdges[i] = e;
  }

  // external
  prev = nullptr;

  for (int i = 3; i < k + 2; i += 2) {
    Edge* e = g.newEdge(g.vertices[1], g.vertices[i]);
    g.vertices[1]->addEdgeBefore(e, prev);
    g.vertices[i]->addEdge(e);
    prev = e;
    outEdges[i] = e;
  }

  // wheel
  for (int i = 2; i < k + 2; i += 2) {
    int next = (i + 1 < k + 2 ? i + 1 : 2);
    Edge* e = g.newEdge(g.vertices[i], g.vertices[next]);
    g.vertices[i]->addEdge(e);
    g.vertices[next]->addEdge(e);
  }

  for (int i = 3; i < k + 2; i += 2) {
    int next = (i + 1 < k + 2 ? i + 1 : 2);
    Edge* e = g.newEdge(g.vertices[i], g.vertices[next]);
    g.vertices[i]->addEdgeAfter(e, outEdges[i]);
    g.vertices[next]->addEdgeAfter(e, outEdges[next]);
  }

  Edge* outerEdge = g.vertices[1]->adjacentEdge(g.vertices[k + 1]);
  g.outerFace = g.extractRightFace(g.vertices[1], outerEdge);
}

bool vertexSplitting(PlanarGraph& g) {
  // pick a vertex of degree >= 4
  auto candidates = vector<Vertex*>();
  for (auto v : g.vertices) {
    if (v->degree() >= 4) {
      candidates.push_back(v);
    }
  }
  if (candidates.empty()) {
    return false;
  }
  auto v = candidates[Rand::next(candidates.size())];
  CHECK(v->degree() >= 4);

  Edge* e0 = v->edges[Rand::next(v->edges.size())];
  Edge* e1 = v->findEdgeAfter(e0);
  Edge* e2 = v->findEdgeBefore(e0);
  Vertex* v1 = e1->other(v);
  Vertex* v2 = e2->other(v);

  auto adjacentViaFaces = [&](Vertex* v1, Vertex* v2) {
    auto faces = g.extractFaces(v1);
    for (auto& f : faces) {
      if (f.contains(v1) && f.contains(v2)) {
        return true;
      }
    }
    return false;
  };

  int attempt = 0;
  int maxAttempts = 10;
  while (++attempt < maxAttempts) {
    if (!adjacentViaFaces(v1, v2)) break;

    e0 = v->edges[Rand::next(v->edges.size())];
    e1 = v->findEdgeAfter(e0);
    e2 = v->findEdgeBefore(e0);
    v1 = e1->other(v);
    v2 = e2->other(v);
  }

  if (attempt >= maxAttempts) {
    return false;
  }

  Vertex* u = g.newVertex();
  v->removeEdge(e0);

  if (e0->source == v) {
    e0->source = u;
  } else {
    e0->target = u;
  }

  Edge* e3 = g.newEdge(u, v1);
  Edge* e4 = g.newEdge(u, v2);
  u->addEdges({e3, e4, e0});
  v1->addEdgeAfter(e3, e1);
  v2->addEdgeBefore(e4, e2);
  //restore outerface
  int vIndex = g.outerFace.getIndex(v);

  if (vIndex != -1) {
    CHECK(g.outerFace.length() == 4);
    // opposite
    int oIndex = (vIndex + 2) % 4;
    Vertex* vo = g.outerFace[oIndex];
    Edge* eo = vo->adjacentEdge(g.outerFace.vertices[(oIndex + 1) % 4]);
    g.outerFace = g.extractRightFace(vo, eo);
  }
  return true;
}

Face cycleAddition(PlanarGraph& g, Face face) {
  Vertex* v0 = face.vertices[0];
  Vertex* v1 = face.vertices[1];
  Vertex* v2 = face.vertices[2];
  Vertex* v3 = face.vertices[3];
  Vertex* u0 = g.newVertex();
  Vertex* u1 = g.newVertex();
  Vertex* u2 = g.newVertex();
  Vertex* u3 = g.newVertex();
  Edge* e0 = g.newEdge(v0, u0);
  v0->addEdgeAfter(e0, face.edges[0]);
  Edge* e1 = g.newEdge(v1, u1);
  v1->addEdgeAfter(e1, face.edges[1]);
  Edge* e2 = g.newEdge(v2, u2);
  v2->addEdgeAfter(e2, face.edges[2]);
  Edge* e3 = g.newEdge(v3, u3);
  v3->addEdgeAfter(e3, face.edges[3]);
  Edge* e4 = g.newEdge(u0, u1);
  Edge* e5 = g.newEdge(u1, u2);
  Edge* e6 = g.newEdge(u2, u3);
  Edge* e7 = g.newEdge(u3, u0);
  u0->addEdges({e0, e4, e7});
  u1->addEdges({e1, e5, e4});
  u2->addEdges({e2, e6, e5});
  u3->addEdges({e6, e3, e7});
  return g.extractFace({u0, u1, u2, u3});
}

void cycleAddition(PlanarGraph& g) {
  Face face = g.randomFace();
  cycleAddition(g, face);
}

void genQuadrang(PlanarGraph& g, int n, bool useVertexSplitting, bool useCycleAddition) {
  CHECK(n >= 6);
  if (!useVertexSplitting && !useCycleAddition) {
    genDoubleWheel(g, n - 2);
  } else {
    const int k = 4;
    genDoubleWheel(g, k);

    CHECK(useVertexSplitting || useCycleAddition);
    while (g.numberOfVertices() < n) {
      if (useCycleAddition && Rand::check(0.2)) {
        cycleAddition(g);
      } else if (useVertexSplitting) {
        bool res = vertexSplitting(g);
        if (!res) {
          cycleAddition(g);
        }
      }
    }
  }
  g.outerFace = g.extractLongestFace();
  CHECK(g.checkConsistency(), "generated quadrangulation is not consistent");
}

/// Generate planar cubic 3-connected graphs (duals of triangulations)
void genPlanarCubic(PlanarGraph& g, int n) {
  CHECK(n >= 4);
  PlanarGraph dual;
  genMaxPlanar(dual, n / 2 + 2);
  dual.constructDual(g);
  CHECK(g.checkConsistency(), "generated graph is not consistent");
  CHECK(g.maxDegree() <= 3);
}
