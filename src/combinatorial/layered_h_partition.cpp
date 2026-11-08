// Construct planar queue layouts by decomposing a plane triangulation into
// tripods. Reordering the vertical paths gives a bound of 33 queues; keeping
// their decomposition order gives a bound of 48 queues.
//
// Pipeline (buildPPSLayout):
//   1. tripod decomposition of a plane triangulation (LayeredHPartition);
//   2. the embedded quotient, with loops and parallel edges
//      (extractRawTripodQuotient, buildRawQuotientFaces);
//   3. levels and level components of the quotient (TreePartition), and for
//      each component the graph K with its auxiliary triangles (buildLevelK,
//      wrapOuterFaces);
//   4. face order, quotient order, and five quotient
//      queues (buildQuotientOrder);
//   5. tripod reordering: the order of the vertical paths of each tripod
//      (buildPathOrderAndCheckPhases);
//   6. the layout of G: BFS layers, then the quotient order, then the port
//      order, with the queues of the product construction (QueueAssignment).
// Construction invariants and final queue assignments use always-on CHECKs.
//
// Terminology:
//   pod                    tripod (a vertex of the quotient); 0, 1, 2 are the
//                          three initial single-vertex tripods
//   path of a pod          vertical path of a tripod; a port of the quotient
//   raw quotient           the embedded quotient multigraph with all loops and
//                          parallel edges
//   incidence              an edge end in the rotation at a tripod
//   depth                  the level of a tripod in the quotient
//   bag (TreePartition)    a level component; bag2parents are its neighbors
//                          in the preceding level
//   bag (LayeredHPartition) one recursive call of the tripod construction
//   support                a level edge of a level component; its parallel
//                          copies form one class in the rotation
//   binding                an edge between consecutive levels
//   child component        a level component of the next level
//   layer                  a BFS layer of G (not a level of the quotient)

#include "bob/logging.h"
#include "bob/common.h"
#include "bob/cmd_options.h"
#include "bob/adjacency.h"
#include "augmentation.h"
#include "planar_graph.h"
#include "graph_generator.h"
#include "queue_orders.h"

#include <algorithm>
#include <array>
#include <functional>
#include <memory>
#include <numeric>
#include <queue>
#include <set>
#include <sstream>
#include <tuple>
#include <unordered_set>
#include <unordered_map>

using namespace std;

/// Build a layering for a given planar graph
void getLayering(PlanarGraph& graph, int root, vector<int>& layer, vector<int>& parent, vector<int>& ocIdx, int verbose) {
  int n = graph.numberOfVertices();
  layer = vector<int>(n, -1);

  if (parent.empty()) {
    parent = vector<int>(n, -1);
  }

  ocIdx = vector<int>(n, -1);
  int curIdx = 0;
  queue<int> q;
  q.push(root);
  layer[root] = 0;
  ocIdx[root] = curIdx++;

  while (!q.empty()) {
    auto vId = q.front();
    q.pop();
    auto v = graph.vertices[vId];
    Edge* curEdge = parent[vId] == -1 ? v->edges[0] : v->adjacentEdge(graph.vertices[parent[vId]]);

    for (int i = 0; i < (int)v->edges.size(); i++) {
      Vertex* u = curEdge->other(v);
      int uId = u->index;

      if (layer[uId] == -1 && (parent[uId] == vId || parent[uId] == -1)) {
        layer[uId] = layer[vId] + 1;
        parent[uId] = vId;
        ocIdx[uId] = curIdx++;
        q.push(uId);
      }

      curEdge = v->findEdgeBefore(curEdge);
    }
  }

  for (int i = 0; i < n; i++) {
    CHECK(layer[i] != -1);
    CHECK(ocIdx[i] != -1);
    CHECK(i == root || parent[i] != -1);
  }

  // consecutive vertices of layer-1 are adjacent
  if (graph.isMaximal()) {
    for (int i = 0; i < n; i++) {
      for (int j = i + 1; j < n; j++) {
        if (parent[i] == parent[j] && abs(ocIdx[i] - ocIdx[j]) == 1 && layer[i] == 1) {
          CHECK(graph.vertices[i]->adjacent(graph.vertices[j]));
        }
      }
    }
  }

  if (verbose >= 2) {
    vector<int> vertices;

    for (int i = 0; i < n; i++) {
      vertices.push_back(i);
    }

    sort(vertices.begin(), vertices.end(), [&](int l, int r) { return ocIdx[l] < ocIdx[r]; });

    for (int v : vertices) {
      cerr << " vertex " << v << ": layer = " << layer[v] << ", parent = " << parent[v] << ", ocIdx = " << ocIdx[v] << "\n";
    }
  }
}

struct LayeredHPartition {
  struct Pod {
    vector<int> paths[3];

    Pod(const vector<int>& p) {
      CHECK(p.size() > 0);
      paths[0] = p;
    }

    Pod(const vector<vector<int>>& ps) {
      CHECK(1 <= ps.size() && ps.size() <= 3);
      int idx = 0;

      for (auto& p : ps) {
        if (p.size() > 0) {
          paths[idx] = p;
          idx++;
        }
      }

      CHECK(idx > 0);
    }

    int size() const {
      return int(paths[0].size() + paths[1].size() + paths[2].size());
    }

    int lowestVertex(int pathId) const {
      CHECK(0 <= pathId && pathId < 3);
      CHECK(!paths[pathId].empty());
      return paths[pathId].back();
    }

    int highestVertex(int pathId) const {
      CHECK(0 <= pathId && pathId < 3);
      CHECK(!paths[pathId].empty());
      return paths[pathId].front();
    }

    int numPaths() const {
      int res = 0;

      if (paths[0].size() > 0) {
        res++;
      }
      if (paths[1].size() > 0) {
        res++;
      }
      if (paths[2].size() > 0) {
        res++;
      }

      return res;
    }

    bool isBipod() const {
      return numPaths() == 2;
    }

    bool isUnipod() const {
      return numPaths() == 1;
    }

    void print() const {
      int cp = numPaths();
      CHECK(cp >= 1);

      if (cp == 1) {
        cerr << " unipod:";
      } else if (cp == 2) {
        cerr << "  bipod:";
      } else if (cp == 3) {
        cerr << " tripod:";
      } else {
        cerr << " quadpod:";
      }

      for (int i = 0; i < 3; i++) {
        if (paths[i].size() > 0) {
          cerr << " (" << to_string(paths[i]) << ")";
        }
      }
    }

    vector<int> concat() const {
      vector<int> vec;
      vec.insert(vec.end(), paths[0].begin(), paths[0].end());
      vec.insert(vec.end(), paths[1].begin(), paths[1].end());
      vec.insert(vec.end(), paths[2].begin(), paths[2].end());
      return vec;
    }
  };

  int verbose;
  bool debug = false;

  // Original graph data
  int n;
  Adjacency adj;
  std::vector<EdgeTy> edges;
  std::vector<vector<int>> faces;
  std::unordered_map<string, int> hash2faceIdx;
  vector<vector<int>> facesAdj;

  // BFS vertex root
  int root;
  // BFS layers of every vertex
  std::vector<int> layer;
  // BFS tree (parent of each vertex)
  std::vector<int> parent;
  // Vertex discovery order in the embedding-dependent BFS
  std::vector<int> ocIdx; 

  // The tripods, with one, two, or three vertical paths
  std::vector<Pod> pods;
  // Color order of the Sperner face that created each pod; initial pods have -1s.
  std::vector<std::array<int, 3>> podSelectedFace;
  // Distinct earlier tripods on the boundary of the call creating each pod.
  std::vector<vector<int>> podBoundaryParents;
  // Recursive call that created each pod; initial pods have no such call.
  std::vector<int> podCreatingBag;
  // original vertex => the pod containing it
  std::vector<int> vertex2pod;
  // original vertex => the path index (0,1,2) containing it
  std::vector<int> vertex2path;

  // Each recursive call: the tripods on its boundary and the one it creates
  std::vector<vector<int>> bags;
  // The parent call of each call
  std::vector<int> bag2parent;
  // Which immediate recursive region led from its parent call to this bag.
  std::vector<int> bagRegionFromParent;
  // The root of the decomposition
  int rootBag;

  LayeredHPartition(int n_, int _verbose):
      verbose(_verbose), debug(false), adj(n_) {}

  void init(PlanarGraph& graph, int root_) {
    CHECK(graph.numberOfVertices() > 3);
    CHECK(graph.outerFace.length() == 3);

    root = root_;
    getLayering(graph, root, layer, parent, ocIdx, verbose);
    n = graph.numberOfVertices();
    if ((int)adj.size() != n) {
      adj.init(n);
    }
    edges.reserve(graph.numberOfEdges());

    for (auto v : graph.vertices) {
      adj.reserve(v->index, v->edges.size());
      for (auto& e : v->edges) {
        auto u = e->other(v);
        adj.set(v->index, u->index);

        if (v->index < u->index) {
          edges.push_back(make_pair(v->index, u->index));
        }
      }
    }
    adj.shrink_to_fit();

    // Index faces and their neighbors across each boundary edge.
    auto rFaces = graph.extractFaces();

    for (int i = 0; i < (int)rFaces.size(); i++) {
      auto& f = rFaces[i];
      CHECK(f.length() == 3);
      hash2faceIdx[f.hash()] = i;
    }

    for (int i = 0; i < (int)rFaces.size(); i++) {
      auto& f = rFaces[i];
      faces.push_back({f.vertices[0]->index, f.vertices[1]->index, f.vertices[2]->index});
      facesAdj.push_back({-1, -1, -1});

      for (int j = 0; j < f.length(); j++) {
        auto adjFace = graph.extractLeftFace(f.vertices[j], f.edges[j]);
        facesAdj[i][j] = hash2faceIdx[adjFace.hash()];
      }
    }
  }

  struct DeferredRec {
    int depth;
    vector<int> fence;
    int parentBag;
    int region;
    unordered_set<int> activeFaces;
    vector<int> activeVertices;
  };

  void build(PlanarGraph& graph) {
    const int maxLayer = *std::max_element(layer.begin(), layer.end());
    LOG_IF(verbose, "building a layered %d-partition for a planar graph with %d layers and root = %d", 3, maxLayer + 1, root);
    vertex2pod = std::vector<int>(n, -1);
    // The initial fence (v1, v2, v3) is the root with its last and first
    // neighbors in the BFS order, which visits the neighbors of the root
    // counterclockwise; these neighbors are consecutive around the root, so
    // the fence bounds a face, which becomes the outer face.
    int v1 = root;
    int v2 = -1;
    int v3 = -1;

    for (int v = 0; v < n; v++) {
      if (layer[v] != 1)
        continue;

      if (v2 == -1 || ocIdx[v2] < ocIdx[v]) {
        v2 = v;
      }

      if (v3 == -1 || ocIdx[v3] > ocIdx[v]) {
        v3 = v;
      }
    }
    // set outerface
    graph.outerFace = graph.extractFace({v1, v2, v3});

    auto path1 = {v1};
    auto path2 = {v2};
    auto path3 = {v3};
    auto pod1 = Pod(path1);
    auto pod2 = Pod(path2);
    auto pod3 = Pod(path3);
    addPod(pod1);
    addPod(pod2);
    addPod(pod3);
    auto Fence = {v1, v2, v3};
    // The recursion chain can be linear in |G|, so the recursive calls are
    // scheduled on an explicit work list (in the same order).
    vector<DeferredRec> pending;
    rootBag = buildRec(graph, 0, Fence, &pending, -1, -1);
    while (!pending.empty()) {
      DeferredRec task = std::move(pending.back());
      pending.pop_back();
      const int childBag = buildRec(
          graph, task.depth, task.fence, &pending, task.parentBag, task.region,
          &task.activeFaces, &task.activeVertices);
      CHECK(childBag >= 0 && bag2parent[childBag] == task.parentBag &&
            bagRegionFromParent[childBag] == task.region,
            "deferred PPS recursion lost a child region");
    }
    for (int v = 0; v < n; v++) {
      CHECK(vertex2pod[v] >= 0,
            "PPS recursion left vertex %d outside every tripod", v);
    }
    CHECK(rootBag != -1);

    if (verbose >= 2) {
      cerr << "numBags: " << bags.size()
           << ", numPods: " << pods.size() 
           << ", rootBag: " << rootBag 
           << "\n";
    }

    // Direct every path away from the BFS root.
    for (auto& pod : pods) {
      for (int i = 0; i < 3; i++) {
        if (pod.paths[i].empty())
          continue;

        if (layer[pod.paths[i][0]] > layer[pod.paths[i].back()]) {
          pod.paths[i] = reverse(pod.paths[i]);
        }
      }
    }

    vertex2path = std::vector<int>(n, -1);
    for (auto& pod : pods) {
      for (int pathId = 0; pathId < 3; pathId++) {
        for (int v : pod.paths[pathId]) {
          CHECK(vertex2path[v] == -1);
          vertex2path[v] = pathId;
        }
      }
    }
  }

  /// Decompose one recursive region and return its bag index.
  int buildRec(
      PlanarGraph& graph,
      const int depth,
      const std::vector<int>& Fence,
      vector<DeferredRec>* pending,
      int deferredParentBag = -1,
      int deferredRegion = -1,
      unordered_set<int>* preparedFaces = nullptr,
      vector<int>* preparedVertices = nullptr) {
    debug = (verbose >= 2 && depth <= 3) || verbose >= 3;
    if (debug) {
      cerr << "buildRec [depth=" << depth << "] with fence [" << to_string(Fence) << "]\n";
    }

    // Check that Fence is a clockwise simple cycle in G.
    CHECK(Fence.size() >= 3);
    CHECK(pending != nullptr);
    {
      const set<int> distinctFence(Fence.begin(), Fence.end());
      CHECK(distinctFence.size() == Fence.size(),
            "recursive PPS fence repeats a boundary vertex");
    }
    for (size_t i = 0; i < Fence.size(); i++) {
      CHECK(adj.test(Fence[i], Fence[(i + 1) % Fence.size()]));
    }

    // get active vertices and faces
    std::unordered_set<int> activeFaces;
    vector<int> activeVertices;
    if (preparedFaces != nullptr) {
      CHECK(preparedVertices != nullptr &&
            !preparedFaces->empty() &&
            preparedVertices->size() >= Fence.size(),
            "deferred PPS region has no prepared active faces");
      activeFaces = std::move(*preparedFaces);
      activeVertices = std::move(*preparedVertices);
    } else {
      CHECK(preparedVertices == nullptr);
      activeVertices = getActive(graph, Fence, activeFaces);
    }
    if (debug) {
      std::sort(activeVertices.begin(), activeVertices.end());
      cerr << "  activeVertices : " << to_string(activeVertices) << "\n";
    }

    CHECK(activeVertices.size() >= Fence.size());
    if (activeVertices.size() <= Fence.size())
      return -1;

    // extract pods from the fence
    std::vector<Pod> P;
    std::vector<int> PodIDs;
    splitFence(Fence, P, PodIDs);
    checkBoundaryTripods(P, PodIDs);
    std::vector<int> R[3];
    colorBoundary(P, R);

    if (debug) {
      cerr << "  R[0] = " << to_string(R[0]) << "\n";
      cerr << "  R[1] = " << to_string(R[1]) << "\n";
      cerr << "  R[2] = " << to_string(R[2]) << "\n";
    }

    // Select a tricolored face and trace its tree paths to the boundary.
    std::vector<int> Q[3];
    std::vector<int> vvi = {-1, -1, -1};
    applySpernerFace(R, Fence, activeVertices, activeFaces, Q, vvi, debug);
    std::vector<int> xPID;
    const int newPID = createTripod(Q, vvi, PodIDs, xPID);

    // create new bag
    const int bagIndex = (int)bags.size();
    bags.push_back(addBag(PodIDs, xPID));
    bag2parent.push_back(-1);
    bagRegionFromParent.push_back(-1);
    CHECK((depth == 0 && deferredParentBag == -1 &&
           deferredRegion == -1) ||
          (depth > 0 && 0 <= deferredParentBag &&
           deferredParentBag < bagIndex &&
           0 <= deferredRegion && deferredRegion < 3),
          "invalid parent or region for a deferred PPS call");
    bag2parent[bagIndex] = deferredParentBag;
    bagRegionFromParent[bagIndex] = deferredRegion;
    if (newPID != -1) {
      CHECK(podCreatingBag[newPID] == -1);
      podCreatingBag[newPID] = bagIndex;
    }
    LOG_IF(debug, "added bag[%d]: (%s)", bagIndex, to_string(bags.back()).c_str());
    LOG_IF(debug, "  PodIDs: %s", to_string(PodIDs).c_str());
    LOG_IF(debug, "  newPID: %d", newPID);

    unordered_set<int> usedChildFaces;
    vector<DeferredRec> deferredChildren;
    scheduleChildRegions(graph, depth, bagIndex, R, Q, vvi, activeFaces,
                         usedChildFaces, deferredChildren);
    verifyRegionCoverage(graph, Q, vvi, newPID, activeFaces, usedChildFaces);

    // Push children in reverse order so the LIFO work list visits regions
    // in depth-first order.
    for (int j = (int)deferredChildren.size() - 1; j >= 0; j--) {
      pending->push_back(std::move(deferredChildren[j]));
    }

    LOG_IF(debug, "completed bag %d; num pods = %d", bagIndex, pods.size());

    return bagIndex;
  }

  // Each boundary piece of the fence is one or two vertical paths of a
  // distinct earlier tripod.
  void checkBoundaryTripods(const vector<Pod>& P, const vector<int>& PodIDs) {
    CHECK(P.size() == PodIDs.size());
    const size_t k = PodIDs.size();

    CHECK(1 <= k && k <= 3);
    for (size_t j = 0; j < k; j++) {
      const auto& pod = P[j];

      CHECK(pod.isUnipod() || pod.isBipod());

      for (auto& path : pod.paths) {
        if (path.empty())
          continue;

        const int minL = minLayer(path);
        const int maxL = maxLayer(path);
        CHECK(minL <= maxL);
        CHECK(maxL - minL + 1 == (int)path.size());

        for (size_t i = 0; i < path.size(); i++) {
          CHECK(i + 1 == path.size() || isBFSTreeEdge(path[i], path[i + 1]));
          CHECK(vertex2pod[path[i]] == PodIDs[j]);
        }
      }
    }

    // check distinct PodIDs
    for (size_t i = 0; i < k; i++) {
      for (size_t j = i + 1; j < k; j++) {
        CHECK(PodIDs[i] != PodIDs[j]);
      }
    }
  }

  // Split the fence into three nonempty consecutive paths, each in one
  // boundary tripod, colored 1, 2, 3.
  void colorBoundary(const vector<Pod>& P, std::vector<int> (&R)[3]) {
    const size_t k = P.size();

    if (k == 1) {
      auto vec = P[0].concat();
      CHECK(vec.size() >= 3);
      R[0] = {vec.front()};
      R[1] = vector<int>(vec.begin() + 1, vec.end() - 1);
      R[2] = {vec.back()};
    } else if (k == 2) {
      auto vec0 = P[0].concat();
      auto vec1 = P[1].concat();
      CHECK(vec0.size() >= 2 || vec1.size() >= 2);

      if (vec0.size() >= 2) {
        R[0] = {vec0[0]};
        R[1] = vector<int>(vec0.begin() + 1, vec0.end());
        R[2] = vec1;
      } else {
        R[0] = {vec1[0]};
        R[1] = vector<int>(vec1.begin() + 1, vec1.end());
        R[2] = vec0;
      }
    } else {
      for (size_t i = 1; i <= k / 3; i++) {
        auto vec = P[i - 1].concat();
        R[0].insert(R[0].end(), vec.begin(), vec.end());
      }

      for (size_t i = k / 3 + 1; i <= 2 * k / 3; i++) {
        auto vec = P[i - 1].concat();
        R[1].insert(R[1].end(), vec.begin(), vec.end());
      }

      for (size_t i = 2 * k / 3 + 1; i <= k; i++) {
        auto vec = P[i - 1].concat();
        R[2].insert(R[2].end(), vec.begin(), vec.end());
      }
    }

    CHECK(R[0].size() > 0 && R[1].size() > 0 && R[2].size() > 0);
  }

  // The tripod of the selected face (if any of its paths is nonempty).
  // Returns its id and the tripod of each color class (xPID).
  int createTripod(const std::vector<int> (&Q)[3], const vector<int>& vvi,
                   const vector<int>& PodIDs, vector<int>& xPID) {
    xPID = {-1, -1, -1};
    std::vector<vector<int>> newQ;

    for (int i = 0; i < 3; i++) {
      if (Q[i].empty())
        continue;

      newQ.push_back(Q[i]);
    }

    // create a new Pod, if needed
    int newPID = -1;
    if (!newQ.empty()) {
      auto xp = Pod(newQ);
      newPID = addPod(xp);
      podBoundaryParents[newPID] = PodIDs;
      podSelectedFace[newPID] = {
          Q[0].empty() ? vvi[0] : Q[0].front(),
          Q[1].empty() ? vvi[1] : Q[1].front(),
          Q[2].empty() ? vvi[2] : Q[2].front()};

      for (int i = 0; i < 3; i++) {
        if (xPID[i] == -1 && !Q[i].empty()) {
          xPID[i] = newPID;
        }
      }
    }
    return newPID;
  }

  // The regions R^1, R^2, R^3 left by the new tripod, as recursive calls
  // to schedule (deferredChildren); checks they are disjoint disks inside
  // the current one.
  void scheduleChildRegions(PlanarGraph& graph, int depth, int bagIndex,
                            const std::vector<int> (&R)[3], const std::vector<int> (&Q)[3],
                            const vector<int>& vvi, const unordered_set<int>& activeFaces,
                            unordered_set<int>& usedChildFaces,
                            vector<DeferredRec>& deferredChildren) {
    std::vector<int> R_minus[3];
    std::vector<int> R_plus[3];

    for (int i = 0; i < 3; i++) {
      R_minus[i] = vector<int>(R[i].begin(), find(R[i].begin(), R[i].end(), vvi[i]) + 1);
      R_plus[i] = vector<int>(find(R[i].begin(), R[i].end(), vvi[i]), R[i].end());
    }

    for (int i = 0; i < 3; i++) {
      const int i1 = (i + 1) % 3;
      size_t intFaceSize = 0;
      intFaceSize += Q[i].size();
      intFaceSize += R_plus[i].size();
      intFaceSize += R_minus[i1].size();
      intFaceSize += Q[i1].size();

      if (intFaceSize > 2) {
        std::vector<int> innerFence;
        innerFence.reserve(intFaceSize);
        innerFence.insert(innerFence.end(), Q[i].begin(), Q[i].end());
        innerFence.insert(innerFence.end(), R_plus[i].begin(), R_plus[i].end());
        innerFence.insert(innerFence.end(), R_minus[i1].begin(), R_minus[i1].end());
        innerFence.insert(innerFence.end(), Q[i1].rbegin(), Q[i1].rend());


        {
          const set<int> distinctChildFence(
              innerFence.begin(), innerFence.end());
          CHECK(distinctChildFence.size() == innerFence.size(),
                "deferred PPS fence repeats a boundary vertex");
          for (size_t j = 0; j < innerFence.size(); j++) {
            CHECK(adj.test(
                      innerFence[j],
                      innerFence[(j + 1) % innerFence.size()]),
                  "deferred PPS fence has a missing boundary edge");
          }
          unordered_set<int> childFaces;
          vector<int> childVertices =
              getActive(graph, innerFence, childFaces);
          CHECK(childVertices.size() >= innerFence.size());
          CHECK(childFaces.size() < activeFaces.size(),
                "deferred PPS region did not reduce the face count");
          for (int face : childFaces) {
            CHECK(activeFaces.count(face),
                  "deferred child region contains a face outside its parent");
            CHECK(usedChildFaces.insert(face).second,
                  "two deferred child regions overlap in a face");
          }
          if (childVertices.size() > innerFence.size()) {
            deferredChildren.push_back(
                {depth + 1, std::move(innerFence), bagIndex, i,
                 std::move(childFaces), std::move(childVertices)});
          }
        }
      }
    }
  }

  // Every face of the current disk lies in the selected face, in a child
  // region, or touches the new tripod.
  void verifyRegionCoverage(PlanarGraph& graph, const std::vector<int> (&Q)[3],
                            const vector<int>& vvi, int newPID,
                            const unordered_set<int>& activeFaces,
                            const unordered_set<int>& usedChildFaces) {
    vector<int> selectedVertices;
    for (int i = 0; i < 3; i++) {
      selectedVertices.push_back(
          Q[i].empty() ? vvi[i] : Q[i].front());
    }
    const Face selectedFace = graph.extractFace(selectedVertices);
    const string selectedHash = selectedFace.hash();
    CHECK(hash2faceIdx.count(selectedHash),
          "selected tricolored face is missing from the face index");
    const int selectedFaceId = hash2faceIdx.at(selectedHash);
    CHECK(activeFaces.count(selectedFaceId),
          "selected tricolored face is outside the recursive disk");
    for (int faceId : activeFaces) {
      if (usedChildFaces.count(faceId) || faceId == selectedFaceId) {
        continue;
      }
      bool touchesNewTripod = false;
      if (newPID != -1) {
        for (int vertex : faces[faceId]) {
          touchesNewTripod |= vertex2pod[vertex] == newPID;
        }
      }
      CHECK(touchesNewTripod,
            "recursive call left face %d outside every child region "
            "and the new tripod", faceId);
    }
  }

  /// Find the Sperner face and corresponding paths
  void applySpernerFace(
      const vector<int> (&R)[3],
      const vector<int>& F,
      const vector<int>& activeVertices,
      const unordered_set<int>& activeFaces,
      vector<int> (&Q)[3],
      vector<int>& vvi,
      bool debug
  ) {
    auto isF = vector<bool>(n, false);

    for (auto v : F) {
      isF[v] = true;
    }

    // 3-coloring of vertices
    auto color = vector<int>(n, -1);

    for (int i = 0; i < 3; i++) {
      for (int v : R[i]) {
        CHECK(color[v] == -1);
        CHECK(isF[v]);
        color[v] = i + 1;
      }
    }

    for (int i : activeVertices) {
      if (color[i] != -1) {
        CHECK(isF[i]);
        continue;
      }

      int v = i;

      while (!isF[v]) {
        v = parent[v];
      }

      CHECK(v != -1 && color[v] != -1);
      color[i] = color[v];
    }

    // finding Sperner's face
    vector<int> vi = {-1, -1, -1};
    int numColoredFaces = 0;
    int selectedFaceId = -1;

    for (int faceId : activeFaces) {
      auto& face = faces[faceId];

      if (color[face[0]] == -1 || color[face[1]] == -1 || color[face[2]] == -1) {
        continue;
      }

      if (isF[face[0]] && isF[face[1]] && isF[face[2]] && F.size() == 3) {
        continue;
      }

      if (color[face[0]] == color[face[1]]) {
        continue;
      }

      if (color[face[0]] == color[face[2]]) {
        continue;
      }

      if (color[face[1]] == color[face[2]]) {
        continue;
      }

      if (selectedFaceId == -1 || faceId < selectedFaceId) {
        selectedFaceId = faceId;
        for (int i = 0; i < 3; i++) {
          const int c = color[face[i]];
          CHECK(1 <= c && c <= 3);
          vi[c - 1] = face[i];
        }
      }

      numColoredFaces++;
    }

    CHECK(numColoredFaces >= 1 && selectedFaceId >= 0,
          "Sperner call has no tricolored face");
    CHECK(vi[0] != -1 && vi[1] != -1 && vi[2] != -1);
    CHECK(adj.test(vi[0], vi[1]) && adj.test(vi[0], vi[2]) && adj.test(vi[1], vi[2]));

    if (debug) {
      cerr << "  Sperner face: (" << vi[0] << ", " << vi[1] << ", " << vi[2] << ")\n";
    }

    for (int i = 0; i < 3; i++) {
      int v = vi[i];

      while (!isF[v]) {
        Q[i].push_back(v);
        v = parent[v];
      }

      vvi[i] = v;
    }

    if (debug) {
      cerr << "  Q[0] = (" << to_string(Q[0]) << ")\n";
      cerr << "  Q[1] = (" << to_string(Q[1]) << ")\n";
      cerr << "  Q[2] = (" << to_string(Q[2]) << ")\n";
    }
  }

  /// returns index for the newly added pod
  int addPod(const Pod& pod) {
    const auto vertices = pod.concat();
    const int podId = (int)pods.size();

    for (auto v : vertices) {
      CHECK(vertex2pod[v] == -1, "vertex %d of a new tripod is already in tripod %d",
            v, vertex2pod[v]);
      vertex2pod[v] = podId;
    }

    pods.push_back(pod);
    podSelectedFace.push_back({-1, -1, -1});
    podBoundaryParents.emplace_back();
    podCreatingBag.push_back(-1);
    LOG_IF(debug, "added pod[%d]: (%s)", podId, to_string(vertices).c_str());
    return podId;
  }

  /// Add a bag consisting of given (pod) ids plus x (if that's not -1)
  std::vector<int> addBag(const std::vector<int>& ids, const std::vector<int>& x) {
    std::vector<int> res;

    for (int id : ids) {
      CHECK(id != -1);

      if (find(res.begin(), res.end(), id) == res.end()) {
        res.push_back(id);
      }
    }

    for (int id : x) {
      if (id != -1 && find(res.begin(), res.end(), id) == res.end()) {
        res.push_back(id);
      }
    }

    // Verify that the bag contains distinct elements
    for (size_t i = 0; i < res.size(); i++) {
      for (size_t j = i + 1; j < res.size(); j++) {
        CHECK(res[i] != res[j]);
      }
    }

    return res;
  }

  /// Return vertices in the region bounded by the fence, including its boundary.
  vector<int> getActive(PlanarGraph& graph, const vector<int>& F, std::unordered_set<int>& activeFaces) {
    CHECK(F.size() >= 3);
    auto isActive = vector<bool>(n, false);
    vector<int> active;
    set<pair<int, int>> isFence;
    for (size_t i = 0; i < F.size(); i++) {
      int u = F[i];
      int v = F[(i + 1) % F.size()];
      isFence.insert(make_pair(u, v));
      isFence.insert(make_pair(v, u));
    }

    queue<int> q;
    auto u0 = graph.vertices[F[0]];
    auto v0 = graph.vertices[F[1]];
    auto edge0 = u0->adjacentEdge(v0);
    auto face0 = graph.extractRightFace(u0, edge0);
    CHECK(face0.length() == 3 || face0.length() == 4);
    int face0Id = hash2faceIdx[face0.hash()];
    q.push(face0Id);
    activeFaces.insert(face0Id);

    while (!q.empty()) {
      auto faceId = q.front();
      q.pop();

      for (int i = 0; i < (int)faces[faceId].size(); i++) {
        int u = faces[faceId][i];
        int v = faces[faceId][(i + 1) % faces[faceId].size()];

        if (!isActive[u]) {
          isActive[u] = true;
          active.push_back(u);
        }

        if (!isActive[v]) {
          isActive[v] = true;
          active.push_back(v);
        }

        if (isFence.find(make_pair(u, v)) == isFence.end()) {
          int nextFaceId = facesAdj[faceId][i];

          if (activeFaces.find(nextFaceId) == activeFaces.end()) {
            q.push(nextFaceId);
            activeFaces.insert(nextFaceId);
          }
        }
      }
    }

    return active;
  }

  /// Split a given fence into pods
  void splitFence(const vector<int>& F, vector<Pod>& P, vector<int>& PIDs) {
    CHECK(F.size() >= 3);
    int startIndex = 0;

    for (int i = 0; i < (int)F.size(); i++) {
      int i1 = (i + 1) % F.size();

      if (vertex2pod[F[i]] != vertex2pod[F[i1]]) {
        startIndex = i1;
        break;
      }
    }

    vector<int> curPod = {F[startIndex]};

    for (int i = 1; i < (int)F.size(); i++) {
      int prevI = (i - 1 + startIndex) % F.size();
      int curI = (i + startIndex) % F.size();

      if (vertex2pod[F[prevI]] == vertex2pod[F[curI]]) {
        curPod.push_back(F[curI]);
      } else {
        auto paths = splitIntoPaths(curPod);
        CHECK(paths.size() <= 3);
        P.push_back(Pod(paths));
        PIDs.push_back(vertex2pod[paths[0][0]]);
        curPod = {F[curI]};
      }
    }

    if (curPod.size() > 0) {
      auto paths = splitIntoPaths(curPod);
      CHECK(paths.size() <= 2);
      P.push_back(Pod(paths));
      PIDs.push_back(vertex2pod[paths[0][0]]);
    }
  }

  /// Split a given pod into paths
  vector<vector<int>> splitIntoPaths(const vector<int>& vec) {
    CHECK(vec.size() >= 1);
    int pid = vertex2pod[vec[0]];

    for (int v : vec) {
      CHECK(vertex2pod[v] == pid);
    }

    vector<vector<int>> paths;
    vector<int> curPath = {vec[0]};

    for (size_t i = 1; i < vec.size(); i++) {
      if (isBFSTreeEdge(vec[i - 1], vec[i])) {
        curPath.push_back(vec[i]);
      } else {
        paths.push_back(curPath);
        curPath = {vec[i]};
      }
    }

    if (curPath.size() > 0) {
      paths.push_back(curPath);
    }

    return paths;
  }

  int minLayer(const vector<int>& path) {
    CHECK(path.size() > 0);
    int res = layer[path[0]];

    for (auto v : path) {
      res = min(res, layer[v]);
    }

    return res;
  }

  int maxLayer(const vector<int>& path) {
    CHECK(path.size() > 0);
    int res = layer[path[0]];

    for (auto v : path) {
      res = max(res, layer[v]);
    }

    return res;
  }

  /// Check whether edge (u, v) is a part of BFS tree
  bool isBFSTreeEdge(int u, int v) const {
    return parent[u] == v || parent[v] == u;
  }

  /// Verify correctness of constructed layered h-partition
  void verify() {
    if (verbose >= 2) {
      cerr << "pods:\n";

      for (int i = 0; i < (int)pods.size(); i++) {
        cerr << "  pod " << i << ": ";
        pods[i].print();
        cerr << "\n";
      }

      cerr << "bags:\n";

      for (int i = 0; i < (int)bags.size(); i++) {
        cerr << "  bag " << i << ": (" << to_string(bags[i]) << "),";
        cerr << "  bag2parent[" << i << "] = " << bag2parent[i] << "\n";
      }
    }

    CHECK((int)vertex2pod.size() == n);

    for (int i = 0; i < n; i++) {
      string msg = "vertex2pod[" + to_string(i) + "] = " + to_string(vertex2pod[i]);
      CHECK(0 <= vertex2pod[i] && vertex2pod[i] < (int)pods.size(), msg.c_str());
    }

    // verify all paths are 'vertical'
    for (auto& pod : pods) {
      for (auto& path : pod.paths) {
        if (path.empty()) {
          continue;
        }

        const int minL = minLayer(path);
        const int maxL = maxLayer(path);
        CHECK(minL <= maxL);
        CHECK(maxL - minL + 1 == (int)path.size());

        for (size_t i = 0; i + 1 < path.size(); i++) {
          CHECK(isBFSTreeEdge(path[i], path[i + 1]));
        }
      }
    }

    CHECK((int)ocIdx.size() == n);
    CHECK(bag2parent.size() == bags.size());
    CHECK(0 <= rootBag && rootBag < (int)bags.size() &&
          bag2parent[rootBag] == -1);
    vector<int> occurrences(pods.size(), 0), sharedEdges(pods.size(), 0);
    for (int i = 0; i < (int)bags.size(); i++) {
      const auto& bag = bags[i];
      CHECK(1 <= bag.size() && bag.size() <= 4);
      set<int> distinct;
      for (int pod : bag) {
        CHECK(0 <= pod && pod < (int)pods.size() && distinct.insert(pod).second);
        occurrences[pod]++;
      }
      if (i == rootBag) continue;
      CHECK(0 <= bag2parent[i] && bag2parent[i] < i,
            "decomposition parent is not an earlier bag");
      const auto& parentBag = bags[bag2parent[i]];
      int commonPods = 0;
      for (int pod : bag) {
        if (std::find(parentBag.begin(), parentBag.end(), pod) != parentBag.end()) {
          sharedEdges[pod]++;
          commonPods++;
        }
      }
      CHECK(commonPods > 0, "adjacent decomposition bags are disjoint");
    }
    // Bags containing one tripod induce a forest in the parent tree.
    // One fewer shared edge than occurrences is exactly connectivity.
    for (int pod = 0; pod < (int)pods.size(); pod++) {
      CHECK(occurrences[pod] > 0 && sharedEdges[pod] + 1 == occurrences[pod],
            "bags containing tripod %d do not form a subtree", pod);
    }

    // The recursive region of a later neighbor meets at most two paths
    // of the earlier tripod.
    // Check all original edges, across all layers, not one selected neighbor.
    CHECK((int)vertex2path.size() == n);
    map<EdgeTy, unsigned> earlierPaths;
    for (const auto& [u, v] : edges) {
      const int podU = vertex2pod[u], podV = vertex2pod[v];
      if (podU == podV) continue;
      const EdgeTy pair = make_edge(podU, podV);
      const int path = vertex2path[podU == pair.first ? u : v];
      CHECK(0 <= path && path < pods[pair.first].numPaths());
      earlierPaths[pair] |= 1u << path;
    }
    for (const auto& [pair, mask] : earlierPaths) {
      CHECK(__builtin_popcount(mask) <= 2,
            "later tripod %d touches all three paths of earlier tripod %d",
            pair.second, pair.first);
    }
  }

};

namespace {

// A non-owning view of the embedded tripod quotient. Edge* values refer to
// edges of graph, which must outlive this view. In particular, a loop has two
// distinct endpoint incidences even though both belong to the same pod.
struct RawTripodQuotient {
  struct EdgeRecord {
    Edge* originalEdge;
    int endpointVertex[2];
    int endpointPod[2];
    int endpointPath[2];
    bool selectedFaceBase;
  };

  struct Incidence {
    Edge* originalEdge;
    int endpoint;  // 0 = original source, 1 = original target
    int pathId;
  };

  vector<EdgeRecord> edges;
  unordered_map<Edge*, int> edgeIndex;
  vector<vector<Incidence>> clockwiseRotation;
  Adjacency simplePodAdj;

  explicit RawTripodQuotient(int numPods)
      : clockwiseRotation(numPods), simplePodAdj(numPods) {}
};

class RawQuotientBuilder {
 public:
  RawQuotientBuilder(const LayeredHPartition& lhp, const PlanarGraph& graph)
      : lhp(lhp), graph(graph), numPods((int)lhp.pods.size()),
        raw(make_unique<RawTripodQuotient>(numPods)), baseSeams(numPods) {
    CHECK((int)lhp.podSelectedFace.size() == numPods);
    CHECK((int)lhp.vertex2pod.size() == graph.numberOfVertices());
    CHECK((int)lhp.vertex2path.size() == graph.numberOfVertices());
  }

  unique_ptr<RawTripodQuotient> build() {
    collectPathsAndSelectedFaces();
    recordRetainedEdges();
    buildRotations();
    verifyRotations();
    return std::move(raw);
  }

 private:
    struct BaseSeam {
      Edge* edge;
      int afterPath;
      int beforePath;
    };

  // The vertical-path edges of every tripod (contracted) and the edges of the
  // face selected to create it (they become loops at the path seams).
  void collectPathsAndSelectedFaces() {
    for (int podId = 0; podId < numPods; podId++) {
      const auto& pod = lhp.pods[podId];
      const int pathCount = pod.numPaths();
      CHECK(1 <= pathCount && pathCount <= 3);
      for (int pathId = 0; pathId < pathCount; pathId++) {
        const auto& path = pod.paths[pathId];
        CHECK(!path.empty());
        for (int index = 0; index < (int)path.size(); index++) {
          const int v = path[index];
          CHECK(0 <= v && v < graph.numberOfVertices());
          CHECK(lhp.vertex2pod[v] == podId && lhp.vertex2path[v] == pathId,
                "pod/path label mismatch at original vertex %d", v);
          if (index == 0) {
            continue;
          }
          const int parentVertex = path[index - 1];
          CHECK(lhp.parent[v] == parentVertex,
                "vertical path edge (%d,%d) disagrees with BFS parent", parentVertex, v);
          Edge* edge = graph.vertices[v]->adjacentEdge(graph.vertices[parentVertex]);
          CHECK(edge != nullptr, "missing vertical path edge (%d,%d)", parentVertex, v);
          CHECK(verticalEdges.insert(edge).second,
                "vertical path edge (%d,%d) appears twice", parentVertex, v);
        }
      }

      if (podId < 3) {
        CHECK(pathCount == 1);
        CHECK(lhp.podSelectedFace[podId] == (array<int, 3>{-1, -1, -1}));
        continue;
      }

      const auto& selected = lhp.podSelectedFace[podId];
      for (int v : selected) {
        CHECK(0 <= v && v < graph.numberOfVertices(),
              "pod %d has an invalid selected-face vertex %d", podId, v);
      }
      CHECK(selected[0] != selected[1] && selected[1] != selected[2] &&
            selected[2] != selected[0], "pod %d has a repeated selected-face vertex", podId);
      Face face = graph.extractFace({selected[0], selected[1], selected[2]});
      CHECK(face.length() == 3, "pod %d selected face is not triangular", podId);
      int selectedPathEnds = 0;
      for (int v : selected) {
        if (lhp.vertex2pod[v] == podId) {
          const int pathId = lhp.vertex2path[v];
          CHECK(0 <= pathId && pathId < pathCount &&
                v == pod.lowestVertex(pathId),
                "pod %d selected-face vertex %d is not a path end", podId, v);
          selectedPathEnds++;
        }
      }
      CHECK(selectedPathEnds == pathCount,
            "pod %d selected face has %d path ends, expected %d",
            podId, selectedPathEnds, pathCount);
      int numBaseEdges = 0;
      for (int i = 0; i < 3; i++) {
        const int u = face.vertices[i]->index;
        const int v = face.vertices[(i + 1) % 3]->index;
        const int pathU = lhp.vertex2pod[u] == podId ? lhp.vertex2path[u] : -1;
        const int pathV = lhp.vertex2pod[v] == podId ? lhp.vertex2path[v] : -1;
        if (pathU == -1 || pathV == -1) {
          continue;
        }
        CHECK(pathU != pathV);
        CHECK(u == pod.lowestVertex(pathU) && v == pod.lowestVertex(pathV),
              "selected-face base edge (%d,%d) is not between path ends", u, v);
        Edge* edge = face.edges[i];
        CHECK(edge->incident(graph.vertices[u]) && edge->incident(graph.vertices[v]));
        CHECK(!verticalEdges.count(edge));
        CHECK(baseOwner.emplace(edge, podId).second,
              "selected-face base edge (%d,%d) belongs to multiple pods", u, v);
        if (pathCount == 3) {
          CHECK(pathV == (pathU + 1) % 3,
                "pod %d path order disagrees with selected-face orientation", podId);
        } else {
          CHECK(pathCount == 2 && pathV == 1 - pathU);
        }
        baseSeams[podId].push_back({edge, pathU, pathV});
        numBaseEdges++;
      }
      CHECK(numBaseEdges == (pathCount == 3 ? 3 : pathCount == 2 ? 1 : 0),
            "pod %d has %d selected-face base edges for %d paths",
            podId, numBaseEdges, pathCount);
    }
  }

  // Every edge of G that is not a vertical-path edge is an edge of the
  // quotient (a loop if both ends lie in one tripod).
  void recordRetainedEdges() {
    const auto originalEdges = graph.extractEdges();
    CHECK((int)originalEdges.size() == graph.numberOfEdges(),
          "raw extraction expects a loop-free original PlanarGraph");
    for (Edge* edge : originalEdges) {
      CHECK(edge != nullptr);
      const int u = edge->source->index;
      const int v = edge->target->index;
      CHECK(0 <= u && u < graph.numberOfVertices());
      CHECK(0 <= v && v < graph.numberOfVertices());
      CHECK(u != v, "original PlanarGraph contains a loop");
      const int podU = lhp.vertex2pod[u];
      const int podV = lhp.vertex2pod[v];
      const int pathU = lhp.vertex2path[u];
      const int pathV = lhp.vertex2path[v];
      CHECK(0 <= podU && podU < numPods && 0 <= podV && podV < numPods);
      CHECK(0 <= pathU && pathU < 3 && 0 <= pathV && pathV < 3);
      if (verticalEdges.count(edge)) {
        CHECK(podU == podV && pathU == pathV && lhp.isBFSTreeEdge(u, v));
        CHECK(!baseOwner.count(edge));
        continue;
      }
      CHECK(!lhp.isBFSTreeEdge(u, v) || podU != podV,
            "intra-pod BFS edge (%d,%d) was not classified as vertical", u, v);
      if (baseOwner.count(edge)) {
        CHECK(podU == podV && baseOwner.at(edge) == podU && pathU != pathV,
              "selected-face edge (%d,%d) does not become a loop", u, v);
      }
      const int index = (int)raw->edges.size();
      CHECK(raw->edgeIndex.emplace(edge, index).second,
            "original edge (%d,%d) was enumerated twice", u, v);
      raw->edges.push_back({
          edge, {u, v}, {podU, podV}, {pathU, pathV},
          baseOwner.count(edge) != 0});
      if (podU != podV) {
        raw->simplePodAdj.set(podU, podV);
        raw->simplePodAdj.set(podV, podU);
      }
    }
    raw->simplePodAdj.shrink_to_fit();
  }

  void appendIncidence(int podId, int originalVertex, Edge* edge) {
      CHECK(raw->edgeIndex.count(edge),
            "raw rotation includes missing/vertical edge at vertex %d", originalVertex);
      const auto& record = raw->edges[raw->edgeIndex.at(edge)];
      int endpoint = -1;
      if (record.endpointVertex[0] == originalVertex) {
        endpoint = 0;
      } else if (record.endpointVertex[1] == originalVertex) {
        endpoint = 1;
      }
      CHECK(endpoint != -1, "raw edge is not incident to original vertex %d", originalVertex);
      CHECK(record.originalEdge == edge);
      CHECK(record.endpointPod[endpoint] == podId &&
            lhp.vertex2pod[originalVertex] == podId);
      CHECK(record.endpointPath[endpoint] == lhp.vertex2path[originalVertex]);
      auto& count = incidenceCount[edge];
      CHECK(count[endpoint] == 0,
            "original edge (%d,%d) has a repeated endpoint incidence",
            record.endpointVertex[0], record.endpointVertex[1]);
      count[endpoint]++;
      raw->clockwiseRotation[podId].push_back({
          edge, endpoint, record.endpointPath[endpoint]});
  }

  bool isBoundary(int podId, Edge* edge) {
      if (verticalEdges.count(edge)) {
        CHECK(lhp.vertex2pod[edge->source->index] == podId &&
              lhp.vertex2pod[edge->target->index] == podId);
        return true;
      }
      if (baseOwner.count(edge)) {
        CHECK(baseOwner.at(edge) == podId);
        return true;
      }
      return false;
  }

  Edge* scanUntilBoundary(int podId, int originalVertex, Edge* first) {
      Vertex* vertex = graph.vertices[originalVertex];
      CHECK(first != nullptr && first->incident(vertex) && isBoundary(podId, first));
      const int start = vertex->findEdgeIndex(first);
      CHECK(start >= 0);
      for (int step = 1; step <= vertex->degree(); step++) {
        Edge* edge = vertex->edges[(start + step) % vertex->degree()];
        if (isBoundary(podId, edge)) {
          return edge;
        }
        appendIncidence(podId, originalVertex, edge);
      }
      CHECK(false, "pod %d boundary walk failed at vertex %d", podId, originalVertex);
      return static_cast<Edge*>(nullptr);
  }

  // The rotation at each tripod: walk around its vertical paths and record
  // the incidences between consecutive boundary edges.
  void buildRotations() {
    for (int podId = 0; podId < numPods; podId++) {
      const auto& pod = lhp.pods[podId];
      const int pathCount = pod.numPaths();
      if (pathCount == 1 && pod.paths[0].size() == 1) {
        const int v = pod.paths[0][0];
        for (Edge* edge : graph.vertices[v]->edges) {
          CHECK(!isBoundary(podId, edge));
          appendIncidence(podId, v, edge);
        }
        continue;
      }

      auto verticalToParent = [&](int pathId, int index) {
        CHECK(index > 0);
        const auto& path = pod.paths[pathId];
        Edge* edge = graph.vertices[path[index]]->adjacentEdge(
            graph.vertices[path[index - 1]]);
        CHECK(edge != nullptr && verticalEdges.count(edge));
        return edge;
      };
      auto basePrev = [&](int pathId) {
        CHECK(pathCount > 1);
        const int prev = (pathId + pathCount - 1) % pathCount;
        Edge* edge = graph.vertices[pod.lowestVertex(pathId)]->adjacentEdge(
            graph.vertices[pod.lowestVertex(prev)]);
        CHECK(edge != nullptr && baseOwner.count(edge) && baseOwner.at(edge) == podId);
        return edge;
      };

      for (int pathId = 0; pathId < pathCount; pathId++) {
        const auto& path = pod.paths[pathId];
        const int len = (int)path.size();
        Edge* first = pathCount > 1 ? basePrev(pathId)
                                    : verticalToParent(pathId, len - 1);
        Edge* boundary = first;
        for (int index = len - 1; index >= 0; index--) {
          boundary = scanUntilBoundary(podId, path[index], boundary);
        }
        const int lastIndex = pathCount == 1 ? len - 2 : len - 1;
        for (int index = 1; index <= lastIndex; index++) {
          boundary = scanUntilBoundary(podId, path[index], boundary);
        }
        if (pathCount == 1) {
          CHECK(boundary == first,
                "unipod %d boundary walk did not close", podId);
        } else {
          const int next = (pathId + 1) % pathCount;
          Edge* nextBase = graph.vertices[pod.lowestVertex(pathId)]->adjacentEdge(
              graph.vertices[pod.lowestVertex(next)]);
          CHECK(boundary == nextBase,
                "pod %d path %d boundary walk ended at the wrong base edge",
                podId, pathId);
        }

        // A bipod has only one base edge. The selected face's clockwise
        // orientation chooses which of its two path seams contains the loop.
        for (const auto& seam : baseSeams[podId]) {
          if (seam.afterPath == pathId) {
            appendIncidence(podId, pod.lowestVertex(seam.afterPath), seam.edge);
            appendIncidence(podId, pod.lowestVertex(seam.beforePath), seam.edge);
          }
        }
      }
    }
  }

  // Each retained edge has two incidences, the ports form consecutive blocks
  // in the rotation, and every selected-face loop sits at its path seam.
  void verifyRotations() {
    for (const auto& record : raw->edges) {
      const auto it = incidenceCount.find(record.originalEdge);
      CHECK(it != incidenceCount.end() &&
            it->second[0] == 1 && it->second[1] == 1,
            "retained edge (%d,%d) does not have exactly two raw incidences",
            record.endpointVertex[0], record.endpointVertex[1]);
    }
    for (Edge* edge : verticalEdges) {
      CHECK(!raw->edgeIndex.count(edge) && !incidenceCount.count(edge),
            "vertical path edge (%d,%d) leaked into the raw quotient",
            edge->source->index, edge->target->index);
    }

    for (int podId = 0; podId < numPods; podId++) {
      const int pathCount = lhp.pods[podId].numPaths();
      const auto& rotation = raw->clockwiseRotation[podId];
      if (pathCount > 1) {
        CHECK(!rotation.empty());
        int transitions = 0;
        for (int i = 0; i < (int)rotation.size(); i++) {
          const int a = rotation[i].pathId;
          const int b = rotation[(i + 1) % rotation.size()].pathId;
          if (a != b) {
            CHECK(b == (a + 1) % pathCount,
                  "pod %d raw rotation reverses path order", podId);
            transitions++;
          }
        }
        CHECK(transitions == pathCount,
              "pod %d raw rotation does not have %d cyclic path blocks",
              podId, pathCount);
      }
      for (const auto& seam : baseSeams[podId]) {
        int first = -1;
        int second = -1;
        for (int i = 0; i < (int)rotation.size(); i++) {
          if (rotation[i].originalEdge != seam.edge) {
            continue;
          }
          if (rotation[i].pathId == seam.afterPath) {
            CHECK(first == -1);
            first = i;
          } else if (rotation[i].pathId == seam.beforePath) {
            CHECK(second == -1);
            second = i;
          } else {
            CHECK(false, "pod %d base loop has an unexpected path", podId);
          }
        }
        CHECK(first >= 0 && second == (first + 1) % (int)rotation.size(),
              "pod %d selected-face loop is not at its path seam", podId);
        CHECK(incidenceCount.at(seam.edge)[0] == 1 &&
              incidenceCount.at(seam.edge)[1] == 1,
              "pod %d selected-face loop does not have two endpoint incidences",
              podId);
      }
      if (pathCount == 2) {
        CHECK(baseSeams[podId].size() == 1,
              "bipod %d must have exactly one base edge and one occupied seam",
              podId);
      } else if (pathCount == 3) {
        CHECK(baseSeams[podId].size() == 3,
              "tripod %d must have a base edge at each path seam", podId);
      }
    }
  }

  const LayeredHPartition& lhp;
  const PlanarGraph& graph;
  const int numPods;
  unique_ptr<RawTripodQuotient> raw;
  vector<vector<BaseSeam>> baseSeams;
  unordered_map<Edge*, int> baseOwner;
  unordered_set<Edge*> verticalEdges;
  unordered_map<Edge*, array<int, 2>> incidenceCount;
};

unique_ptr<RawTripodQuotient> extractRawTripodQuotient(
    const LayeredHPartition& lhp, const PlanarGraph& graph) {
  return RawQuotientBuilder(lhp, graph).build();
}

struct RawQuotientFaces {
  vector<vector<int>> faceDarts;
  vector<int> faceOfDart;
  vector<int> twin;
  vector<int> nextClockwise;
  vector<int> dartPod;
  vector<Edge*> dartEdge;
};

// Recover faces from the two original incidences of every retained edge.
// The face traversal includes both incidences of loops and all parallel edges.
RawQuotientFaces buildRawQuotientFaces(const RawTripodQuotient& raw) {
  RawQuotientFaces result;
  const int edgeCount = (int)raw.edges.size();
  const int dartCount = 2 * edgeCount;
  result.faceOfDart.assign(dartCount, -1);
  result.twin.assign(dartCount, -1);
  result.nextClockwise.assign(dartCount, -1);
  result.dartPod.assign(dartCount, -1);
  result.dartEdge.assign(dartCount, nullptr);

  unordered_map<Edge*, int> edgeId;
  for (int e = 0; e < edgeCount; e++) {
    CHECK(edgeId.emplace(raw.edges[e].originalEdge, e).second);
  }
  for (int pod = 0; pod < (int)raw.clockwiseRotation.size(); pod++) {
    const auto& rotation = raw.clockwiseRotation[pod];
    for (int pos = 0; pos < (int)rotation.size(); pos++) {
      const auto& incidence = rotation[pos];
      CHECK(edgeId.count(incidence.originalEdge));
      const int e = edgeId.at(incidence.originalEdge);
      CHECK(incidence.endpoint == 0 || incidence.endpoint == 1);
      const int dart = 2 * e + incidence.endpoint;
      const int nextPos = (pos + 1) % (int)rotation.size();
      const auto& nextIncidence = rotation[nextPos];
      CHECK(edgeId.count(nextIncidence.originalEdge));
      const int nextDart =
          2 * edgeId.at(nextIncidence.originalEdge) + nextIncidence.endpoint;
      CHECK(result.dartPod[dart] == -1,
            "raw dart %d occurs twice in tripod rotations", dart);
      result.dartPod[dart] = pod;
      result.dartEdge[dart] = incidence.originalEdge;
      result.nextClockwise[dart] = nextDart;
      CHECK(raw.edges[e].endpointPod[incidence.endpoint] == pod);
    }
  }
  for (int e = 0; e < edgeCount; e++) {
    const int a = 2 * e, b = 2 * e + 1;
    CHECK(result.dartPod[a] >= 0 && result.dartPod[b] >= 0);
    CHECK(result.nextClockwise[a] >= 0 && result.nextClockwise[b] >= 0);
    result.twin[a] = b;
    result.twin[b] = a;
    CHECK(result.dartEdge[a] == raw.edges[e].originalEdge &&
          result.dartEdge[b] == raw.edges[e].originalEdge);
  }

  vector<int> nextFaceDart(dartCount, -1);
  vector<int> indegree(dartCount, 0);
  for (int dart = 0; dart < dartCount; dart++) {
    const int next = result.nextClockwise[result.twin[dart]];
    CHECK(0 <= next && next < dartCount);
    CHECK(result.dartPod[next] == result.dartPod[result.twin[dart]],
          "face walk leaves tripod %d at a wrong corner",
          result.dartPod[result.twin[dart]]);
    nextFaceDart[dart] = next;
    indegree[next]++;
  }
  for (int dart = 0; dart < dartCount; dart++) {
    CHECK(indegree[dart] == 1,
          "raw quotient face successor is not a permutation");
  }

  for (int start = 0; start < dartCount; start++) {
    if (result.faceOfDart[start] != -1) {
      continue;
    }
    const int faceId = (int)result.faceDarts.size();
    result.faceDarts.emplace_back();
    int dart = start;
    do {
      CHECK(result.faceOfDart[dart] == -1,
            "raw face walk reached another face before closing");
      result.faceOfDart[dart] = faceId;
      result.faceDarts.back().push_back(dart);
      CHECK((int)result.faceDarts.back().size() <= dartCount);
      dart = nextFaceDart[dart];
    } while (dart != start);
  }
  for (int dart = 0; dart < dartCount; dart++) {
    CHECK(result.faceOfDart[dart] >= 0);
  }
  CHECK((int)result.faceDarts.size() ==
            edgeCount - (int)raw.clockwiseRotation.size() + 2,
        "contracted embedding violates Euler's formula: V=%d E=%d F=%d",
        (int)raw.clockwiseRotation.size(), edgeCount,
        (int)result.faceDarts.size());

  for (int e = 0; e < edgeCount; e++) {
    if (!raw.edges[e].selectedFaceBase) {
      continue;
    }
    CHECK(raw.edges[e].endpointPod[0] == raw.edges[e].endpointPod[1]);
    const int faceA = result.faceOfDart[2 * e];
    const int faceB = result.faceOfDart[2 * e + 1];
    CHECK(result.faceDarts[faceA].size() == 1 ||
          result.faceDarts[faceB].size() == 1,
          "selected-face loop (%d,%d) does not bound an empty monogon",
          raw.edges[e].endpointVertex[0], raw.edges[e].endpointVertex[1]);
  }
  return result;
}

void verifyImmediateRecursiveRegions(
    const LayeredHPartition& lhp,
    const RawTripodQuotient& raw,
    const TreePartition& tp) {
  const int podCount = (int)lhp.pods.size();
  CHECK((int)lhp.podCreatingBag.size() == podCount);
  CHECK(lhp.bag2parent.size() == lhp.bagRegionFromParent.size());
  for (int pod = 3; pod < podCount; pod++) {
    CHECK(lhp.podCreatingBag[pod] >= 0 &&
          lhp.podCreatingBag[pod] < (int)lhp.bags.size());
  }
  map<pair<int, int>, int> componentRegion;
  for (const auto& record : raw.edges) {
    const int podA = record.endpointPod[0];
    const int podB = record.endpointPod[1];
    if (podA == podB) continue;
    const int earlier = std::min(podA, podB);
    const int later = std::max(podA, podB);
    if (earlier < 3 || lhp.pods[earlier].numPaths() != 3) {
      continue;
    }
    const int creatingCall = lhp.podCreatingBag[earlier];
    int call = lhp.podCreatingBag[later];
    CHECK(call != creatingCall);
    int region = -1;
    int steps = 0;
    while (call >= 0 && call != creatingCall) {
      const int parentCall = lhp.bag2parent[call];
      if (parentCall == creatingCall) {
        region = lhp.bagRegionFromParent[call];
        break;
      }
      call = parentCall;
      CHECK(++steps <= (int)lhp.bags.size(),
            "recursive call ancestry has a cycle");
    }
    CHECK(0 <= region && region < 3,
          "later tripod %d is not in an immediate region of tripod %d",
          later, earlier);
    const int endpoint = podA == earlier ? 0 : 1;
    const int touchedPath = record.endpointPath[endpoint];
    CHECK(touchedPath == region ||
          touchedPath == (region + 1) % 3,
          "later tripod %d reaches the third path of tripod %d",
          later, earlier);
    if (tp.vertex2depth[later] == tp.vertex2depth[earlier] + 1) {
      const int child = tp.vertex2bag[later];
      const pair<int, int> key = {earlier, child};
      const auto [it, inserted] = componentRegion.emplace(key, region);
      CHECK(inserted || it->second == region,
            "next-level component %d spans two immediate regions of tripod %d",
            child, earlier);
    }
  }
}

struct RawRotationAtoms {
  struct Gap {
    int leftSupportPod;
    int rightSupportPod;
    int lastLeftCopy;
    int firstRightCopy;
  };
  // For each incidence, exactly one of these is nonnegative.
  vector<int> classPod;
  vector<int> gapId;
  vector<int> supportPods;
  vector<Gap> gaps;
  // Alternating whole classes and gaps in clockwise order.
  // true denotes a support class (value = neighboring pod);
  // false denotes a gap (value = gap ID).
  vector<pair<bool, int>> cyclicAtoms;
};

// Copies of one same-level edge occupy one cyclic class. The sectors
// between consecutive copies belong to that class except for the
// exterior sector when there is only one support class.
RawRotationAtoms partitionRawRotation(
    const RawTripodQuotient& raw,
    const TreePartition& tp,
    int pod) {
  CHECK(0 <= pod && pod < (int)raw.clockwiseRotation.size());
  const auto& rotation = raw.clockwiseRotation[pod];
  const int length = (int)rotation.size();
  CHECK(length > 0);
  RawRotationAtoms atoms;
  atoms.classPod.assign(length, -1);
  atoms.gapId.assign(length, -1);

  vector<int> supportPositions;
  vector<int> supportLabels;
  for (int pos = 0; pos < length; pos++) {
    const auto& incidence = rotation[pos];
    CHECK(raw.edgeIndex.count(incidence.originalEdge));
    const auto& record = raw.edges[raw.edgeIndex.at(incidence.originalEdge)];
    const int other = record.endpointPod[1 - incidence.endpoint];
    if (other != pod && tp.vertex2depth[other] == tp.vertex2depth[pod]) {
      CHECK(tp.vertex2bag[other] == tp.vertex2bag[pod]);
      supportPositions.push_back(pos);
      supportLabels.push_back(other);
      atoms.classPod[pos] = other;
    }
  }
  std::set<int> distinctSupports(supportLabels.begin(), supportLabels.end());
  atoms.supportPods.assign(distinctSupports.begin(), distinctSupports.end());
  if (supportPositions.empty()) {
    atoms.gaps.push_back({-1, -1, -1, -1});
    std::fill(atoms.gapId.begin(), atoms.gapId.end(), 0);
    atoms.cyclicAtoms.push_back({false, 0});
    return atoms;
  }

  const int supportCount = (int)supportPositions.size();
  int exteriorSegment = -1;
  if (distinctSupports.size() == 1) {
    // A noninitial tripod has a preceding-level edge. It determines the
    // unbounded gap of a single parallel class; all other sectors are
    // bounded digons. An initial tripod never has only one support here.
    for (int i = 0; i < supportCount; i++) {
      const int next = (i + 1) % supportCount;
      bool containsEarlier = false;
      for (int pos = (supportPositions[i] + 1) % length;
           pos != supportPositions[next];
           pos = (pos + 1) % length) {
        const auto& incidence = rotation[pos];
        const auto& record = raw.edges[
            raw.edgeIndex.at(incidence.originalEdge)];
        const int other = record.endpointPod[1 - incidence.endpoint];
        containsEarlier |=
            tp.vertex2depth[other] == tp.vertex2depth[pod] - 1;
      }
      if (containsEarlier) {
        CHECK(exteriorSegment == -1,
              "preceding-level incidences of tripod %d split one support class",
              pod);
        exteriorSegment = i;
      }
    }
    CHECK(exteriorSegment >= 0 || tp.vertex2depth[pod] == 0,
          "single support class at tripod %d has no exterior gap", pod);
    if (exteriorSegment == -1) {
      // This affects only an initial tripod; no three-path order is needed.
      exteriorSegment = supportCount - 1;
    }
  }

  std::map<int, int> entryCount;
  vector<int> segmentGapId(supportCount, -1);
  for (int i = 0; i < supportCount; i++) {
    const int previous = (i + supportCount - 1) % supportCount;
    if (supportLabels[previous] != supportLabels[i]) {
      entryCount[supportLabels[i]]++;
    }
  }
  if (distinctSupports.size() > 1) {
    for (int supportPod : distinctSupports) {
      CHECK(entryCount[supportPod] == 1,
            "support class (%d,%d) is not cyclically consecutive",
            pod, supportPod);
    }
  }

  for (int i = 0; i < supportCount; i++) {
    const int next = (i + 1) % supportCount;
    const int left = supportLabels[i], right = supportLabels[next];
    const bool isGap = left != right || i == exteriorSegment;
    int id = -1;
    if (isGap) {
      id = (int)atoms.gaps.size();
      atoms.gaps.push_back({
          left, right, supportPositions[i], supportPositions[next]});
      segmentGapId[i] = id;
    }
    for (int pos = (supportPositions[i] + 1) % length;
         pos != supportPositions[next];
         pos = (pos + 1) % length) {
      CHECK(atoms.classPod[pos] == -1 && atoms.gapId[pos] == -1);
      if (isGap) {
        atoms.gapId[pos] = id;
      } else {
        atoms.classPod[pos] = left;
        const auto& incidence = rotation[pos];
        const auto& record = raw.edges[
            raw.edgeIndex.at(incidence.originalEdge)];
        const int other = record.endpointPod[1 - incidence.endpoint];
        CHECK(other == pod ||
              tp.vertex2depth[other] > tp.vertex2depth[pod],
              "support digon of (%d,%d) contains an earlier-level binding",
              pod, left);
      }
    }
  }
  for (int pos = 0; pos < length; pos++) {
    CHECK((atoms.classPod[pos] >= 0) != (atoms.gapId[pos] >= 0));
  }
  CHECK(!atoms.gaps.empty());
  int start = -1;
  if (distinctSupports.size() == 1) {
    start = (exteriorSegment + 1) % supportCount;
  } else {
    for (int i = 0; i < supportCount; i++) {
      const int previous = (i + supportCount - 1) % supportCount;
      if (supportLabels[previous] != supportLabels[i]) {
        start = i;
        break;
      }
    }
  }
  CHECK(start >= 0);
  for (int j = 0; j < supportCount; j++) {
    const int i = (start + j) % supportCount;
    const int previous = (i + supportCount - 1) % supportCount;
    if (j == 0 || supportLabels[previous] != supportLabels[i]) {
      atoms.cyclicAtoms.push_back({true, supportLabels[i]});
    }
    if (segmentGapId[i] >= 0) {
      atoms.cyclicAtoms.push_back({false, segmentGapId[i]});
    }
  }
  CHECK(atoms.cyclicAtoms.size() == 2 * distinctSupports.size(),
        "tripod %d support classes and gaps do not alternate", pod);
  return atoms;
}

// Where child components attach at each parent: one face per child, at most
// two ports of the parent per child, and binding edges of distinct children
// that do not interleave.
void verifyChildLocations(
    const LayeredHPartition& lhp,
    const RawTripodQuotient& raw,
    const TreePartition& tp,
    const vector<RawRotationAtoms>& atomsByPod) {
  const int podCount = (int)raw.clockwiseRotation.size();
  CHECK((int)atomsByPod.size() == podCount);
  map<array<int, 3>, int> threeParentOwner;
  for (int child = 0; child < tp.numBags; child++) {
    const auto& parents = tp.bag2parents[child];
    if (parents.size() != 3) continue;
    const array<int, 3> triple = {
        parents[0], parents[1], parents[2]};
    CHECK(threeParentOwner.emplace(triple, child).second,
          "two next-level components have the same three parents");
  }
  for (int pod = 0; pod < podCount; pod++) {
    const auto& rotation = raw.clockwiseRotation[pod];
    const auto& atoms = atomsByPod[pod];

    struct AdjacentChild {
      vector<int> positions;
      int touchedPaths{0};
    };
    map<int, AdjacentChild> children;
    map<pair<int, int>, vector<int>> transitionPositions;
    vector<int> multiParentBindings;
    for (int pos = 0; pos < (int)rotation.size(); pos++) {
      const auto& incidence = rotation[pos];
      const auto& record = raw.edges[
          raw.edgeIndex.at(incidence.originalEdge)];
      const int other = record.endpointPod[1 - incidence.endpoint];
      if (record.selectedFaceBase && other == pod) {
        const int a = std::min(
            record.endpointPath[0], record.endpointPath[1]);
        const int b = std::max(
            record.endpointPath[0], record.endpointPath[1]);
        CHECK(a != b);
        transitionPositions[{a, b}].push_back(pos);
      }
      if (tp.vertex2depth[other] == tp.vertex2depth[pod] + 1) {
        const int child = tp.vertex2bag[other];
        CHECK(child != tp.vertex2bag[pod]);
        auto& entry = children[child];
        entry.positions.push_back(pos);
        entry.touchedPaths |= 1 << incidence.pathId;
        if (tp.bag2parents[child].size() >= 2) {
          multiParentBindings.push_back(child);
        }
      }
    }
    set<int> distinctMulti(multiParentBindings.begin(),
                           multiParentBindings.end());
    if (distinctMulti.size() > 1) {
      map<int, int> cyclicEntries;
      for (int i = 0; i < (int)multiParentBindings.size(); i++) {
        const int previous = multiParentBindings[
            (i + (int)multiParentBindings.size() - 1) %
            multiParentBindings.size()];
        if (previous != multiParentBindings[i]) {
          cyclicEntries[multiParentBindings[i]]++;
        }
      }
      for (int child : distinctMulti) {
        CHECK(cyclicEntries[child] == 1,
              "multi-parent bindings of child component %d interleave "
              "at tripod %d", child, pod);
      }
    }
    if (lhp.pods[pod].numPaths() == 3 && pod >= 3) {
      CHECK(transitionPositions.size() == 3,
            "three-path tripod %d has no three selected-face transitions",
            pod);
    }
    for (const auto& [pair, positions] : transitionPositions) {
      CHECK(positions.size() == 2,
            "selected-face transition at tripod %d has %d incidences",
            pod, (int)positions.size());
      CHECK(atoms.classPod[positions[0]] == atoms.classPod[positions[1]] &&
            atoms.gapId[positions[0]] == atoms.gapId[positions[1]],
            "selected-face transition at tripod %d is split between atoms",
            pod);
    }

    for (const auto& [child, entry] : children) {
      CHECK(!entry.positions.empty());
      const auto& parents = tp.bag2parents[child];
      CHECK(std::find(parents.begin(), parents.end(), pod) != parents.end());
      const int first = entry.positions[0];
      const pair<int, int> firstAtom = {
          atoms.classPod[first], atoms.gapId[first]};
      for (int pos : entry.positions) {
        CHECK(make_pair(atoms.classPod[pos], atoms.gapId[pos]) == firstAtom,
              "bindings of child component %d occupy different raw atoms at tripod %d",
              child, pod);
      }
      CHECK(__builtin_popcount((unsigned)entry.touchedPaths) <= 2,
            "child component %d touches all three paths of tripod %d",
            child, pod);
      if (lhp.pods[pod].numPaths() == 3 &&
          __builtin_popcount((unsigned)entry.touchedPaths) == 2) {
        int touched[2], count = 0;
        for (int path = 0; path < 3; path++) {
          if (entry.touchedPaths & (1 << path)) touched[count++] = path;
        }
        CHECK(count == 2);
        const auto it = transitionPositions.find({touched[0], touched[1]});
        CHECK(it != transitionPositions.end(),
              "child component %d has no touched-path transition at tripod %d",
              child, pod);
        for (int pos : it->second) {
          CHECK(make_pair(atoms.classPod[pos], atoms.gapId[pos]) == firstAtom,
                "child component %d is separated from its transition at tripod %d",
                child, pod);
        }
      }

      if (parents.size() == 1) {
        CHECK(parents[0] == pod);
        continue;
      }
      if (parents.size() == 2) {
        const int otherParent = parents[0] == pod ? parents[1] : parents[0];
        CHECK(firstAtom.first == otherParent && firstAtom.second == -1,
              "two-parent child component %d is outside its support class at %d",
              child, pod);
      } else {
        CHECK(parents.size() == 3);
        CHECK(firstAtom.first == -1 && firstAtom.second >= 0,
              "three-parent child component %d is not in a bounded parent corner at %d",
              child, pod);
        const auto& gap = atoms.gaps[firstAtom.second];
        set<int> otherParents(parents.begin(), parents.end());
        otherParents.erase(pod);
        CHECK(otherParents == set<int>({gap.leftSupportPod, gap.rightSupportPod}),
              "three-parent child component %d is not between its two support classes at %d",
              child, pod);
      }
    }
  }
}

// Delete everything except the level edges of one level
// in the dual, then inspect the bounded face containing each child.
// This checks the whole connected child, not only its bindings at a parent.
void verifyBoundedChildRegions(
    const RawTripodQuotient& raw,
    const RawQuotientFaces& faces,
    const TreePartition& tp,
    const PlanarGraph& graph) {
  CHECK(graph.outerFace.length() == 3);
  set<Edge*> outerEdges(
      graph.outerFace.edges.begin(), graph.outerFace.edges.end());
  CHECK(outerEdges.size() == 3);
  int rawExterior = -1;
  for (int face = 0; face < (int)faces.faceDarts.size(); face++) {
    if (faces.faceDarts[face].size() != 3) continue;
    set<Edge*> boundary;
    for (int dart : faces.faceDarts[face]) {
      boundary.insert(faces.dartEdge[dart]);
    }
    if (boundary == outerEdges) {
      CHECK(rawExterior == -1,
            "raw quotient has two faces with the designated outer triangle");
      rawExterior = face;
    }
  }
  CHECK(rawExterior >= 0,
        "contracted quotient lost the designated outer face");

  const int edgeCount = (int)raw.edges.size();
  const int faceCount = (int)faces.faceDarts.size();
  vector<vector<int>> supportEdgesByLevel(tp.maxDepth + 1);
  vector<vector<int>> childrenAtLevel(tp.maxDepth + 1);
  vector<vector<int>> bindingEdgesByChild(tp.numBags);
  for (int child = 0; child < tp.numBags; child++) {
    childrenAtLevel[tp.bag2depth[child]].push_back(child);
  }
  for (int e = 0; e < edgeCount; e++) {
    const int u = raw.edges[e].endpointPod[0];
    const int v = raw.edges[e].endpointPod[1];
    const int du = tp.vertex2depth[u];
    const int dv = tp.vertex2depth[v];
    if (u != v && du == dv) {
      supportEdgesByLevel[du].push_back(e);
    } else if (std::abs(du - dv) == 1) {
      const int deeper = du > dv ? u : v;
      bindingEdgesByChild[tp.vertex2bag[deeper]].push_back(e);
    }
  }
  for (int level = 0; level < tp.maxDepth; level++) {
    bool hasMultipleParents = false;
    for (int child : childrenAtLevel[level + 1]) {
      if (tp.bag2parents[child].size() >= 2) {
        hasMultipleParents = true;
      }
    }
    if (!hasMultipleParents) continue;
    vector<bool> isSupport(edgeCount, false);
    for (int e : supportEdgesByLevel[level]) {
      isSupport[e] = true;
    }
    vector<int> parent(faceCount);
    vector<int> size(faceCount, 1);
    std::iota(parent.begin(), parent.end(), 0);
    auto findRegion = [&](int face) {
      while (parent[face] != face) {
        parent[face] = parent[parent[face]];
        face = parent[face];
      }
      return face;
    };
    auto joinRegions = [&](int a, int b) {
      a = findRegion(a);
      b = findRegion(b);
      if (a == b) return;
      if (size[a] < size[b]) std::swap(a, b);
      parent[b] = a;
      size[a] += size[b];
    };
    for (int e = 0; e < edgeCount; e++) {
      if (!isSupport[e]) {
        joinRegions(
            faces.faceOfDart[2 * e], faces.faceOfDart[2 * e + 1]);
      }
    }
    const int exterior = findRegion(rawExterior);
    vector<vector<int>> boundaryEdges(faceCount);
    for (int e : supportEdgesByLevel[level]) {
      boundaryEdges[findRegion(faces.faceOfDart[2 * e])].push_back(e);
      boundaryEdges[findRegion(faces.faceOfDart[2 * e + 1])].push_back(e);
    }
    map<int, set<int>> allowedOldPods;
    for (int child : childrenAtLevel[level + 1]) {
      const auto& parents = tp.bag2parents[child];
      if (parents.size() < 2) continue;
      CHECK(parents.size() <= 3 && !bindingEdgesByChild[child].empty());
      int region = -1;
      for (int e : bindingEdgesByChild[child]) {
        CHECK(!isSupport[e]);
        const int first = findRegion(faces.faceOfDart[2 * e]);
        const int second = findRegion(faces.faceOfDart[2 * e + 1]);
        CHECK(first == second,
              "binding edge to child %d separates two support regions",
              child);
        if (region == -1) region = first;
        CHECK(region == first,
              "child component %d spans two support regions", child);
      }
      CHECK(region != exterior,
            "multi-parent child component %d lies outside its parent supports",
            child);
      for (int pod : tp.bags[child]) {
        for (const auto& incidence : raw.clockwiseRotation[pod]) {
          const int e = raw.edgeIndex.at(incidence.originalEdge);
          CHECK(!isSupport[e]);
          const int dart = 2 * e + incidence.endpoint;
          CHECK(findRegion(faces.faceOfDart[dart]) == region,
                "pod %d of child component %d leaves its bounded support region",
                pod, child);
        }
      }
      const vector<int>& boundary = boundaryEdges[region];
      CHECK(boundary.size() == parents.size(),
            "child component %d has a support boundary of length %d, "
            "expected %d",
            child, (int)boundary.size(), (int)parents.size());
      set<int> distinctCopies(boundary.begin(), boundary.end());
      CHECK(distinctCopies.size() == boundary.size(),
            "child component %d is bounded twice by one support copy",
            child);
      set<EdgeTy> expectedSides;
      if (parents.size() == 2) {
        expectedSides.insert(make_edge(parents[0], parents[1]));
        CHECK(boundary.size() == 2);
      } else {
        expectedSides.insert(make_edge(parents[0], parents[1]));
        expectedSides.insert(make_edge(parents[0], parents[2]));
        expectedSides.insert(make_edge(parents[1], parents[2]));
        CHECK(boundary.size() == 3);
      }
      for (int e : boundary) {
        const EdgeTy pair = make_edge(
            raw.edges[e].endpointPod[0],
            raw.edges[e].endpointPod[1]);
        CHECK(expectedSides.count(pair),
              "child component %d is bounded by a non-parent support",
              child);
        if (parents.size() == 3) {
          CHECK(expectedSides.erase(pair) == 1,
                "three-parent child component %d uses one side twice",
                child);
        }
      }
      if (parents.size() == 3) {
        CHECK(expectedSides.empty());
      }
      const set<int> parentSet(parents.begin(), parents.end());
      const auto [it, inserted] =
          allowedOldPods.emplace(region, parentSet);
      CHECK(inserted || it->second == parentSet,
            "one bounded support region contains children with different parents");
    }
    for (int dart = 0; dart < 2 * edgeCount; dart++) {
      const int region = findRegion(faces.faceOfDart[dart]);
      auto it = allowedOldPods.find(region);
      if (it == allowedOldPods.end()) continue;
      const int pod = faces.dartPod[dart];
      if (tp.vertex2depth[pod] <= level) {
        CHECK(it->second.count(pod),
              "bounded child region contains unrelated earlier-level tripod %d",
              pod);
      }
    }
  }
}

struct ParentFaceCorner {
  int clockwiseStart;
  int clockwiseEnd;
};

struct ParentFace {
  int rawFaceId;
  int child{-1};
  set<int> boundaryPods;
  map<int, vector<ParentFaceCorner>> cornersByPod;
};

// For each level i, recover the faces of the quotient restricted to levels
// 0..i by deleting every other edge in the dual. This includes loops and
// repeated dart occurrences; boundary pods are a set, not a count of boundary
// darts. Check that every bounded face of a level component has at most three
// distinct boundary tripods, holds at most one child component, and that the
// parents of a child are exactly the boundary tripods of its face.
class ParentFaceCollector {
 public:
  ParentFaceCollector(
      const RawTripodQuotient& raw,
      const RawQuotientFaces& faces,
      const TreePartition& tp,
      const PlanarGraph& graph)
      : raw(raw), faces(faces), tp(tp), graph(graph),
        podCount((int)raw.clockwiseRotation.size()),
        edgeCount((int)raw.edges.size()),
        faceCount((int)faces.faceDarts.size()),
        parentFaces(tp.numBags), childrenAtLevel(tp.maxDepth + 1),
        bindingsByChild(tp.numBags), dual(0) {}

  vector<vector<ParentFace>> build() {
    findExterior();
    collectChildren();
    for (int level = 0; level <= tp.maxDepth; level++) {
      nextChildren = level < tp.maxDepth ? childrenAtLevel[level + 1] : vector<int>();
      mergeFacesAboveLevel(level);
      recordCorners(level);
      locateDeeperPods(level);
      placeChildren(level);
      collectComponentFaces(level);
      verifyComponentFaceCounts(level);
    }
    return std::move(parentFaces);
  }

 private:
  struct Dsu {
    vector<int> parent;
    vector<int> size;

    explicit Dsu(int count) : parent(count), size(count, 1) {
      std::iota(parent.begin(), parent.end(), 0);
    }
    int find(int item) {
      while (parent[item] != item) {
        parent[item] = parent[parent[item]];
        item = parent[item];
      }
      return item;
    }
    void join(int a, int b) {
      a = find(a);
      b = find(b);
      if (a == b) return;
      if (size[a] < size[b]) std::swap(a, b);
      parent[b] = a;
      size[a] += size[b];
    }
  };

  // The face of the quotient bounded by the initial triangle.
  void findExterior() {
    CHECK(graph.outerFace.length() == 3);
    const set<Edge*> outerEdges(
        graph.outerFace.edges.begin(), graph.outerFace.edges.end());
    CHECK(outerEdges.size() == 3);
    rawExterior = -1;
    for (int face = 0; face < faceCount; face++) {
      const auto& darts = faces.faceDarts[face];
      CHECK(!darts.empty() && darts.size() <= 3,
            "raw quotient face %d has facial-walk length %d, expected at most 3",
            face, (int)darts.size());
      if (darts.size() != 3) continue;
      set<Edge*> edges;
      for (int dart : darts) edges.insert(faces.dartEdge[dart]);
      if (edges == outerEdges) {
        CHECK(rawExterior == -1,
              "raw quotient has two faces with the designated outer triangle");
        rawExterior = face;
      }
    }
    CHECK(rawExterior >= 0,
          "contracted quotient lost the designated outer face");
  }

  // The child components of each level and their binding edges.
  void collectChildren() {
    for (int child = 0; child < tp.numBags; child++) {
      childrenAtLevel[tp.bag2depth[child]].push_back(child);
    }
    for (int e = 0; e < edgeCount; e++) {
      const int u = raw.edges[e].endpointPod[0];
      const int v = raw.edges[e].endpointPod[1];
      const int du = tp.vertex2depth[u];
      const int dv = tp.vertex2depth[v];
      CHECK(std::abs(du - dv) <= 1,
            "raw quotient edge %d skips a level", e);
      if (du != dv) {
        const int deeper = du > dv ? u : v;
        bindingsByChild[tp.vertex2bag[deeper]].push_back(e);
      }
    }
  }

  // The faces of the quotient restricted to levels 0..level, as unions of
  // faces of the quotient.
  void mergeFacesAboveLevel(int level) {
    Dsu upToLevel(podCount);
    dual = Dsu(faceCount);
    retained.assign(edgeCount, false);
    for (int e = 0; e < edgeCount; e++) {
      const int u = raw.edges[e].endpointPod[0];
      const int v = raw.edges[e].endpointPod[1];
      if (tp.vertex2depth[u] <= level &&
          tp.vertex2depth[v] <= level) {
        retained[e] = true;
        upToLevel.join(u, v);
      } else {
        dual.join(faces.faceOfDart[2 * e],
                  faces.faceOfDart[2 * e + 1]);
      }
    }
    const int upToLevelRoot = upToLevel.find(0);
    for (int pod = 0; pod < podCount; pod++) {
      if (tp.vertex2depth[pod] <= level) {
        CHECK(upToLevel.find(pod) == upToLevelRoot,
              "the quotient up to level %d is disconnected at pod %d",
              level, pod);
      }
    }
  }

  // Boundary tripods and corners of every such face.
  void recordCorners(int level) {
    exterior = dual.find(rawExterior);
    boundaryPods.assign(faceCount, {});
    cornersByRegion.assign(faceCount, {});
    for (int e = 0; e < edgeCount; e++) {
      if (!retained[e]) continue;
      // Count each dart side separately. A bridge can put both sides in the
      // same face, and a loop can contribute the same pod more than once.
      for (int dart : {2 * e, 2 * e + 1}) {
        boundaryPods[dual.find(faces.faceOfDart[dart])].insert(
            faces.dartPod[dart]);
      }
    }
    for (int pod = 0; pod < podCount; pod++) {
      if (tp.vertex2depth[pod] > level) continue;
      const auto& rotation = raw.clockwiseRotation[pod];
      vector<int> retainedPositions;
      for (int pos = 0; pos < (int)rotation.size(); pos++) {
        const int e = raw.edgeIndex.at(rotation[pos].originalEdge);
        if (retained[e]) retainedPositions.push_back(pos);
      }
      CHECK(!retainedPositions.empty(),
            "the quotient up to the level has no incidence at pod %d at level %d",
            pod, level);
      for (int i = 0; i < (int)retainedPositions.size(); i++) {
        const int start = retainedPositions[i];
        const int end = retainedPositions[
            (i + 1) % retainedPositions.size()];
        const auto& startIncidence = rotation[start];
        const auto& endIncidence = rotation[end];
        const int startDart =
            2 * raw.edgeIndex.at(startIncidence.originalEdge) +
            startIncidence.endpoint;
        const int endDart =
            2 * raw.edgeIndex.at(endIncidence.originalEdge) +
            endIncidence.endpoint;
        const int region = dual.find(
            faces.faceOfDart[faces.twin[startDart]]);
        CHECK(region == dual.find(faces.faceOfDart[endDart]),
              "retained darts around pod %d bound different faces of the quotient up to the level "
              "at level %d", pod, level);
        cornersByRegion[region][pod].push_back({start, end});
      }
    }
  }

  // Each tripod of a deeper level lies inside one such face.
  void locateDeeperPods(int level) {
    containsDeeperPod.assign(faceCount, false);
    for (int pod = 0; pod < podCount; pod++) {
      if (tp.vertex2depth[pod] <= level) continue;
      CHECK(!raw.clockwiseRotation[pod].empty(),
            "deeper pod %d has no raw incidence", pod);
      int region = -1;
      for (const auto& incidence : raw.clockwiseRotation[pod]) {
        const int e = raw.edgeIndex.at(incidence.originalEdge);
        const int dart = 2 * e + incidence.endpoint;
        const int current = dual.find(faces.faceOfDart[dart]);
        if (region == -1) region = current;
        CHECK(region == current,
              "deeper pod %d spans faces of the quotient up to the level at level %d",
              pod, level);
      }
      containsDeeperPod[region] = true;
    }
  }

  // Each child component lies inside one bounded face whose distinct
  // boundary tripods are its parents, and no two children share a face.
  void placeChildren(int level) {
    childInFace.assign(faceCount, -1);
    for (int child : nextChildren) {
      const auto& parents = tp.bag2parents[child];
      CHECK(!parents.empty() && !bindingsByChild[child].empty(),
            "child component %d has no binding at level %d",
            child, level);
      int region = -1;
      for (int e : bindingsByChild[child]) {
        const int u = raw.edges[e].endpointPod[0];
        const int v = raw.edges[e].endpointPod[1];
        CHECK(std::min(tp.vertex2depth[u], tp.vertex2depth[v]) == level &&
              std::max(tp.vertex2depth[u], tp.vertex2depth[v]) == level + 1,
              "child component %d has a binding at the wrong level",
              child);
        for (int dart : {2 * e, 2 * e + 1}) {
          const int current = dual.find(faces.faceOfDart[dart]);
          if (region == -1) region = current;
          CHECK(region == current,
                "bindings of child component %d span faces of the quotient up to the level "
                "at level %d", child, level);
        }
      }
      for (int pod : tp.bags[child]) {
        CHECK(tp.vertex2depth[pod] == level + 1,
              "child component %d contains a pod at the wrong level",
              child);
        CHECK(!raw.clockwiseRotation[pod].empty(),
              "child pod %d has no raw incidence", pod);
        for (const auto& incidence : raw.clockwiseRotation[pod]) {
          const int e = raw.edgeIndex.at(incidence.originalEdge);
          const int dart = 2 * e + incidence.endpoint;
          CHECK(dual.find(faces.faceOfDart[dart]) == region,
                "pod %d of child component %d leaves its face of the quotient up to the level "
                "at level %d", pod, child, level);
        }
      }
      CHECK(region != exterior,
            "child component %d occupies the outer face of the quotient up to the level "
            "at level %d", child, level);
      const set<int> parentSet(parents.begin(), parents.end());
      CHECK(parentSet.size() == parents.size());
      CHECK(boundaryPods[region] == parentSet,
            "face of child component %d at level %d has %d "
            "distinct boundary pods, expected its %d parents",
            child, level, (int)boundaryPods[region].size(),
            (int)parentSet.size());
      CHECK(childInFace[region] == -1,
            "child components %d and %d share a face of the quotient up to the level at level %d",
            childInFace[region], child, level);
      childInFace[region] = child;
    }
    for (int face = 0; face < faceCount; face++) {
      if (dual.find(face) != face || !containsDeeperPod[face]) continue;
      CHECK(face != exterior,
            "the outer face of the quotient up to the level contains a deeper pod at level %d", level);
      CHECK(childInFace[face] >= 0,
            "face %d of the quotient up to the level contains deeper pods but no next-level "
            "child at level %d", face, level);
    }
  }

  // The bounded faces of each level component, with their corners.
  void collectComponentFaces(int level) {
    for (int face = 0; face < faceCount; face++) {
      if (dual.find(face) != face || face == exterior ||
          boundaryPods[face].empty()) continue;
      const int firstPod = *boundaryPods[face].begin();
      if (tp.vertex2depth[firstPod] != level) continue;
      const int bag = tp.vertex2bag[firstPod];
      bool belongsToBag = true;
      for (int pod : boundaryPods[face]) {
        belongsToBag &= tp.vertex2depth[pod] == level &&
                        tp.vertex2bag[pod] == bag;
      }
      if (!belongsToBag) continue;
      CHECK(boundaryPods[face].size() <= 3,
            "bounded parent face %d of component %d has %d "
            "distinct boundary pods", face, bag,
            (int)boundaryPods[face].size());
      CHECK(cornersByRegion[face].size() == boundaryPods[face].size(),
            "bounded parent face %d has a missing boundary corner", face);
      ParentFace parentFace;
      parentFace.rawFaceId = face;
      parentFace.child = childInFace[face];
      parentFace.boundaryPods = std::move(boundaryPods[face]);
      parentFace.cornersByPod = std::move(cornersByRegion[face]);
      for (int pod : parentFace.boundaryPods) {
        const auto& corners = parentFace.cornersByPod.at(pod);
        CHECK(!corners.empty());
        const auto& rotation = raw.clockwiseRotation[pod];
        const int length = (int)rotation.size();
        for (const ParentFaceCorner& corner : corners) {
          int bindingCount = 0;
          for (int step = 1; step < length; step++) {
            const int pos = (corner.clockwiseStart + step) % length;
            if (pos == corner.clockwiseEnd) break;
            const auto& incidence = rotation[pos];
            const auto& record =
                raw.edges[raw.edgeIndex.at(incidence.originalEdge)];
            const int other = record.endpointPod[1 - incidence.endpoint];
            CHECK(tp.vertex2depth[other] == level + 1,
                  "nonretained dart inside parent face %d has wrong level",
                  parentFace.rawFaceId);
            CHECK(tp.vertex2bag[other] == parentFace.child,
                  "corner of parent face %d at pod %d binds child %d "
                  "instead of child %d",
                  parentFace.rawFaceId, pod, tp.vertex2bag[other],
                  parentFace.child);
            bindingCount++;
          }
          CHECK(parentFace.child < 0 || bindingCount > 0,
                "occupied parent face %d has a corner at pod %d "
                "without a binding to child %d",
                parentFace.rawFaceId, pod, parentFace.child);
        }
      }
      parentFaces[bag].push_back(std::move(parentFace));
    }
  }

  // Euler's formula for each level component, and one face per child.
  void verifyComponentFaceCounts(int level) {
    for (int bag = 0; bag < tp.numBags; bag++) {
      if (tp.bag2depth[bag] != level) continue;
      int levelEdgeCount = 0;
      for (int e = 0; e < edgeCount; e++) {
        const int u = raw.edges[e].endpointPod[0];
        const int v = raw.edges[e].endpointPod[1];
        levelEdgeCount += tp.vertex2bag[u] == bag &&
                          tp.vertex2bag[v] == bag;
      }
      CHECK((int)parentFaces[bag].size() ==
                levelEdgeCount - (int)tp.bags[bag].size() + 1,
            "component %d has %d recovered bounded faces, expected %d",
            bag, (int)parentFaces[bag].size(),
            levelEdgeCount - (int)tp.bags[bag].size() + 1);
      set<int> occupied;
      for (const ParentFace& face : parentFaces[bag]) {
        if (face.child >= 0) {
          CHECK(occupied.insert(face.child).second,
                "child %d occupies two bounded faces of component %d",
                face.child, bag);
        }
      }
      for (int child : nextChildren) {
        if (tp.vertex2bag[tp.bag2parents[child][0]] == bag) {
          CHECK(occupied.count(child),
                "child %d has no bounded parent face of component %d",
                child, bag);
        }
      }
    }
  }

  const RawTripodQuotient& raw;
  const RawQuotientFaces& faces;
  const TreePartition& tp;
  const PlanarGraph& graph;
  const int podCount, edgeCount, faceCount;
  vector<vector<ParentFace>> parentFaces;
  int rawExterior{-1};
  vector<vector<int>> childrenAtLevel;
  vector<vector<int>> bindingsByChild;
  // State for the current level.
  vector<int> nextChildren;
  Dsu dual;
  vector<bool> retained;
  int exterior{-1};
  vector<set<int>> boundaryPods;
  vector<map<int, vector<ParentFaceCorner>>> cornersByRegion;
  vector<bool> containsDeeperPod;
  vector<int> childInFace;
};

vector<vector<ParentFace>> verifyParentFaceChildBijection(
    const RawTripodQuotient& raw,
    const RawQuotientFaces& faces,
    const TreePartition& tp,
    const PlanarGraph& graph) {
  return ParentFaceCollector(raw, faces, tp, graph).build();
}

// The auxiliary simple outerplane graph K of one level component K̂.
// Vertices 0..numReal-1 are its tripods in podIds order; the remaining
// vertices complete triangles containing the faces of K̂. At a real vertex,
// one cyclic clockwise list of slots merges its raw incidences with the edges
// of K that are not raw edges. A support edge of K sits at the slot of its
// retained raw copy.
struct LevelK {
  enum EdgeKind { kSupport, kAugmentation, kAuxiliary };
  struct KEdge {
    int end[2];
    EdgeKind kind;
    int rawEdge;  // retained copy of a support edge, otherwise -1
  };
  struct Slot {
    int rawPos;  // raw incidence at this slot, or -1
    int kEdge;   // edge of K at this slot, or -1
  };

  vector<int> podIds;
  int numReal{0};
  vector<double> x;
  vector<int> y;
  vector<KEdge> edges;
  map<EdgeTy, vector<int>> supportCopies;  // local pair -> raw edges
  map<EdgeTy, int> supportEdge;            // local pair -> edge of K
  vector<vector<int>> classOf;             // real vertex: raw pos -> support pod or -1
  vector<vector<Slot>> slots;              // real vertices
  vector<vector<int>> auxRotation;         // auxiliary vertices, by id - numReal
  int startEdge{-1};
  int outerDart{-1};
  int designatedTriangles{0};
  int wrapReused{0};
  int wrapAdded{0};

  // Faces, recomputed by computeFaces(). Dart 2e goes from end[0] to end[1].
  vector<int> faceOfDart;
  vector<vector<int>> faceDarts;
  int outerFace{-1};

  int numVertices() const { return (int)y.size(); }
  bool isAux(int v) const { return v >= numReal; }
  int other(int e, int v) const {
    CHECK(edges[e].end[0] == v || edges[e].end[1] == v);
    return edges[e].end[0] == v ? edges[e].end[1] : edges[e].end[0];
  }
  int dart(int e, int from) const {
    CHECK(edges[e].end[0] == from || edges[e].end[1] == from);
    return 2 * e + (edges[e].end[0] == from ? 0 : 1);
  }
  int head(int d) const { return edges[d / 2].end[1 - d % 2]; }
  int span(int e) const {
    return std::abs(y[edges[e].end[0]] - y[edges[e].end[1]]);
  }

  vector<int> rotation(int v) const {
    if (isAux(v)) return auxRotation[v - numReal];
    vector<int> result;
    for (const Slot& slot : slots[v]) {
      if (slot.kEdge >= 0) result.push_back(slot.kEdge);
    }
    return result;
  }

  // The sector at v from edge f clockwise to the next edge of K.
  int sectorFace(int v, int f) const {
    return faceOfDart[dart(f, other(f, v))];
  }

  int slotOfEdge(int u, int e) const {
    CHECK(!isAux(u));
    int found = -1;
    for (int i = 0; i < (int)slots[u].size(); i++) {
      if (slots[u][i].kEdge == e) {
        CHECK(found == -1);
        found = i;
      }
    }
    CHECK(found >= 0, "edge %d of K has no slot at vertex %d", e, u);
    return found;
  }

  int slotOfRaw(int u, int pos) const {
    for (int i = 0; i < (int)slots[u].size(); i++) {
      if (slots[u][i].rawPos == pos) return i;
    }
    CHECK(false, "raw incidence %d has no slot", pos);
    return -1;
  }

  // Slots of the copies of a support edge and everything between them
  // (one cyclic run); a single slot for any other edge of K.
  pair<int, int> classSlots(int u, int e) const {
    const int at = slotOfEdge(u, e);
    if (edges[e].kind != kSupport) return {at, at};
    const int pod = podIds[other(e, u)];
    const int size = (int)slots[u].size();
    auto inClass = [&](int i) {
      const Slot& slot = slots[u][(i + size) % size];
      return slot.rawPos >= 0 && classOf[u][slot.rawPos] == pod;
    };
    int first = at, last = at, steps = 0;
    while (inClass(first - 1)) {
      first = (first - 1 + size) % size;
      CHECK(++steps < size, "support class fills the rotation at %d", u);
    }
    while (inClass(last + 1)) {
      last = (last + 1) % size;
      CHECK(++steps < size, "support class fills the rotation at %d", u);
    }
    return {first, last};
  }

  // Is the designated side of the edge u-w (above a span-one edge, right of a
  // span-two edge) the clockwise side of the ray from u to w?
  bool designatedClockwise(int u, int w) const {
    const double dx = x[w] - x[u];
    const int dy = y[w] - y[u];
    CHECK(dx != 0 && (std::abs(dy) == 1 || std::abs(dy) == 2),
          "edge (%d,%d) of K has no span-one/span-two direction", u, w);
    return std::abs(dy) == 1 ? dx < 0 : dy > 0;
  }

  void insertSlot(int u, int index, int e) {
    CHECK(0 <= index && index <= (int)slots[u].size());
    slots[u].insert(slots[u].begin() + index, Slot{-1, e});
  }

  // Insert edge e of K at vertex v next to edge f, on the side of the outer
  // face (just beyond the copies of f on that side).
  void insertNextToOuterSide(int v, int f, int e) {
    const bool clockwise = sectorFace(v, f) == outerFace;
    if (isAux(v)) {
      auto& rot = auxRotation[v - numReal];
      const int at = (int)(std::find(rot.begin(), rot.end(), f) - rot.begin());
      CHECK(at < (int)rot.size());
      rot.insert(rot.begin() + (clockwise ? at + 1 : at), e);
      return;
    }
    const auto [first, last] = classSlots(v, f);
    insertSlot(v, clockwise ? last + 1 : first, e);
  }

  void computeFaces() {
    const int n = numVertices();
    vector<vector<int>> rot(n);
    vector<unordered_map<int, int>> pos(n);
    for (int v = 0; v < n; v++) {
      rot[v] = rotation(v);
      for (int i = 0; i < (int)rot[v].size(); i++) {
        CHECK(pos[v].emplace(rot[v][i], i).second,
              "edge %d of K repeats in the rotation at %d", rot[v][i], v);
      }
    }
    for (int e = 0; e < (int)edges.size(); e++) {
      CHECK(pos[edges[e].end[0]].count(e) && pos[edges[e].end[1]].count(e),
            "edge %d of K is missing from an endpoint rotation", e);
    }
    faceOfDart.assign(2 * edges.size(), -1);
    faceDarts.clear();
    for (int start = 0; start < 2 * (int)edges.size(); start++) {
      if (faceOfDart[start] >= 0) continue;
      const int face = (int)faceDarts.size();
      faceDarts.emplace_back();
      int d = start;
      do {
        CHECK(faceOfDart[d] == -1, "face walk of K closes on a used dart");
        faceOfDart[d] = face;
        faceDarts[face].push_back(d);
        const int h = head(d);
        const int i = pos[h].at(d / 2);
        const int f = rot[h][(i + 1) % rot[h].size()];
        d = dart(f, h);
      } while (d != start);
    }
    CHECK((int)faceDarts.size() == (int)edges.size() - n + 2,
          "K violates Euler's formula: V=%d E=%d F=%d",
          n, (int)edges.size(), (int)faceDarts.size());
    outerFace = faceOfDart[outerDart];
  }

  vector<int> faceVertices(int face) const {
    vector<int> result;
    for (int d : faceDarts[face]) result.push_back(edges[d / 2].end[d % 2]);
    return result;
  }

  // The K-face containing a raw corner (clockwise from s to t) at real u.
  int cornerFace(int u, int s, int t) const {
    const int size = (int)slots[u].size();
    const int from = slotOfRaw(u, s);
    const int to = slotOfRaw(u, t);
    for (int i = (from + 1) % size; i != to; i = (i + 1) % size) {
      CHECK(slots[u][i].kEdge < 0,
            "an edge of K splits a face corner of K̂ at tripod %d", podIds[u]);
    }
    for (int step = 0; step < size; step++) {
      const int i = (from - step + size) % size;
      if (slots[u][i].kEdge >= 0) return sectorFace(u, slots[u][i].kEdge);
    }
    CHECK(false, "no edge of K at vertex %d", u);
    return -1;
  }
};

// Builds the graph K of one level component K̂, before its monogons are
// wrapped: augment the simple graph of K̂ to a maximal outerplanar graph,
// draw it on tracks from a span-one outer edge, keep one copy of every
// parallel class, and add the auxiliary triangle on every designated side
// that is the outer face.
class LevelKBuilder {
 public:
  LevelKBuilder(
      const RawTripodQuotient& raw,
      const TreePartition& tp,
      int bagId,
      const vector<int>& rawSupportEdges,
      const vector<int>& initialOuterPodCycle,
      const vector<RawRotationAtoms>& atomsByPod, int verbose)
      : raw(raw), tp(tp), bagId(bagId), rawSupportEdges(rawSupportEdges),
        initialOuterPodCycle(initialOuterPodCycle), atomsByPod(atomsByPod), verbose(verbose) {
    K.podIds = tp.bags[bagId];
    count = (int)K.podIds.size();
    K.numReal = count;
    CHECK(count >= 1);
  }

  LevelK build() {
    buildSimpleGraph();
    chooseOuterFace();
    augmentToMaximalOuterplanar();
    drawOnTracks();
    buildSlots();
    addDesignatedSideTriangles();
    return std::move(K);
  }

 private:
  // The simple graph of K̂, with the rotations of the raw contraction.
  void buildSimpleGraph() {
    for (int i = 0; i < count; i++) {
      CHECK(local.emplace(K.podIds[i], i).second);
      g.newVertex();
    }

    vector<int> simpleDegree(count, 0);
    for (int rawId : rawSupportEdges) {
      CHECK(0 <= rawId && rawId < (int)raw.edges.size());
      const auto& record = raw.edges[rawId];
      const int u = record.endpointPod[0];
      const int v = record.endpointPod[1];
      CHECK(u != v && local.count(u) && local.count(v));
      CHECK(tp.vertex2bag[u] == bagId && tp.vertex2bag[v] == bagId);
      const EdgeTy pair = make_edge(local.at(u), local.at(v));
      K.supportCopies[pair].push_back(rawId);
      if (!support.count(pair)) {
        support[pair] = g.newEdge(g.vertices[pair.first], g.vertices[pair.second]);
        simpleDegree[pair.first]++;
        simpleDegree[pair.second]++;
      }
    }
    if (count >= 2) {
      CHECK(!support.empty());
    }
    for (int i = 0; i < count; i++) {
      const int pod = K.podIds[i];
      vector<int> rawNeighborSequence;
      vector<Edge*> simpleRotation;
      set<int> seenNeighbors;
      for (const auto& incidence : raw.clockwiseRotation[pod]) {
        const auto& record = raw.edges[raw.edgeIndex.at(incidence.originalEdge)];
        const int other = record.endpointPod[1 - incidence.endpoint];
        if (other == pod || !local.count(other)) continue;
        const EdgeTy pair = make_edge(i, local.at(other));
        CHECK(support.count(pair));
        rawNeighborSequence.push_back(other);
        if (seenNeighbors.insert(other).second) {
          simpleRotation.push_back(support.at(pair));
        }
      }
      CHECK(simpleRotation.size() == (size_t)simpleDegree[i],
            "simple support degree differs from contracted rotation at tripod %d", pod);
      if (rawNeighborSequence.size() > 1 && seenNeighbors.size() > 1) {
        map<int, int> entering;
        for (int j = 0; j < (int)rawNeighborSequence.size(); j++) {
          const int previous = rawNeighborSequence[
              (j + (int)rawNeighborSequence.size() - 1) % rawNeighborSequence.size()];
          if (previous != rawNeighborSequence[j]) entering[rawNeighborSequence[j]]++;
        }
        for (int neighbor : seenNeighbors) {
          CHECK(entering[neighbor] == 1,
                "support copies of (%d,%d) interleave another support at tripod %d",
                pod, neighbor, pod);
        }
      }
      g.vertices[i]->edges = simpleRotation;
    }
  }

  // The outer face of the simple graph (a level component is outerplane).
  void chooseOuterFace() {
    if (count < 3) return;
    {
      const auto simpleEdges = g.extractEdges();
      unordered_map<Edge*, int> simpleEdgeId;
      for (int e = 0; e < (int)simpleEdges.size(); e++) simpleEdgeId[simpleEdges[e]] = e;
      vector<bool> seenDart(2 * simpleEdges.size(), false);
      vector<Face> faces;
      for (Edge* edge : simpleEdges) {
        for (Vertex* start : {edge->source, edge->target}) {
          if (seenDart[2 * simpleEdgeId.at(edge) + (edge->source == start ? 0 : 1)]) continue;
          Face face = g.extractRightFace(start, edge);
          for (int i = 0; i < face.length(); i++) {
            Edge* side = face.edges[i];
            const int sideDart = 2 * simpleEdgeId.at(side) +
                (side->source == face.vertices[i] ? 0 : 1);
            CHECK(!seenDart[sideDart], "support face walk repeats an oriented edge side");
            seenDart[sideDart] = true;
          }
          faces.push_back(face);
        }
      }
      CHECK((int)faces.size() == (int)support.size() - count + 2,
            "level component %d violates Euler's formula", bagId);
      vector<Face> possibleOuterFaces;
      for (const Face& face : faces) {
        vector<bool> onFace(count, false);
        for (Vertex* v : face.vertices) onFace[v->index] = true;
        if (std::all_of(onFace.begin(), onFace.end(), [](bool yes) { return yes; })) {
          possibleOuterFaces.push_back(face);
        }
      }
      CHECK(possibleOuterFaces.size() == 1 ||
            (count == 3 && support.size() == 3 && possibleOuterFaces.size() == 2),
            "level component %d has no unique face incident with every vertex", bagId);
      for (const Face& face : faces) {
        bool possibleOuter = false;
        for (const Face& candidate : possibleOuterFaces) possibleOuter |= candidate == face;
        CHECK(possibleOuter || face.length() == 3,
              "level component %d has a bounded nontriangular face", bagId);
      }
      for (const auto& block : biconnectedComponents(count, g.extractEdgesId())) {
        const vector<int> blockVertices = vertices_of(block);
        if (blockVertices.size() >= 3) {
          CHECK(block.size() == 2 * blockVertices.size() - 3,
                "level component %d has a nonmaximal outerplane block", bagId);
        }
      }
      if (possibleOuterFaces.size() == 1) {
        g.outerFace = possibleOuterFaces[0];
      } else {
        int selected = -1;
        for (int faceId = 0; faceId < 2; faceId++) {
          const Face& face = possibleOuterFaces[faceId];
          bool outer = false;
          if (tp.bag2depth[bagId] == 0) {
            CHECK(initialOuterPodCycle.size() == 3);
            for (int shift = 0; shift < 3; shift++) {
              bool agrees = true;
              for (int i = 0; i < 3; i++) {
                agrees &= K.podIds[face.vertices[(shift + i) % 3]->index] ==
                          initialOuterPodCycle[i];
              }
              outer |= agrees;
            }
          } else {
            // Each vertex of a positive-level triangle has a preceding-level
            // edge, which descends to the initial boundary; it lies on the
            // outer side of the triangle.
            int previousLevelCorners = 0;
            for (int i = 0; i < 3; i++) {
              const int pod = K.podIds[face.vertices[i]->index];
              const int outPod = K.podIds[face.edges[i]->other(face.vertices[i])->index];
              const int inPod = K.podIds[face.edges[(i + 2) % 3]->other(face.vertices[i])->index];
              const auto& rotation = raw.clockwiseRotation[pod];
              int outPos = -1, inPos = -1;
              for (int pos = 0; pos < (int)rotation.size(); pos++) {
                const auto& record = raw.edges[raw.edgeIndex.at(rotation[pos].originalEdge)];
                const int other = record.endpointPod[1 - rotation[pos].endpoint];
                if (other == outPod && outPos == -1) outPos = pos;
                if (other == inPod && inPos == -1) inPos = pos;
              }
              CHECK(outPos >= 0 && inPos >= 0 && outPos != inPos);
              bool seesPreviousLevel = false;
              for (int pos = (outPos + 1) % rotation.size(); pos != inPos;
                   pos = (pos + 1) % rotation.size()) {
                const auto& record = raw.edges[raw.edgeIndex.at(rotation[pos].originalEdge)];
                const int other = record.endpointPod[1 - rotation[pos].endpoint];
                seesPreviousLevel |= tp.vertex2depth[other] == tp.bag2depth[bagId] - 1;
              }
              previousLevelCorners += seesPreviousLevel;
            }
            CHECK(previousLevelCorners == 0 || previousLevelCorners == 3,
                  "triangle level component %d has a mixed preceding-level side", bagId);
            outer = previousLevelCorners == 3;
          }
          if (outer) {
            CHECK(selected == -1, "both sides of triangle component %d look outer", bagId);
            selected = faceId;
          }
        }
        CHECK(selected >= 0, "cannot identify the exterior face of component %d", bagId);
        g.outerFace = possibleOuterFaces[selected];
      }
    }
  }

  // A single vertex gets two auxiliary vertices and a single edge one.
  void augmentToMaximalOuterplanar() {
    if (count == 1) {
      Vertex* u = g.vertices[0];
      Vertex* a = g.newVertex();
      Vertex* b = g.newVertex();
      Edge* ua = g.newEdge(u, a);
      Edge* ub = g.newEdge(u, b);
      Edge* ab = g.newEdge(a, b);
      u->edges = {ua, ub};
      a->edges = {ab, ua};
      b->edges = {ub, ab};
      g.outerFace = g.extractRightFace(u, ua);
    } else if (count == 2) {
      CHECK(support.size() == 1);
      Vertex* u = g.vertices[0];
      Vertex* v = g.vertices[1];
      Edge* uv = support.begin()->second;
      Vertex* a = g.newVertex();
      Edge* ua = g.newEdge(u, a);
      Edge* va = g.newEdge(v, a);
      u->edges = {uv, ua};
      v->edges = {uv, va};
      a->edges = {ua, va};
      g.outerFace = g.extractRightFace(u, uv);
    } else {
      augmentOuterplanar(g, verbose);
    }
    nK = g.numberOfVertices();
    CHECK(nK >= 3 && g.numberOfEdges() == 2 * nK - 3 && g.outerFace.length() == nK,
          "augmented level component %d is not maximal outerplanar", bagId);
    CHECK(g.checkConsistency(false));
    for (const auto& [pair, edge] : support) {
      CHECK(g.extractEdge(g.vertices[pair.first], g.vertices[pair.second]) == edge,
            "augmentation removed a support edge of component %d", bagId);
    }
  }

  // The track drawing of the outerplanar graph, from an outer edge of span one.
  void drawOnTracks() {
    Adjacency adjK(nK);
    adjK.from_edges(g.extractEdgesId());
    vector<int> all(nK);
    std::iota(all.begin(), all.end(), 0);
    map<EdgeTy, int> drawingQueue;
    buildOuterplanarOrder(adjK, all, drawingQueue, &xs, &ys, verbose);
    CHECK((int)xs.size() == nK && (int)ys.size() == nK);
    // The orderer gives horizontal ranks, not coordinates. Check the embedded
    // order with the vertices placed on a convex curve in that order.
    auto convexCoordinates = [&]() {
      vector<int> byX(nK);
      std::iota(byX.begin(), byX.end(), 0);
      std::sort(byX.begin(), byX.end(), [&](int u, int v) { return xs[u] < xs[v]; });
      vector<int> ranks(nK, -1);
      vector<long long> convexY(nK, 0);
      for (int i = 0; i < nK; i++) {
        if (i > 0) {
          CHECK(xs[byX[i - 1]] < xs[byX[i]], "two vertices of K share a horizontal rank");
        }
        ranks[byX[i]] = i;
        convexY[byX[i]] = -(long long)i * i;
      }
      return make_pair(ranks, convexY);
    };
    auto mirror = [&]() {
      const int largest = *std::max_element(xs.begin(), xs.end());
      for (int& coordinate : xs) coordinate = largest - coordinate;
    };
    vector<long long> convexY;
    std::tie(rank, convexY) = convexCoordinates();
    if (!drawingMatchesClockwiseRotations(g, rank, convexY)) {
      mirror();
      std::tie(rank, convexY) = convexCoordinates();
      CHECK(drawingMatchesClockwiseRotations(g, rank, convexY),
            "the drawing changes the embedding of level component %d", bagId);
    }
    const Face& outer = g.outerFace;
    auto outerRanks = [&]() {
      vector<int> ranks(nK);
      for (int i = 0; i < nK; i++) ranks[i] = rank[outer.vertices[i]->index];
      return ranks;
    };
    auto clockwiseFromLeftmost = [&](bool forward) {
      const vector<int> ranks = outerRanks();
      const int at = (int)(std::find(ranks.begin(), ranks.end(), 0) - ranks.begin());
      bool agrees = true;
      for (int i = 0; i < nK; i++) {
        agrees &= ranks[(at + (forward ? i : nK - i)) % nK] == i;
      }
      return agrees;
    };
    if (nK == 3 && clockwiseFromLeftmost(true) && !clockwiseFromLeftmost(false)) {
      // A rotation at a degree-two vertex cannot tell a triangle from its
      // mirror; the designated outer face can.
      mirror();
      std::tie(rank, convexY) = convexCoordinates();
      CHECK(drawingMatchesClockwiseRotations(g, rank, convexY));
    }
    CHECK(clockwiseFromLeftmost(false),
          "the drawing reverses the outer face of level component %d", bagId);
    set<EdgeTy> outerPairs;
    for (int i = 0; i < nK; i++) {
      outerPairs.insert(make_edge(outer.vertices[i]->index, outer.vertices[(i + 1) % nK]->index));
    }
    vector<int> vertexAtRank(nK);
    for (int v = 0; v < nK; v++) vertexAtRank[rank[v]] = v;
    for (int i = 0; i + 1 < nK; i++) {
      CHECK(outerPairs.count(make_edge(vertexAtRank[i], vertexAtRank[i + 1])),
            "consecutive horizontal ranks are not adjacent on the outer face");
    }
    leftmost = vertexAtRank[0];
    rightmost = vertexAtRank[nK - 1];
    CHECK(outerPairs.count(make_edge(leftmost, rightmost)) &&
          std::abs(ys[leftmost] - ys[rightmost]) == 1,
          "the drawing of component %d does not start from a span-one outer edge", bagId);
  }

  // The edges of K, the retained copies, and the slots of every tripod.
  void buildSlots() {
    const Face& outer = g.outerFace;
    K.x.resize(nK);
    K.y.resize(nK);
    for (int v = 0; v < nK; v++) {
      K.x[v] = rank[v];
      K.y[v] = ys[v];
    }
    unordered_map<Edge*, int> kEdgeOf;
    for (Edge* edge : g.extractEdges()) {
      const int a = edge->source->index, b = edge->target->index;
      const EdgeTy pair = make_edge(a, b);
      const bool isSupport = a < count && b < count && support.count(pair) &&
                             support.at(pair) == edge;
      kEdgeOf[edge] = (int)K.edges.size();
      K.edges.push_back({{a, b}, isSupport ? LevelK::kSupport : LevelK::kAugmentation, -1});
      if (isSupport) K.supportEdge[pair] = kEdgeOf[edge];
    }
    CHECK(K.supportEdge.size() == support.size());
    K.startEdge = kEdgeOf.at(g.extractEdge(g.vertices[leftmost], g.vertices[rightmost]));
    CHECK(outer == g.extractRightFace(outer.vertices[0], outer.edges[0]));
    // The corner of the outer face at outer.vertices[0] runs clockwise from
    // outer.edges[0]; it is the sector entered along that edge.
    K.outerDart = K.dart(kEdgeOf.at(outer.edges[0]), outer.vertices[1]->index);

    K.classOf.assign(count, {});
    for (int u = 0; u < count; u++) {
      const auto& atoms = atomsByPod[K.podIds[u]];
      K.classOf[u] = atoms.classPod;
    }
    // The retained copy of each support is the extreme copy opposite to its
    // designated side, so the digons lie on the designated side.
    auto classRawRange = [&](int u, int w) {
      const auto& cls = K.classOf[u];
      const int length = (int)cls.size();
      const int pod = K.podIds[w];
      int first = -1;
      for (int pos = 0; pos < length; pos++) {
        if (cls[pos] == pod && cls[(pos + length - 1) % length] != pod) {
          CHECK(first == -1, "support class (%d,%d) is not consecutive", K.podIds[u], pod);
          first = pos;
        }
      }
      CHECK(first >= 0);
      int last = first;
      while (cls[(last + 1) % length] == pod) last = (last + 1) % length;
      return make_pair(first, last);
    };
    map<pair<int, int>, int> retainedPos;  // (vertex, K edge) -> raw position
    for (const auto& [pair, e] : K.supportEdge) {
      int retainedEdge = -1;
      for (int side = 0; side < 2; side++) {
        const int u = side == 0 ? pair.first : pair.second;
        const int w = side == 0 ? pair.second : pair.first;
        const auto [first, last] = classRawRange(u, w);
        const int pos = K.designatedClockwise(u, w) ? first : last;
        const auto& incidence = raw.clockwiseRotation[K.podIds[u]][pos];
        const int rawId = raw.edgeIndex.at(incidence.originalEdge);
        const auto& record = raw.edges[rawId];
        CHECK(record.endpointPod[1 - incidence.endpoint] == K.podIds[w],
              "a support class does not end with a copy");
        // The copies appear in reversed cyclic order at the two endpoints, so
        // this checks the class structure, not the choice of side (which the
        // ownership checks of the digons test).
        CHECK(retainedEdge == -1 || retainedEdge == rawId,
              "the extreme copies of (%d,%d) differ at its two endpoints",
              K.podIds[pair.first], K.podIds[pair.second]);
        retainedEdge = rawId;
        retainedPos[{u, e}] = pos;
      }
      K.edges[e].rawEdge = retainedEdge;
    }

    K.slots.assign(count, {});
    for (int u = 0; u < count; u++) {
      const int pod = K.podIds[u];
      const int length = (int)raw.clockwiseRotation[pod].size();
      for (int pos = 0; pos < length; pos++) K.slots[u].push_back({pos, -1});
      for (Edge* edge : g.vertices[u]->edges) {
        const int e = kEdgeOf.at(edge);
        if (K.edges[e].kind == LevelK::kSupport) {
          K.slots[u][retainedPos.at({u, e})].kEdge = e;
        }
      }
      // Edges of K that are not raw edges, in the rotation of g.
      const auto& rotation = g.vertices[u]->edges;
      const int degree = (int)rotation.size();
      int startAt = -1;
      for (int i = 0; i < degree; i++) {
        if (K.edges[kEdgeOf.at(rotation[i])].kind == LevelK::kSupport) {
          startAt = i;
          break;
        }
      }
      int pointer = -1;
      if (startAt == -1) {
        // A single vertex: insert both auxiliary edges at one top-level cut, so
        // that the empty sector between them is the outer face.
        CHECK(count == 1 && degree == 2);
        const int at = outer.getIndex(g.vertices[u]);
        CHECK(at >= 0);
        startAt = rotation[0] == outer.edges[at] ? 0 : 1;
        CHECK(rotation[startAt] == outer.edges[at]);
        pointer = 0;
        int anchorEdge = (int)raw.edges.size();
        for (int pos = 0; pos < length; pos++) {
          const auto& incidence = raw.clockwiseRotation[pod][pos];
          const int rawId = raw.edgeIndex.at(incidence.originalEdge);
          const int other = raw.edges[rawId].endpointPod[1 - incidence.endpoint];
          if (tp.vertex2depth[other] == tp.vertex2depth[pod] - 1 && rawId < anchorEdge) {
            anchorEdge = rawId;
            pointer = pos;
          }
        }
      }
      for (int step = 0; step < degree; step++) {
        const int e = kEdgeOf.at(rotation[(startAt + step) % degree]);
        if (K.edges[e].kind == LevelK::kSupport) {
          pointer = K.classSlots(u, e).second + 1;
        } else {
          K.insertSlot(u, pointer, e);
          pointer++;
        }
      }
    }
    K.auxRotation.assign(nK - count, {});
    for (int v = count; v < nK; v++) {
      for (Edge* edge : g.vertices[v]->edges) K.auxRotation[v - count].push_back(kEdgeOf.at(edge));
    }
    K.computeFaces();
    CHECK((int)K.faceDarts[K.outerFace].size() == nK,
          "outer face of K for component %d does not visit every vertex", bagId);
    // Track the outer face by the outer side of the starting edge; no
    // auxiliary triangle is ever attached on that side.
    {
      const int d0 = 2 * K.startEdge, d1 = 2 * K.startEdge + 1;
      CHECK((K.faceOfDart[d0] == K.outerFace) != (K.faceOfDart[d1] == K.outerFace),
            "the starting edge of component %d is not on the outer face once", bagId);
      K.outerDart = K.faceOfDart[d0] == K.outerFace ? d0 : d1;
    }
    for (int face = 0; face < (int)K.faceDarts.size(); face++) {
      CHECK(face == K.outerFace || K.faceDarts[face].size() == 3,
            "augmented component %d has a bounded nontriangular face", bagId);
    }
  }

  // Auxiliary triangles on designated sides that are the outer face.
  void addDesignatedSideTriangles() {
    struct Pending { int e, a, b; };
    vector<Pending> pending;
    for (const auto& [pair, e] : K.supportEdge) {
      const int a = pair.first, b = pair.second;
      const int cwFace = K.sectorFace(a, e);
      const auto rot = K.rotation(a);
      const int at = (int)(std::find(rot.begin(), rot.end(), e) - rot.begin());
      const int ccwFace = K.sectorFace(a, rot[(at + rot.size() - 1) % rot.size()]);
      if (cwFace != K.outerFace && ccwFace != K.outerFace) continue;
      CHECK(cwFace != ccwFace, "support (%d,%d) is a bridge of K", a, b);
      if (K.designatedClockwise(a, b) == (cwFace == K.outerFace)) {
        CHECK(e != K.startEdge, "the starting edge has its designated side outside");
        pending.push_back({e, a, b});
      }
    }
    for (const Pending& p : pending) {
      const int aux = K.numVertices();
      const int spanAB = K.span(p.e);
      K.x.push_back((K.x[p.a] + K.x[p.b]) / 2);
      K.y.push_back(spanAB == 1 ? std::max(K.y[p.a], K.y[p.b]) + 1
                                : std::min(K.y[p.a], K.y[p.b]) + 1);
      const int ea = (int)K.edges.size();
      K.edges.push_back({{p.a, aux}, LevelK::kAuxiliary, -1});
      const int eb = (int)K.edges.size();
      K.edges.push_back({{p.b, aux}, LevelK::kAuxiliary, -1});
      K.auxRotation.push_back({ea, eb});
      // Faces are still those before this insertion at p.a and p.b, since
      // pending triangles sit on distinct edges.
      K.insertNextToOuterSide(p.a, p.e, ea);
      K.insertNextToOuterSide(p.b, p.e, eb);
      K.designatedTriangles++;
    }
    K.computeFaces();
  }

  const RawTripodQuotient& raw;
  const TreePartition& tp;
  const int bagId;
  const vector<int>& rawSupportEdges;
  const vector<int>& initialOuterPodCycle;
  const vector<RawRotationAtoms>& atomsByPod;
  const int verbose;
  LevelK K;
  int count{0};
  PlanarGraph g;
  unordered_map<int, int> local;   // tripod -> vertex of g
  map<EdgeTy, Edge*> support;      // level edge of K̂ -> its edge of g
  int nK{0};                       // vertices of the augmented graph
  vector<int> xs, ys, rank;        // drawing: rank, track, horizontal rank
  int leftmost{-1}, rightmost{-1};
};

LevelK buildLevelK(
    const RawTripodQuotient& raw,
    const TreePartition& tp,
    int bagId,
    const vector<int>& rawSupportEdges,
    const vector<int>& initialOuterPodCycle,
    const vector<RawRotationAtoms>& atomsByPod, int verbose) {
  return LevelKBuilder(raw, tp, bagId, rawSupportEdges, initialOuterPodCycle, atomsByPod, verbose).build();
}

// Wrap each face of K̂ that still lies in the outer face of K. The
// edge of an auxiliary triangle at u is moved over the faces, or a new
// triangle (u, w, a) is added on an outer edge u-w.
void wrapOuterFaces(LevelK& K, const vector<ParentFace>& faces) {
  map<int, int> localOf;
  for (int i = 0; i < K.numReal; i++) localOf[K.podIds[i]] = i;
  for (int round = 0;; round++) {
    CHECK(round <= K.numReal, "wrapping faces of K̂ does not terminate");
    map<int, vector<const ParentFace*>> outerAt;
    for (const ParentFace& face : faces) {
      const int pod = *face.boundaryPods.begin();
      const auto& corner = face.cornersByPod.at(pod).front();
      if (K.cornerFace(localOf.at(pod), corner.clockwiseStart, corner.clockwiseEnd) !=
          K.outerFace) continue;
      CHECK(face.boundaryPods.size() == 1,
            "a digon or triangular face of K̂ lies in the outer face of K");
      outerAt[localOf.at(pod)].push_back(&face);
    }
    if (outerAt.empty()) return;
    const int u = outerAt.begin()->first;
    const auto rot = K.rotation(u);
    int ea = -1, eb = -1;
    for (int i = 0; i < (int)rot.size(); i++) {
      if (K.sectorFace(u, rot[i]) == K.outerFace) {
        CHECK(ea == -1, "vertex %d of K has two outer corners", u);
        ea = rot[i];
        eb = rot[(i + 1) % rot.size()];
      }
    }
    CHECK(ea >= 0);
    const int size = (int)K.slots[u].size();
    const int base = K.slotOfEdge(u, ea);
    auto offset = [&](int slot) { return (slot - base + size) % size; };
    const int limit = offset(K.slotOfEdge(u, eb));
    int lo = size, hi = -1;
    for (const ParentFace* face : outerAt.at(u)) {
      for (const auto& corner : face->cornersByPod.at(K.podIds[u])) {
        lo = std::min(lo, offset(K.slotOfRaw(u, corner.clockwiseStart)));
        hi = std::max(hi, offset(K.slotOfRaw(u, corner.clockwiseEnd)));
      }
    }
    CHECK(0 < lo && lo <= hi && hi < limit,
          "faces of K̂ in the outer face at tripod %d leave its outer corner", K.podIds[u]);
    const int loRaw = K.slots[u][(base + lo) % size].rawPos;
    const int hiRaw = K.slots[u][(base + hi) % size].rawPos;
    CHECK(loRaw >= 0 && hiRaw >= 0);
    auto moveSlot = [&](int e, bool afterHi) {
      auto& list = K.slots[u];
      const LevelK::Slot slot = list[K.slotOfEdge(u, e)];
      list.erase(list.begin() + K.slotOfEdge(u, e));
      const int at = afterHi ? K.slotOfRaw(u, hiRaw) + 1 : K.slotOfRaw(u, loRaw);
      list.insert(list.begin() + at, slot);
    };
    if (K.edges[ea].kind == LevelK::kAuxiliary) {
      moveSlot(ea, true);
      K.wrapReused++;
    } else if (K.edges[eb].kind == LevelK::kAuxiliary) {
      moveSlot(eb, false);
      K.wrapReused++;
    } else {
      int via = -1;
      for (int e : {ea, eb}) {
        const int w = K.other(e, u);
        if (e == K.startEdge) continue;
        if (K.span(e) == 2 && K.y[w] < K.y[u]) continue;
        via = e;
        break;
      }
      CHECK(via >= 0, "tripod %d has no outer edge for a wrapping triangle "
            "(both outer edges have span two and go down?)", K.podIds[u]);
      const int w = K.other(via, u);
      const int aux = K.numVertices();
      K.x.push_back((K.x[u] + K.x[w]) / 2);
      K.y.push_back(K.span(via) == 1 ? std::max(K.y[u], K.y[w]) + 1
                                     : std::min(K.y[u], K.y[w]) + 1);
      const int eu = (int)K.edges.size();
      K.edges.push_back({{u, aux}, LevelK::kAuxiliary, -1});
      const int ew = (int)K.edges.size();
      K.edges.push_back({{w, aux}, LevelK::kAuxiliary, -1});
      K.auxRotation.push_back({eu, ew});
      K.insertNextToOuterSide(w, via, ew);
      K.insertSlot(u, via == ea ? K.slotOfRaw(u, hiRaw) + 1 : K.slotOfRaw(u, loRaw), eu);
      K.wrapAdded++;
    }
    K.computeFaces();
  }
}

// The properties of the track drawing of K with its auxiliary vertices.
vector<int> verifyLevelKDrawing(const LevelK& K, int bagId) {
  const int n = K.numVertices();
  for (int e = 0; e < (int)K.edges.size(); e++) {
    CHECK(K.span(e) == 1 || K.span(e) == 2, "edge %d of K in component %d has span %d",
          e, bagId, K.span(e));
  }
  CHECK((int)K.faceDarts[K.outerFace].size() == n,
        "outer face of K in component %d does not visit every vertex", bagId);
  vector<int> byX(n);
  std::iota(byX.begin(), byX.end(), 0);
  std::sort(byX.begin(), byX.end(), [&](int u, int v) { return K.x[u] < K.x[v]; });
  vector<int> xRank(n);
  for (int i = 0; i < n; i++) {
    if (i > 0) CHECK(K.x[byX[i - 1]] < K.x[byX[i]], "two vertices of K share x");
    xRank[byX[i]] = i;
  }
  for (int face = 0; face < (int)K.faceDarts.size(); face++) {
    if (face == K.outerFace) continue;
    vector<int> vs = K.faceVertices(face);
    CHECK(vs.size() == 3, "component %d: K has a bounded nontriangular face", bagId);
    vector<int> heights = {K.y[vs[0]], K.y[vs[1]], K.y[vs[2]]};
    std::sort(heights.begin(), heights.end());
    CHECK(heights[1] == heights[0] + 1 && heights[2] == heights[0] + 2,
          "component %d: a triangle of K is not on three consecutive tracks", bagId);
    // The vertex in the middle by x is the apex added above the edge joining
    // the other two: one track above both for a span-one edge, on the
    // middle track for a span-two edge.
    std::sort(vs.begin(), vs.end(), [&](int a, int b) { return xRank[a] < xRank[b]; });
    const int baseSpan = std::abs(K.y[vs[0]] - K.y[vs[2]]);
    CHECK(baseSpan == 1 ? K.y[vs[1]] == std::max(K.y[vs[0]], K.y[vs[2]]) + 1
                        : 2 * K.y[vs[1]] == K.y[vs[0]] + K.y[vs[2]],
          "component %d: a triangle of K is not an apex above its base edge", bagId);
  }
  // The outer face follows the horizontal order, closed by the starting edge.
  set<EdgeTy> outerPairs;
  for (int d : K.faceDarts[K.outerFace]) {
    outerPairs.insert(make_edge(K.edges[d / 2].end[0], K.edges[d / 2].end[1]));
  }
  for (int i = 0; i + 1 < n; i++) {
    CHECK(outerPairs.count(make_edge(byX[i], byX[i + 1])),
          "component %d: consecutive vertices of K are not adjacent on the outer face", bagId);
  }
  CHECK(make_edge(byX[0], byX[n - 1]) ==
            make_edge(K.edges[K.startEdge].end[0], K.edges[K.startEdge].end[1]),
        "component %d: the starting edge does not join the extreme vertices", bagId);
  // The embedding agrees with the vertices placed on a convex curve.
  PlanarGraph drawn;
  for (int v = 0; v < n; v++) drawn.newVertex();
  vector<Edge*> edgeOf;
  for (const auto& edge : K.edges) {
    edgeOf.push_back(drawn.newEdge(drawn.vertices[edge.end[0]], drawn.vertices[edge.end[1]]));
  }
  for (int v = 0; v < n; v++) {
    for (int e : K.rotation(v)) drawn.vertices[v]->edges.push_back(edgeOf[e]);
  }
  vector<long long> convexY(n);
  for (int v = 0; v < n; v++) convexY[v] = -(long long)xRank[v] * xRank[v];
  CHECK(drawingMatchesClockwiseRotations(drawn, xRank, convexY),
        "component %d: K with auxiliary vertices is not outerplane in its drawing", bagId);
  // The order of the track drawing and its two queues (span one, span two).
  vector<int> order(n);
  std::iota(order.begin(), order.end(), 0);
  std::sort(order.begin(), order.end(), [&](int u, int v) {
    return make_pair(K.y[u], K.x[u]) < make_pair(K.y[v], K.x[v]);
  });
  vector<EdgeTy> spanEdges[2];
  for (int e = 0; e < (int)K.edges.size(); e++) {
    spanEdges[K.span(e) - 1].push_back(make_edge(K.edges[e].end[0], K.edges[e].end[1]));
  }
  CHECK(countRainbow(spanEdges[0], order) <= 1, "component %d: span-one edges of K nest", bagId);
  CHECK(countRainbow(spanEdges[1], order) <= 1, "component %d: span-two edges of K nest", bagId);
  vector<int> rankK(n);
  for (int i = 0; i < n; i++) rankK[order[i]] = i;
  return rankK;
}

// The intervals I_t(u) and I_mb(u) at a tripod u. I_t runs
// clockwise from the leftmost to the rightmost edge of K from u to a higher
// vertex, both included, through the upward ray; where no such edge exists on
// a side, the line just above the track of u bounds it. I_mb is the rest.
// Both are read from the left boundary: I_t clockwise, I_mb counterclockwise.
// Only incidences of K̂ and binding edges to child components take part;
// edges to the preceding level are not part of this graph.
struct RawIntervals {
  int leftCutBefore{-1};
  vector<bool> inContext;
  vector<bool> incidenceInTop;
  vector<int> topPosition;
  vector<int> bottomMiddlePosition;
};

RawIntervals buildIntervals(
    const LevelK& K, int u, const RawTripodQuotient& raw, const TreePartition& tp) {
  const int pod = K.podIds[u];
  const auto& rotation = raw.clockwiseRotation[pod];
  const int length = (int)rotation.size();
  RawIntervals result;
  result.inContext.assign(length, false);
  result.incidenceInTop.assign(length, false);
  result.topPosition.assign(length, -1);
  result.bottomMiddlePosition.assign(length, -1);
  for (int pos = 0; pos < length; pos++) {
    const auto& record = raw.edges[raw.edgeIndex.at(rotation[pos].originalEdge)];
    const int other = record.endpointPod[1 - rotation[pos].endpoint];
    const int depth = tp.vertex2depth[other] - tp.vertex2depth[pod];
    result.inContext[pos] = depth == 0 || depth == 1;
  }

  const auto rot = K.rotation(u);
  const int degree = (int)rot.size();
  int outerAt = -1;
  for (int i = 0; i < degree; i++) {
    if (K.sectorFace(u, rot[i]) == K.outerFace) {
      CHECK(outerAt == -1, "tripod %d has two corners in the outer face of K", pod);
      outerAt = i;
    }
  }
  CHECK(outerAt >= 0, "tripod %d has no corner in the outer face of K", pod);
  const int ea = rot[outerAt], eb = rot[(outerAt + 1) % degree];
  // Clockwise from the upward ray: up-right, down-right, down-left, up-left.
  enum { UR, DR, DL, UL };
  vector<int> sequence;
  for (int step = 1; step <= degree; step++) sequence.push_back(rot[(outerAt + step) % degree]);
  auto label = [&](int e) {
    const int z = K.other(e, u);
    const double dx = K.x[z] - K.x[u];
    const int dy = K.y[z] - K.y[u];
    CHECK(dx != 0 && dy != 0);
    return dy > 0 ? (dx > 0 ? UR : UL) : (dx > 0 ? DR : DL);
  };
  int firstUL = -1, lastUR = -1;
  for (int i = 0; i < degree; i++) {
    const int current = label(sequence[i]);
    if (i > 0) {
      CHECK(label(sequence[i - 1]) <= current,
            "edges of K at tripod %d are not in angular order around the upward ray", pod);
    }
    if (current == UL && firstUL == -1) firstUL = sequence[i];
    if (current == UR) lastUR = sequence[i];
  }
  const int size = (int)K.slots[u].size();
  const int startSlot = firstUL >= 0 ? K.classSlots(u, firstUL).first
                                     : (K.classSlots(u, ea).second + 1) % size;
  const int endSlot = lastUR >= 0 ? K.classSlots(u, lastUR).second
                                  : (K.classSlots(u, eb).first - 1 + size) % size;
  const int count = (firstUL < 0 && lastUR < 0)
      ? (endSlot - startSlot + 1 + size) % size
      : (endSlot - startSlot + size) % size + 1;
  vector<bool> slotInTop(size, false);
  for (int k = 0; k < count; k++) slotInTop[(startSlot + k) % size] = true;
  // Nothing of this graph remains in the outer face of K.
  const int outerFrom = K.classSlots(u, ea).second;
  const int outerTo = K.classSlots(u, eb).first;
  for (int i = (outerFrom + 1) % size; i != outerTo; i = (i + 1) % size) {
    const int pos = K.slots[u][i].rawPos;
    CHECK(pos < 0 || !result.inContext[pos],
          "an incidence of K̂ at tripod %d lies in the outer face of K", pod);
  }
  int topRank = 0, bottomRank = 0;
  for (int k = 0; k < size; k++) {
    const auto& clockwise = K.slots[u][(startSlot + k) % size];
    if (clockwise.rawPos >= 0) {
      if (result.leftCutBefore < 0) result.leftCutBefore = clockwise.rawPos;
      if (slotInTop[(startSlot + k) % size]) {
        result.incidenceInTop[clockwise.rawPos] = true;
        result.topPosition[clockwise.rawPos] = topRank++;
      }
    }
    const int ccwSlot = (startSlot - 1 - k + 2 * size) % size;
    const auto& counterclockwise = K.slots[u][ccwSlot];
    if (counterclockwise.rawPos >= 0 && !slotInTop[ccwSlot]) {
      result.bottomMiddlePosition[counterclockwise.rawPos] = bottomRank++;
    }
  }
  CHECK(topRank + bottomRank == length && result.leftCutBefore >= 0);
  return result;
}

struct QuotientOrder {
  vector<int> bagOrder;
  vector<int> podOrder;
  vector<int> rawEdgeQueue;  // -1 for a loop, otherwise Q0,Q1,Qt,Qm,Qb = 0,...,4
  vector<vector<int>> childrenInOrder;
};

// Combine lists that agree on common elements into one order preserving
// each list: repeatedly take an element that is first in every
// remaining list containing it; ties go to the smaller key.
vector<int> mergeFaceLists(const vector<vector<int>>& lists, const map<int, int>& key) {
  for (int a = 0; a < (int)lists.size(); a++) {
    for (int b = a + 1; b < (int)lists.size(); b++) {
      vector<int> inA, inB;
      set<int> setA(lists[a].begin(), lists[a].end()), setB(lists[b].begin(), lists[b].end());
      for (int f : lists[a]) if (setB.count(f)) inA.push_back(f);
      for (int f : lists[b]) if (setA.count(f)) inB.push_back(f);
      CHECK(inA == inB, "two lists of one owner disagree on their common faces");
    }
  }
  vector<size_t> head(lists.size(), 0);
  set<int> remaining;
  for (const auto& list : lists) remaining.insert(list.begin(), list.end());
  vector<int> result;
  while (!remaining.empty()) {
    int chosen = -1;
    for (int f : remaining) {
      bool eligible = true;
      for (int l = 0; l < (int)lists.size(); l++) {
        const bool contains = std::find(lists[l].begin() + head[l], lists[l].end(), f) !=
                              lists[l].end();
        eligible &= !contains || lists[l][head[l]] == f;
      }
      if (eligible && (chosen == -1 || key.at(f) < key.at(chosen))) chosen = f;
    }
    CHECK(chosen >= 0, "the lists of one owner admit no common order");
    result.push_back(chosen);
    remaining.erase(chosen);
    for (int l = 0; l < (int)lists.size(); l++) {
      if (head[l] < lists[l].size() && lists[l][head[l]] == chosen) head[l]++;
    }
  }
  return result;
}

// Order level components by their containing faces and assign quotient edges
// to five queues, checking nesting and rotation compatibility.
class QuotientOrderBuilder {
 public:
  QuotientOrderBuilder(
      const RawTripodQuotient& raw,
      const TreePartition& tp,
      const vector<vector<ParentFace>>& parentFaces,
      const vector<LevelK>& Ks,
      const vector<vector<int>>& rankK,
      const vector<RawIntervals>& intervalsByPod,
      int verbose)
      : raw(raw), tp(tp), parentFaces(parentFaces), Ks(Ks), rankK(rankK),
        intervalsByPod(intervalsByPod), verbose(verbose),
        podCount((int)raw.clockwiseRotation.size()), bagCount(tp.numBags),
        localAt(podCount, -1), childFace(bagCount, -1), childOwner(bagCount, -1),
        childRoles(bagCount, {-1, -1, -1}) {
    for (int bag = 0; bag < bagCount; bag++) {
      for (int i = 0; i < Ks[bag].numReal; i++) localAt[Ks[bag].podIds[i]] = i;
    }
    result.childrenInOrder.resize(bagCount);
  }

  QuotientOrder build() {
    for (int bag = 0; bag < bagCount; bag++) orderFaces(bag);
    LOG_IF(verbose, "owners of faces of K̂: triangles=%d digons=%d monogons=%d",
           ownedBy[3], ownedBy[2], ownedBy[1]);
    orderTripods();
    assignQueues();
    verifyIntervalsAndCompatibility();
    return std::move(result);
  }

 private:
  // The owners of the faces of one level component and the order of its
  // child components: owners in lexicographic (b, m, t) order, faces with one
  // owner by merging the lists B, M, and T.
  void orderFaces(int bag) {
    const LevelK& K = Ks[bag];
    const auto& faces = parentFaces[bag];
    vector<int> owner(faces.size(), -1);
    map<int, array<int, 3>> roles;  // owner face -> (b, m, t)
    for (int f = 0; f < (int)faces.size(); f++) {
      for (const auto& [pod, corners] : faces[f].cornersByPod) {
        for (const auto& corner : corners) {
          const int face = K.cornerFace(localAt[pod], corner.clockwiseStart, corner.clockwiseEnd);
          CHECK(owner[f] == -1 || owner[f] == face,
                "a face of K̂ in component %d lies in two faces of K", bag);
          owner[f] = face;
        }
      }
      CHECK(owner[f] >= 0 && owner[f] != K.outerFace,
            "a face of K̂ in component %d has no owner triangle", bag);
      vector<int> tri = K.faceVertices(owner[f]);
      CHECK(tri.size() == 3);
      std::sort(tri.begin(), tri.end(), [&](int a, int b) { return K.y[a] < K.y[b]; });
      roles[owner[f]] = {tri[0], tri[1], tri[2]};
      for (int pod : faces[f].boundaryPods) {
        CHECK(std::find(tri.begin(), tri.end(), localAt[pod]) != tri.end(),
              "a boundary vertex of a face of K̂ is not a vertex of its owner");
      }
      ownedBy[faces[f].boundaryPods.size()]++;
      if (faces[f].child >= 0) {
        CHECK(childFace[faces[f].child] == -1);
        childFace[faces[f].child] = f;
        childOwner[faces[f].child] = owner[f];
        childRoles[faces[f].child] = roles[owner[f]];
      }
    }
    // The lists B, M, T of every owner with occupied faces.
    map<int, vector<vector<int>>> lists;
    map<int, int> key;
    for (int f = 0; f < (int)faces.size(); f++) {
      if (faces[f].child < 0) continue;
      key[f] = faces[f].rawFaceId;
      lists[owner[f]];
    }
    for (auto& [ownerFace, ownerLists] : lists) {
      const auto& r = roles.at(ownerFace);
      for (int role = 0; role < 3; role++) {
        const int v = r[role];
        if (K.isAux(v)) continue;
        const auto rot = K.rotation(v);
        int at = -1;
        for (int i = 0; i < (int)rot.size(); i++) {
          if (K.sectorFace(v, rot[i]) == ownerFace) {
            CHECK(at == -1);
            at = i;
          }
        }
        CHECK(at >= 0, "an owner triangle has no corner at its vertex");
        const int size = (int)K.slots[v].size();
        const int from = K.slotOfEdge(v, rot[at]);
        const int to = K.slotOfEdge(v, rot[(at + 1) % rot.size()]);
        vector<int> sector;
        for (int i = (from + 1) % size; i != to; i = (i + 1) % size) sector.push_back(i);
        if (role != 0) std::reverse(sector.begin(), sector.end());  // counterclockwise at m, t
        vector<int> list;
        set<int> seen;
        const int pod = K.podIds[v];
        for (int i : sector) {
          const int pos = K.slots[v][i].rawPos;
          if (pos < 0) continue;
          const auto& incidence = raw.clockwiseRotation[pod][pos];
          const auto& record = raw.edges[raw.edgeIndex.at(incidence.originalEdge)];
          const int other = record.endpointPod[1 - incidence.endpoint];
          if (tp.vertex2depth[other] != tp.vertex2depth[pod] + 1) continue;
          const int child = tp.vertex2bag[other];
          CHECK(childOwner[child] == ownerFace,
                "a binding inside an owner leads to a component owned elsewhere");
          if (seen.insert(child).second) list.push_back(childFace[child]);
        }
        ownerLists.push_back(list);
      }
    }
    // Owners in lexicographic (b, m, t) order, then the merged lists.
    vector<int> owners;
    for (const auto& [ownerFace, unused] : lists) owners.push_back(ownerFace);
    std::sort(owners.begin(), owners.end(), [&](int a, int b) {
      const auto& ra = roles.at(a);
      const auto& rb = roles.at(b);
      return make_tuple(rankK[bag][ra[0]], rankK[bag][ra[1]], rankK[bag][ra[2]]) <
             make_tuple(rankK[bag][rb[0]], rankK[bag][rb[1]], rankK[bag][rb[2]]);
    });
    for (int ownerFace : owners) {
      map<int, int> ownerKey;
      for (const auto& list : lists.at(ownerFace)) {
        for (int f : list) ownerKey[f] = key.at(f);
      }
      size_t ownedFaces = 0;
      for (int f = 0; f < (int)faces.size(); f++) {
        ownedFaces += faces[f].child >= 0 && owner[f] == ownerFace;
      }
      CHECK(ownerKey.size() == ownedFaces,
            "an occupied face is missing from every list of its owner");
      for (int f : mergeFaceLists(lists.at(ownerFace), ownerKey)) {
        result.childrenInOrder[bag].push_back(faces[f].child);
      }
    }
  }

  // Breadth-first order of the level components; within one, the order of K.
  void orderTripods() {
    const int rootBag = tp.vertex2bag[0];
    result.bagOrder.push_back(rootBag);
    vector<bool> seenBag(bagCount, false);
    seenBag[rootBag] = true;
    for (int cursor = 0; cursor < (int)result.bagOrder.size(); cursor++) {
      const int parent = result.bagOrder[cursor];
      for (int child : result.childrenInOrder[parent]) {
        CHECK(!seenBag[child] && tp.bag2depth[child] == tp.bag2depth[parent] + 1);
        seenBag[child] = true;
        result.bagOrder.push_back(child);
      }
    }
    CHECK((int)result.bagOrder.size() == bagCount, "a component has no owner face");
    bagRank.assign(bagCount, -1);
    podRank.assign(podCount, -1);
    for (int i = 0; i < bagCount; i++) bagRank[result.bagOrder[i]] = i;
    for (int bag : result.bagOrder) {
      vector<int> real(Ks[bag].numReal);
      std::iota(real.begin(), real.end(), 0);
      std::sort(real.begin(), real.end(), [&](int a, int b) {
        return rankK[bag][a] < rankK[bag][b];
      });
      for (int v : real) {
        podRank[Ks[bag].podIds[v]] = (int)result.podOrder.size();
        result.podOrder.push_back(Ks[bag].podIds[v]);
      }
    }
    CHECK((int)result.podOrder.size() == podCount);
  }

  // Level edges by span; binding edges by the role of the parent in the owner
  // of the face of the child.
  void assignQueues() {
    result.rawEdgeQueue.assign(raw.edges.size(), -1);
    std::array<vector<EdgeTy>, 5> queueEdges;
    map<EdgeTy, int> simpleQueue;
    map<pair<int, int>, set<int>> sourcesOf;  // (child, queue) -> parents
    for (int e = 0; e < (int)raw.edges.size(); e++) {
      const int u = raw.edges[e].endpointPod[0];
      const int v = raw.edges[e].endpointPod[1];
      if (u == v) continue;
      int q = -1;
      if (tp.vertex2depth[u] == tp.vertex2depth[v]) {
        const int bag = tp.vertex2bag[u];
        CHECK(bag == tp.vertex2bag[v]);
        const int span = std::abs(Ks[bag].y[localAt[u]] - Ks[bag].y[localAt[v]]);
        CHECK(span == 1 || span == 2);
        q = span - 1;
      } else {
        const int source = tp.vertex2depth[u] < tp.vertex2depth[v] ? u : v;
        const int childPod = source == u ? v : u;
        const int child = tp.vertex2bag[childPod];
        const auto& r = childRoles[child];
        const int role = (int)(std::find(r.begin(), r.end(), localAt[source]) - r.begin());
        CHECK(tp.vertex2bag[source] == tp.vertex2bag[tp.bag2parents[child][0]] && role < 3,
              "a binding parent is not a vertex of the owner of its child");
        q = 2 + role;
        sourcesOf[{child, q}].insert(source);
      }
      result.rawEdgeQueue[e] = q;
      const auto [it, inserted] = simpleQueue.emplace(make_edge(u, v), q);
      CHECK(inserted || it->second == q, "parallel quotient edges use different queues");
      if (inserted) queueEdges[q].push_back(make_edge(u, v));
    }
    CHECK(simpleQueue.size() == raw.simplePodAdj.num_edges());
    for (int q = 0; q < 5; q++) {
      CHECK(countRainbow(queueEdges[q], result.podOrder) <= 1,
            "quotient Q%d contains two nested independent edges", q);
    }
    for (const auto& [childQueue, sources] : sourcesOf) {
      CHECK(sources.size() == 1, "component %d has two parents in one binding queue",
            childQueue.first);
    }
  }

  // Interval containment, and compatibility of the first-edge sequences with
  // the quotient order.
  void verifyIntervalsAndCompatibility() {
    for (int pod = 0; pod < podCount; pod++) {
      const int bag = tp.vertex2bag[pod];
      const LevelK& K = Ks[bag];
      const auto& rotation = raw.clockwiseRotation[pod];
      const auto& intervals = intervalsByPod[pod];
      const int length = (int)rotation.size();
      vector<pair<int, int>> top, bottom;  // (rank, raw position)
      for (int pos = 0; pos < length; pos++) {
        if (!intervals.inContext[pos]) continue;
        const int e = raw.edgeIndex.at(rotation[pos].originalEdge);
        const int other = raw.edges[e].endpointPod[1 - rotation[pos].endpoint];
        const int q = result.rawEdgeQueue[e];
        if (q < 0) continue;  // a loop
        bool wantTop;
        if (q <= 1) {
          wantTop = K.y[localAt[other]] > K.y[localAt[pod]];
        } else {
          if (tp.vertex2depth[other] < tp.vertex2depth[pod]) continue;
          wantTop = q == 2;
        }
        CHECK(intervals.incidenceInTop[pos] == wantTop,
              "Q%d incidence at tripod %d lies in the wrong interval",
              q, pod);
        if (wantTop) top.push_back({intervals.topPosition[pos], pos});
        else bottom.push_back({intervals.bottomMiddlePosition[pos], pos});
      }
      for (auto* sweep : {&top, &bottom}) {
        std::sort(sweep->begin(), sweep->end());
        for (int q = 0; q < 5; q++) {
          set<int> seen;
          int previousRank = -1;
          for (const auto& [rank, pos] : *sweep) {
            const int e = raw.edgeIndex.at(rotation[pos].originalEdge);
            if (result.rawEdgeQueue[e] != q) continue;
            const int other = raw.edges[e].endpointPod[1 - rotation[pos].endpoint];
            const int target = q <= 1 ? other : tp.vertex2bag[other];
            if (!seen.insert(target).second) continue;
            const int targetRank = q <= 1 ? podRank[target] : bagRank[target];
            CHECK(targetRank > previousRank,
                  "first-edge sequence of Q%d at tripod %d is not compatible with the "
                  "quotient order", q, pod);
            previousRank = targetRank;
          }
        }
      }
    }
  }

  const RawTripodQuotient& raw;
  const TreePartition& tp;
  const vector<vector<ParentFace>>& parentFaces;
  const vector<LevelK>& Ks;
  const vector<vector<int>>& rankK;
  const vector<RawIntervals>& intervalsByPod;
  const int verbose;
  const int podCount, bagCount;
  vector<int> localAt;  // tripod -> vertex of K of its component
  // For each child component: its face (in parentFaces of its parent
  // component), its owner, and the owner's bottom, middle and top vertices.
  vector<int> childFace, childOwner;
  vector<array<int, 3>> childRoles;
  int ownedBy[4] = {0, 0, 0, 0};
  vector<int> bagRank, podRank;
  QuotientOrder result;
};

QuotientOrder buildQuotientOrder(
    const RawTripodQuotient& raw,
    const TreePartition& tp,
    const vector<vector<ParentFace>>& parentFaces,
    const vector<LevelK>& Ks,
    const vector<vector<int>>& rankK,
    const vector<RawIntervals>& intervalsByPod,
    int verbose) {
  return QuotientOrderBuilder(raw, tp, parentFaces, Ks, rankK, intervalsByPod, verbose).build();
}

// Order the ports of each tripod (tripod reordering) when reorder is set;
// otherwise keep a fixed order. Then check the order of the child components
// around each tripod and that each quotient queue expands to at most
// expandedBound queues.
class PortOrderBuilder {
 public:
  PortOrderBuilder(
      const LayeredHPartition& lhp,
      const RawTripodQuotient& raw,
      const TreePartition& tp,
      const vector<RawIntervals>& intervalsByPod,
      const QuotientOrder& quotientOrder,
      bool reorder,
      int expandedBound)
      : lhp(lhp), raw(raw), tp(tp), intervalsByPod(intervalsByPod),
        quotientOrder(quotientOrder), reorder(reorder), expandedBound(expandedBound),
        podCount((int)lhp.pods.size()), pathOrder(podCount),
        fullIntervalSide(podCount, -1), pathsInSweep(podCount, {-1, -1, -1}) {
    CHECK((int)intervalsByPod.size() == podCount);
  }

  vector<vector<int>> build() {
    choosePortOrders();
    verifyLevelEdgesMissAPort();
    verifyChildGroups();
    verifyExpandedQuotient();
    return std::move(pathOrder);
  }

 private:
  // If one interval at a tripod meets all three ports, name them a, b, c by
  // their first incidences in its reading and order them b, a, c.
  void choosePortOrders() {
    for (int pod = 0; pod < podCount; pod++) {
      const int pathCount = lhp.pods[pod].numPaths();
      CHECK(1 <= pathCount && pathCount <= 3);
      const auto& rotation = raw.clockwiseRotation[pod];
      const auto& intervals = intervalsByPod[pod];
      int topMask = 0, bottomMask = 0;
      for (int pos = 0; pos < (int)rotation.size(); pos++) {
        CHECK(0 <= rotation[pos].pathId &&
              rotation[pos].pathId < pathCount);
        if (!intervals.inContext[pos]) continue;
        if (intervals.incidenceInTop[pos]) {
          topMask |= 1 << rotation[pos].pathId;
        } else {
          bottomMask |= 1 << rotation[pos].pathId;
        }
      }
      if (pathCount == 3 && reorder) {
        CHECK(!(topMask == 7 && bottomMask == 7),
              "both local intervals touch all three paths of tripod %d",
              pod);
        if (topMask == 7) fullIntervalSide[pod] = 0;
        if (bottomMask == 7) fullIntervalSide[pod] = 1;
      }
      if (fullIntervalSide[pod] < 0) {
        for (int path = 0; path < pathCount; path++) {
          pathOrder[pod].push_back(path);
        }
        continue;
      }
      const bool useTop = fullIntervalSide[pod] == 0;
      int pathMask = 0, named = 0;
      int lastAt[3] = {-1, -1, -1};
      int firstAt[3] = {-1, -1, -1};
      int rank = 0;
      for (int step = 0; step < (int)rotation.size(); step++) {
        const int pos = useTop
            ? (intervals.leftCutBefore + step) % rotation.size()
            : (intervals.leftCutBefore + (int)rotation.size() - 1 - step) %
                  rotation.size();
        if (!intervals.inContext[pos] || intervals.incidenceInTop[pos] != useTop) {
          continue;
        }
        const int path = rotation[pos].pathId;
        if (!(pathMask & (1 << path))) {
          CHECK(named < 3);
          pathsInSweep[pod][named++] = path;
          firstAt[path] = rank;
          pathMask |= 1 << path;
        }
        lastAt[path] = rank++;
      }
      CHECK(named == 3 && pathMask == 7);
      const int a = pathsInSweep[pod][0];
      const int b = pathsInSweep[pod][1];
      const int c = pathsInSweep[pod][2];
      CHECK(lastAt[b] < firstAt[c],
            "path b does not precede path c in the chosen interval at tripod %d",
            pod);
      pathOrder[pod] = {b, a, c};
    }
  }

  // Edges between two tripods of one level use at most two ports of the
  // earlier-created one.
  void verifyLevelEdgesMissAPort() {
    map<EdgeTy, int> earlierSupportPaths;
    for (const auto& record : raw.edges) {
      const int u = record.endpointPod[0];
      const int v = record.endpointPod[1];
      if (u == v || tp.vertex2depth[u] != tp.vertex2depth[v]) {
        continue;
      }
      const int earlier = std::min(u, v);
      const int endpoint = u == earlier ? 0 : 1;
      earlierSupportPaths[make_edge(u, v)] |=
          1 << record.endpointPath[endpoint];
    }
    for (const auto& [support, mask] : earlierSupportPaths) {
      CHECK(__builtin_popcount((unsigned)mask) <= 2,
            "same-level support (%d,%d) touches all three paths of "
            "its earlier-created tripod",
            support.first, support.second);
    }
  }

  // Around a tripod whose ports are named a, b, c, the child components of
  // each binding queue come in three groups, touching only {a, b}, {b, c},
  // and {c, a}, in this order.
  void verifyChildGroups() {
    vector<int> bagRank(tp.numBags, -1);
    for (int i = 0; i < (int)quotientOrder.bagOrder.size(); i++) {
      bagRank[quotientOrder.bagOrder[i]] = i;
    }
    for (int pod = 0; pod < podCount; pod++) {
      if (fullIntervalSide[pod] < 0) continue;
      const int a = pathsInSweep[pod][0];
      const int b = pathsInSweep[pod][1];
      const int c = pathsInSweep[pod][2];
      const int allowedPaths[3] = {
          (1 << a) | (1 << b),
          (1 << b) | (1 << c),
          (1 << c) | (1 << a)};
      const int qStart = fullIntervalSide[pod] == 0 ? 2 : 3;
      const int qStop = fullIntervalSide[pod] == 0 ? 3 : 5;
      for (int q = qStart; q < qStop; q++) {
        map<int, int> childPaths;
        for (int pos = 0;
             pos < (int)raw.clockwiseRotation[pod].size(); pos++) {
          const auto& incidence = raw.clockwiseRotation[pod][pos];
          const int e = raw.edgeIndex.at(incidence.originalEdge);
          if (quotientOrder.rawEdgeQueue[e] != q) continue;
          const auto& record = raw.edges[e];
          const int other = record.endpointPod[1 - incidence.endpoint];
          if (tp.vertex2depth[other] != tp.vertex2depth[pod] + 1) {
            continue;  // Only outgoing bindings have u as their source.
          }
          childPaths[tp.vertex2bag[other]] |= 1 << incidence.pathId;
        }
        vector<int> children;
        for (const auto& [child, mask] : childPaths) {
          CHECK(mask > 0 && __builtin_popcount((unsigned)mask) <= 2);
          CHECK(bagRank[child] >= 0);
          children.push_back(child);
        }
        std::sort(children.begin(), children.end(), [&](int x, int y) {
          return bagRank[x] < bagRank[y];
        });
        int phase = 0;
        for (int child : children) {
          const int mask = childPaths.at(child);
          while (phase < 3 && (mask & ~allowedPaths[phase]) != 0) {
            phase++;
          }
          CHECK(phase < 3,
                "Q%d children around tripod %d violate the ab,bc,ac order "
                "at child component %d",
                q, pod, child);
        }
      }
    }
  }

  // After replacing each tripod by its ordered ports, no quotient queue
  // contains a rainbow longer than expandedBound.
  void verifyExpandedQuotient() {
    vector<int> expandedOrder;
    for (int pod : quotientOrder.podOrder) {
      for (int path : pathOrder[pod]) expandedOrder.push_back(3 * pod + path);
    }
    // Include unused port IDs as isolated vertices at the end of the order.
    for (int pod : quotientOrder.podOrder) {
      for (int path = lhp.pods[pod].numPaths(); path < 3; path++) {
        expandedOrder.push_back(3 * pod + path);
      }
    }
    std::array<vector<EdgeTy>, 5> expandedEdges;
    for (int e = 0; e < (int)raw.edges.size(); e++) {
      const int q = quotientOrder.rawEdgeQueue[e];
      if (q < 0) continue;
      const auto& edge = raw.edges[e];
      expandedEdges[q].push_back(make_edge(
          3 * edge.endpointPod[0] + edge.endpointPath[0],
          3 * edge.endpointPod[1] + edge.endpointPath[1]));
    }
    vector<EdgeTy> allExpanded;
    for (int q = 0; q < 5; q++) {
      allExpanded.insert(allExpanded.end(), expandedEdges[q].begin(), expandedEdges[q].end());
    }
    CHECK(countRainbow(allExpanded, expandedOrder) <= 5 * expandedBound,
          "the expanded quotient needs more than %d queues", 5 * expandedBound);
    for (int q = 0; q < 5; q++) {
      CHECK(countRainbow(expandedEdges[q], expandedOrder) <= expandedBound,
            "expanded quotient Q%d needs more than %d queues", q, expandedBound);
    }
  }

  const LayeredHPartition& lhp;
  const RawTripodQuotient& raw;
  const TreePartition& tp;
  const vector<RawIntervals>& intervalsByPod;
  const QuotientOrder& quotientOrder;
  const bool reorder;
  const int expandedBound;
  const int podCount;
  vector<vector<int>> pathOrder;
  vector<int> fullIntervalSide;  // 0 = I_t, 1 = I_mb, -1 = no full interval
  vector<array<int, 3>> pathsInSweep;  // the ports a, b, c
};

vector<vector<int>> buildPathOrderAndCheckPhases(
    const LayeredHPartition& lhp,
    const RawTripodQuotient& raw,
    const TreePartition& tp,
    const vector<RawIntervals>& intervalsByPod,
    const QuotientOrder& quotientOrder,
    bool reorder,
    int expandedBound) {
  return PortOrderBuilder(lhp, raw, tp, intervalsByPod, quotientOrder, reorder, expandedBound).build();
}

// The queues of the layout of G. The vertex order lists the
// BFS layers; within a layer the tripods in the quotient order and their
// vertices in the port order. Intra-bag edges: one queue for intra-layer
// edges and two for inter-layer edges. Inter-bag edges
// follow the product construction with a path on the expanded quotient: each
// edge of the expanded quotient gets one of its queues (each quotient queue
// splits into `split` queues, as no rainbow in it is longer), and an
// inter-bag edge of G uses
// that queue together with its type: intra-layer, inter-layer forward, or
// inter-layer backward (in the order of the quotient). Returns a queue for
// every edge.
class QueueAssignment {
 public:
  QueueAssignment(
      const LayeredHPartition& lhp,
      const vector<EdgeTy>& allEdges,
      const vector<int>& order,
      const vector<int>& podOrder,
      const vector<vector<int>>& pathOrder,
      const vector<int>& edgeQuotientQueue,
      int queueBound)
      : n(lhp.n), verbose(lhp.verbose), layer(lhp.layer), pods(lhp.pods),
        vertex2pod(lhp.vertex2pod), vertex2path(lhp.vertex2path),
        allEdges(allEdges), order(order), podOrder(podOrder), pathOrder(pathOrder),
        edgeQuotientQueue(edgeQuotientQueue), queueBound(queueBound),
        split(queueBound == 33 ? 2 : 3) {
    CHECK(queueBound == 48 || queueBound == 33);
    CHECK(intraBound + 3 * 5 * split == queueBound);
    CHECK((int)order.size() == n && (int)layer.size() == n &&
          (int)vertex2pod.size() == n && (int)vertex2path.size() == n);
    CHECK(podOrder.size() == pods.size() && pathOrder.size() == pods.size());
    CHECK(edgeQuotientQueue.size() == allEdges.size());
  }

  vector<int> build() {
    verifyVertexOrder();
    buildPortOrder();
    classifyEdges();
    splitExpandedQuotient();
    assignIntraBagEdges();
    assignInterBagEdges();
    verify();
    return std::move(assigned);
  }

 private:
  static constexpr int intraLayerBound = 1, interLayerBound = 2;
  static constexpr int intraBound = intraLayerBound + interLayerBound;
  static constexpr const char* kTypeName[5] = {
      "intra-bag/intra-layer", "intra-bag/inter-layer", "inter-bag/intra-layer",
      "inter-bag/forward", "inter-bag/backward"};

  int port(int v) const { return 3 * vertex2pod[v] + vertex2path[v]; }

  // The order lists the BFS layers; within a layer the tripods in the
  // quotient order, and the vertices of a tripod in its port order.
  void verifyVertexOrder() {
    podRank.assign(pods.size(), -1);
    pathRank.assign(pods.size(), {-1, -1, -1});
    for (int i = 0; i < (int)podOrder.size(); i++) {
      const int pod = podOrder[i];
      CHECK(0 <= pod && pod < (int)pods.size() && podRank[pod] == -1);
      podRank[pod] = i;
      CHECK((int)pathOrder[pod].size() == pods[pod].numPaths());
      for (int j = 0; j < (int)pathOrder[pod].size(); j++) {
        const int path = pathOrder[pod][j];
        CHECK(0 <= path && path < pods[pod].numPaths() &&
              pathRank[pod][path] == -1);
        pathRank[pod][path] = j;
      }
    }
    vector<int> position(n, -1);
    for (int i = 0; i < n; i++) {
      const int v = order[i];
      CHECK(0 <= v && v < n && position[v] == -1);
      position[v] = i;
      const int pod = vertex2pod[v], path = vertex2path[v];
      CHECK(0 <= pod && pod < (int)pods.size() &&
            0 <= path && path < 3 && pathRank[pod][path] >= 0 &&
            layer[v] >= 0);
      if (i == 0) continue;
      const int u = order[i - 1];
      CHECK(layer[u] <= layer[v], "vertex order is not BFS-layer major");
      if (layer[u] != layer[v]) continue;
      CHECK(podRank[vertex2pod[u]] <= podRank[pod],
            "vertex order reverses two tripod blocks on one BFS layer");
      if (vertex2pod[u] == pod) {
        CHECK(pathRank[pod][vertex2path[u]] < pathRank[pod][path],
              "tripod %d changes path order or repeats a path on one BFS layer",
              pod);
      }
    }
  }

  // The expanded quotient: one vertex per port, in the port order.
  void buildPortOrder() {
    for (int pod : podOrder) {
      for (int path : pathOrder[pod]) portOrder.push_back(3 * pod + path);
    }
    for (int pod : podOrder) {
      for (int path = pods[pod].numPaths(); path < 3; path++) portOrder.push_back(3 * pod + path);
    }
  }

  // The type of each edge of G, and the quotient queue of each inter-bag edge.
  void classifyEdges() {
    type.assign(allEdges.size(), -1);
    quotientQueueOf.assign(allEdges.size(), -1);
    map<EdgeTy, int> quotientQueue;
    for (int i = 0; i < (int)allEdges.size(); i++) {
      auto [u, v] = allEdges[i];
      CHECK(0 <= u && u < n && 0 <= v && v < n && u != v);
      CHECK(std::abs(layer[u] - layer[v]) <= 1,
            "edge (%d,%d) skips a BFS layer", u, v);
      if (layer[u] > layer[v]) std::swap(u, v);
      const int podU = vertex2pod[u], podV = vertex2pod[v];
      if (podU == podV) {
        CHECK(edgeQuotientQueue[i] == -1,
              "intra-bag edge was assigned a quotient queue");
        type[i] = layer[u] == layer[v] ? 0 : 1;
      } else {
        const int q = edgeQuotientQueue[i];
        CHECK(0 <= q && q < 5);
        quotientQueueOf[i] = q;
        type[i] = layer[u] == layer[v] ? 2 :
            (podRank[podU] < podRank[podV] ? 3 : 4);
        const EdgeTy pair = make_edge(podU, podV);
        const auto [it, inserted] = quotientQueue.emplace(pair, q);
        CHECK(inserted || it->second == q,
              "one quotient edge is assigned different queues");
        if (inserted) quotientEdges[q].push_back(pair);
        expandedQueue[q].emplace(make_edge(port(u), port(v)), -1);
      }
      typeEdges[type[i]].push_back(allEdges[i]);
    }
    for (int q = 0; q < 5; q++) {
      CHECK(countRainbow(quotientEdges[q], podOrder) <= 1,
            "quotient Q%d contains nested independent edges", q);
    }
  }

  // The queues of the expanded quotient: each quotient queue has no rainbow
  // longer than split, so it splits into split queues.
  void splitExpandedQuotient() {
    for (int q = 0; q < 5; q++) {
      vector<EdgeTy> pairs;
      for (const auto& [pair, unused] : expandedQueue[q]) pairs.push_back(pair);
      const auto parts = colorQueueEdges(pairs, portOrder);
      for (int j = 0; j < (int)pairs.size(); j++) {
        CHECK(0 <= parts[j] && parts[j] < split,
              "quotient Q%d needs more than %d queues of the expanded quotient", q, split);
        expandedQueue[q][pairs[j]] = parts[j];
      }
    }
  }

  // Color intra-bag edges by nesting depth. Within a layer, each bag has at
  // most three consecutive vertices. Between consecutive layers, the fixed
  // path order and planarity exclude three independent nested edges. The
  // resulting limits are one intra-layer queue and two inter-layer queues.
  void assignIntraBagEdges() {
    assigned.assign(allEdges.size(), -1);
    for (int t = 0; t < 2; t++) {
      vector<int> indices;
      vector<EdgeTy> edges;
      for (int i = 0; i < (int)allEdges.size(); i++) {
        if (type[i] == t) {
          indices.push_back(i);
          edges.push_back(allEdges[i]);
        }
      }
      const int limit = t == 0 ? intraLayerBound : interLayerBound;
      const auto colors = colorQueueEdges(edges, order);
      for (int j = 0; j < (int)edges.size(); j++) {
        CHECK(0 <= colors[j] && colors[j] < limit,
              "%s edges need more than %d queues", kTypeName[t], limit);
        assigned[indices[j]] = (t == 0 ? 0 : intraLayerBound) + colors[j];
      }
    }
  }

  // An inter-bag edge: (queue of the expanded quotient, type).
  void assignInterBagEdges() {
    for (int i = 0; i < (int)allEdges.size(); i++) {
      if (type[i] < 2) continue;
      auto [u, v] = allEdges[i];
      const int q = quotientQueueOf[i];
      const int part = expandedQueue[q].at(make_edge(port(u), port(v)));
      assigned[i] = intraBound + 3 * (split * q + part) + (type[i] - 2);
    }
  }

  // No queue contains two nested edges, and every type stays in its budget.
  void verify() {
    vector<vector<EdgeTy>> queues(queueBound);
    array<set<int>, 5> typeQueues;
    map<pair<int, int>, set<int>> familyQueues;  // (type, quotient queue)
    map<pair<int, int>, int> familySize;
    for (int i = 0; i < (int)allEdges.size(); i++) {
      CHECK(0 <= assigned[i] && assigned[i] < queueBound, "queue assignment omits an edge");
      queues[assigned[i]].push_back(allEdges[i]);
      typeQueues[type[i]].insert(assigned[i]);
      if (type[i] >= 2) {
        familyQueues[{type[i], quotientQueueOf[i]}].insert(assigned[i]);
        familySize[{type[i], quotientQueueOf[i]}]++;
      }
    }
    for (int queue = 0; queue < queueBound; queue++) {
      CHECK(countRainbow(queues[queue], order) <= 1,
            "assigned queue %d contains nested independent edges", queue);
    }
    for (int t = 2; t < 5; t++) {
      for (int q = 0; q < 5; q++) {
        const int used = familyQueues.count({t, q}) ? (int)familyQueues.at({t, q}).size() : 0;
        CHECK(used <= split);
        LOG_IF(verbose,
               "queue family: bound=%d type=%s quotient=Q%d edges=%d queues=%d limit=%d",
               queueBound, kTypeName[t], q,
               familySize.count({t, q}) ? familySize.at({t, q}) : 0, used, split);
      }
    }
    const array<int, 5> typeBounds =
        {intraLayerBound, interLayerBound, 5 * split, 5 * split, 5 * split};
    int usedTotal = 0;
    set<int> allUsed;
    for (int t = 0; t < 5; t++) {
      CHECK((int)typeQueues[t].size() <= typeBounds[t],
            "%s edges use too many queues", kTypeName[t]);
      for (int queue : typeQueues[t]) {
        CHECK(allUsed.insert(queue).second, "two edge types share a queue");
      }
      usedTotal += (int)typeQueues[t].size();
    }
    CHECK(usedTotal <= queueBound);
    CHECK(countRainbow(allEdges, order) <= queueBound);
    LOG_IF(verbose,
           "queue allocation: bound=%d %s=%d/%d %s=%d/%d %s=%d/%d %s=%d/%d %s=%d/%d total=%d/%d",
           queueBound,
           kTypeName[0], (int)typeQueues[0].size(), typeBounds[0],
           kTypeName[1], (int)typeQueues[1].size(), typeBounds[1],
           kTypeName[2], (int)typeQueues[2].size(), typeBounds[2],
           kTypeName[3], (int)typeQueues[3].size(), typeBounds[3],
           kTypeName[4], (int)typeQueues[4].size(), typeBounds[4], usedTotal, queueBound);
  }

  const int n, verbose;
  const vector<int>& layer;
  const vector<LayeredHPartition::Pod>& pods;
  const vector<int>& vertex2pod;
  const vector<int>& vertex2path;
  const vector<EdgeTy>& allEdges;
  const vector<int>& order;
  const vector<int>& podOrder;
  const vector<vector<int>>& pathOrder;
  const vector<int>& edgeQuotientQueue;
  const int queueBound, split;
  vector<int> podRank;
  vector<array<int, 3>> pathRank;
  vector<int> portOrder;
  vector<int> type, quotientQueueOf;
  array<vector<EdgeTy>, 5> typeEdges;
  array<vector<EdgeTy>, 5> quotientEdges;
  array<map<EdgeTy, int>, 5> expandedQueue;  // per quotient queue: port pair -> part
  vector<int> assigned;
};

struct PPSLayout {
  vector<int> fullOrder;
  map<Edge*, int> fullEdgeQueue;
  vector<int> originalOrder;
  map<EdgeTy, int> originalEdgeQueue;
};

PPSLayout buildOriginalLayout(
    const LayeredHPartition& lhp,
    const PlanarGraph& graph,
    const RawTripodQuotient& raw,
    const QuotientOrder& quotientOrder,
    const vector<vector<int>>& pathOrder,
    int queueBound,
    int originalVertexCount,
    const vector<Edge*>& inputEdges) {
  CHECK(0 < originalVertexCount &&
        originalVertexCount < graph.numberOfVertices());
  const int podCount = (int)lhp.pods.size();
  CHECK((int)pathOrder.size() == podCount);
  CHECK((int)quotientOrder.podOrder.size() == podCount);
  PPSLayout result;
  vector<int> podRank(podCount, -1);
  for (int i = 0; i < podCount; i++) {
    const int pod = quotientOrder.podOrder[i];
    CHECK(0 <= pod && pod < podCount && podRank[pod] == -1);
    podRank[pod] = i;
    const auto& paths = lhp.pods[pod];
    CHECK((int)pathOrder[pod].size() == paths.numPaths());
    vector<bool> seenPath(paths.numPaths(), false);
    for (int path : pathOrder[pod]) {
      CHECK(0 <= path && path < paths.numPaths() && !seenPath[path]);
      seenPath[path] = true;
      for (int v : paths.paths[path]) {
        CHECK(lhp.vertex2pod[v] == pod &&
              lhp.vertex2path[v] == path);
        result.fullOrder.push_back(v);
      }
    }
  }
  CHECK(result.fullOrder.size() == graph.vertices.size());
  std::stable_sort(
      result.fullOrder.begin(), result.fullOrder.end(),
      [&](int u, int v) { return lhp.layer[u] < lhp.layer[v]; });
  const auto allEdges = graph.extractEdges();
  vector<EdgeTy> endpoints;
  vector<int> edgeQuotientQueue;
  for (Edge* edge : allEdges) {
    const int u = edge->source->index;
    const int v = edge->target->index;
    endpoints.push_back({u, v});
    const int podU = lhp.vertex2pod[u];
    const int podV = lhp.vertex2pod[v];
    if (podU == podV) {
      if (!raw.edgeIndex.count(edge)) {
        CHECK(lhp.isBFSTreeEdge(u, v) &&
              lhp.vertex2path[u] == lhp.vertex2path[v],
              "unretained original edge (%d,%d) is not a vertical path edge",
              u, v);
      }
      edgeQuotientQueue.push_back(-1);
      continue;
    }
    CHECK(raw.edgeIndex.count(edge));
    const int rawId = raw.edgeIndex.at(edge);
    edgeQuotientQueue.push_back(quotientOrder.rawEdgeQueue[rawId]);
  }
  const auto assigned = QueueAssignment(
      lhp, endpoints, result.fullOrder, quotientOrder.podOrder, pathOrder,
      edgeQuotientQueue, queueBound).build();
  CHECK(assigned.size() == allEdges.size());
  for (int i = 0; i < (int)allEdges.size(); i++) {
    CHECK(result.fullEdgeQueue.emplace(allEdges[i], assigned[i]).second);
  }
  CHECK(result.fullEdgeQueue.size() == allEdges.size(),
        "queue assignment omits an edge of the triangulated supergraph");

  for (int v : result.fullOrder) {
    if (v < originalVertexCount) {
      result.originalOrder.push_back(v);
    }
  }
  CHECK((int)result.originalOrder.size() == originalVertexCount);
  set<Edge*> allEdgePointers(allEdges.begin(), allEdges.end());
  for (Edge* edge : inputEdges) {
    CHECK(allEdgePointers.count(edge) &&
          result.fullEdgeQueue.count(edge),
          "input edge did not survive triangulation and root insertion");
    const int u = edge->source->index;
    const int v = edge->target->index;
    CHECK(u < originalVertexCount && v < originalVertexCount,
          "input edge acquired an auxiliary endpoint");
    CHECK(result.originalEdgeQueue.emplace(
              make_edge(u, v), result.fullEdgeQueue.at(edge)).second,
          "input planar graph has parallel edges (%d,%d)", u, v);
  }
  CHECK(result.originalEdgeQueue.size() == inputEdges.size(),
        "restriction does not cover every input edge exactly once");
  vector<vector<EdgeTy>> restrictedQueues(queueBound);
  for (const auto& [edge, q] : result.originalEdgeQueue) {
    CHECK(0 <= q && q < queueBound);
    restrictedQueues[q].push_back(edge);
  }
  for (int q = 0; q < queueBound; q++) {
    CHECK(countRainbow(restrictedQueues[q], result.originalOrder) <= 1,
          "restricted input queue %d contains nested independent edges",
          q);
  }
  return result;
}

}  // namespace

// Each tripod other than the initial ones has as earlier neighbors exactly
// the tripods on the boundary of the region where it was created, and they
// are pairwise adjacent.
void verifyBoundaryParents(const LayeredHPartition& lhp, const RawTripodQuotient& rawQuotient) {
  const RawTripodQuotient* raw = &rawQuotient;
  const int podCount = (int)lhp.pods.size();
  CHECK(podCount >= 3);
  CHECK((int)lhp.podBoundaryParents.size() == podCount);
  for (int pod = 0; pod < podCount; pod++) {
    vector<int> boundaryParents = lhp.podBoundaryParents[pod];
    std::sort(boundaryParents.begin(), boundaryParents.end());
    CHECK(std::adjacent_find(boundaryParents.begin(),
                             boundaryParents.end()) ==
          boundaryParents.end(),
          "tripod %d has repeated boundary parents", pod);
    vector<int> earlierNeighbors;
    raw->simplePodAdj.forEach(pod, [&](int neighbor) {
      if (neighbor < pod) earlierNeighbors.push_back(neighbor);
    });
    std::sort(earlierNeighbors.begin(), earlierNeighbors.end());
    if (pod < 3) {
      CHECK(boundaryParents.empty());
      continue;
    }
    CHECK(!boundaryParents.empty() && boundaryParents.size() <= 3,
          "new tripod %d has %d boundary parents",
          pod, (int)boundaryParents.size());
    CHECK(earlierNeighbors == boundaryParents,
          "earlier neighbors of tripod %d differ from its boundary tripods",
          pod);
    for (int u : earlierNeighbors) {
      for (int v : earlierNeighbors) {
        CHECK(u == v || raw->simplePodAdj.test(u, v),
              "earlier neighbors %d,%d of tripod %d are not adjacent",
              u, v, pod);
      }
    }
  }
  for (int u = 0; u < 3; u++) {
    for (int v = u + 1; v < 3; v++) {
      CHECK(raw->simplePodAdj.test(u, v),
            "initial tripod vertices %d and %d are not adjacent", u, v);
    }
  }
}

// Levels and parents of the level components of the quotient: every edge
// joins equal or consecutive levels, and the parents of a level component are
// pairwise adjacent tripods of one component of the preceding level.
void verifyLevelComponents(const RawTripodQuotient& rawQuotient, const TreePartition& tp) {
  const RawTripodQuotient* raw = &rawQuotient;
  const int podCount = (int)raw->clockwiseRotation.size();
  CHECK((int)tp.vertex2depth.size() == podCount);
  CHECK((int)tp.vertex2bag.size() == podCount);
  CHECK((int)tp.bag2parents.size() == tp.numBags);
  CHECK(tp.vertex2bag[0] == tp.vertex2bag[1] &&
        tp.vertex2bag[1] == tp.vertex2bag[2]);

  for (int u = 0; u < podCount; u++) {
    CHECK(tp.vertex2depth[u] >= 0 && tp.vertex2bag[u] >= 0,
          "tripod %d is missing from a quotient level/component", u);
    if (u >= 3) {
      bool hasPrecedingLevelNeighbor = false;
      raw->simplePodAdj.forEach(u, [&](int v) {
        if (tp.vertex2depth[v] == tp.vertex2depth[u] - 1) {
          hasPrecedingLevelNeighbor = true;
        }
      });
      CHECK(hasPrecedingLevelNeighbor,
            "noninitial tripod %d has no preceding-level neighbor", u);
    }
    raw->simplePodAdj.forEach(u, [&](int v) {
      CHECK(std::abs(tp.vertex2depth[u] - tp.vertex2depth[v]) <= 1,
            "quotient edge (%d,%d) skips a level", u, v);
    });
  }

  for (int bagId = 0; bagId < tp.numBags; bagId++) {
    const auto& component = tp.bags[bagId];
    const auto& parents = tp.bag2parents[bagId];
    const int depth = tp.bag2depth[bagId];
    CHECK(!component.empty());
    if (depth == 0) {
      CHECK(parents.empty(), "initial level component has parents");
      continue;
    }
    CHECK(!parents.empty() && parents.size() <= 3,
          "next-level component %d has %d parents", bagId, (int)parents.size());
    const int firstPod = *std::min_element(component.begin(), component.end());
    vector<int> earlierNeighbors;
    raw->simplePodAdj.forEach(firstPod, [&](int v) {
      if (v < firstPod) {
        earlierNeighbors.push_back(v);
      }
    });
    std::sort(earlierNeighbors.begin(), earlierNeighbors.end());
    CHECK(earlierNeighbors == parents,
          "component %d parents differ from earlier neighbors of tripod %d",
          bagId, firstPod);
    const int parentBag = tp.vertex2bag[parents[0]];
    for (int parent : parents) {
      CHECK(tp.vertex2depth[parent] == depth - 1 &&
            tp.vertex2bag[parent] == parentBag,
            "component %d parents are not in one preceding-level component", bagId);
      for (int other : parents) {
        CHECK(parent == other || raw->simplePodAdj.test(parent, other),
              "component %d has nonadjacent parents %d and %d",
              bagId, parent, other);
      }
    }
  }
}

// The graph K of every level component, with all faces of each component in
// triangles of K. Also returns the faces of each component (parentFaces) and
// the order of the vertices of each K (rankK).
vector<LevelK> buildLevelKs(
    const LayeredHPartition& lhp,
    const RawTripodQuotient& rawQuotient,
    const RawQuotientFaces& rawFaces,
    const TreePartition& tp,
    const PlanarGraph& graph,
    const vector<RawRotationAtoms>& rotationAtoms,
    vector<vector<ParentFace>>& parentFaces,
    vector<vector<int>>& rankK,
    int verbose) {
  const RawTripodQuotient* raw = &rawQuotient;
  vector<vector<int>> supportEdgesByBag(tp.numBags);
  for (int e = 0; e < (int)raw->edges.size(); e++) {
    const int u = raw->edges[e].endpointPod[0];
    const int v = raw->edges[e].endpointPod[1];
    if (u != v && tp.vertex2bag[u] == tp.vertex2bag[v]) {
      CHECK(tp.vertex2depth[u] == tp.vertex2depth[v],
            "support copy (%d,%d) joins different levels", u, v);
      supportEdgesByBag[tp.vertex2bag[u]].push_back(e);
    }
  }
  vector<int> initialOuterPodCycle;
  for (Vertex* v : graph.outerFace.vertices) {
    initialOuterPodCycle.push_back(lhp.vertex2pod[v->index]);
  }
  CHECK(initialOuterPodCycle.size() == 3);
  vector<LevelK> levelKs;
  levelKs.reserve(tp.numBags);
  for (int bagId = 0; bagId < tp.numBags; bagId++) {
    levelKs.push_back(buildLevelK(*raw, tp, bagId, supportEdgesByBag[bagId],
                                  initialOuterPodCycle, rotationAtoms, verbose));
  }
  verifyChildLocations(lhp, *raw, tp, rotationAtoms);
  verifyBoundedChildRegions(*raw, rawFaces, tp, graph);
  parentFaces = verifyParentFaceChildBijection(*raw, rawFaces, tp, graph);
  rankK.assign(tp.numBags, {});
  int designated = 0, reused = 0, added = 0;
  for (int bagId = 0; bagId < tp.numBags; bagId++) {
    wrapOuterFaces(levelKs[bagId], parentFaces[bagId]);
    rankK[bagId] = verifyLevelKDrawing(levelKs[bagId], bagId);
    designated += levelKs[bagId].designatedTriangles;
    reused += levelKs[bagId].wrapReused;
    added += levelKs[bagId].wrapAdded;
  }
  LOG_IF(verbose, "auxiliary triangles of K: designated-side=%d wrap-reused=%d wrap-added=%d",
         designated, reused, added);
  return levelKs;
}

// The 33-queue construction (queueBound 33) and the same construction
// with a fixed order of the vertical paths in every tripod (queueBound 48).
static PPSLayout runPPSPipeline(
    PlanarGraph& graph,
    int verbose,
    int queueBound,
    int inputVertexCount,
    const vector<Edge*>& inputEdges) {
  CHECK(queueBound == 33 || queueBound == 48);
  CHECK(graph.isMaximal());
  CHECK(graph.outerFace.length() == 3);
  const int beforeRootVertexCount = graph.numberOfVertices();
  Vertex* root = addOuterBFSRoot(graph);
  CHECK(root != nullptr && root->index == beforeRootVertexCount);

  LayeredHPartition lhp(graph.numberOfVertices(), verbose);
  lhp.init(graph, root->index);
  lhp.build(graph);
  lhp.verify();

  const auto raw = extractRawTripodQuotient(lhp, graph);
  CHECK(raw != nullptr);
  CHECK(raw->clockwiseRotation.size() == lhp.pods.size());
  CHECK(raw->simplePodAdj.size() == lhp.pods.size());
  const RawQuotientFaces rawFaces = buildRawQuotientFaces(*raw);
  CHECK(!rawFaces.faceDarts.empty());

  const int podCount = (int)lhp.pods.size();
  verifyBoundaryParents(lhp, *raw);
  TreePartition tp(verbose);
  tp.build(raw->simplePodAdj, {0, 1, 2});
  verifyImmediateRecursiveRegions(lhp, *raw, tp);
  verifyLevelComponents(*raw, tp);
  vector<RawRotationAtoms> rotationAtoms;
  rotationAtoms.reserve(podCount);
  for (int pod = 0; pod < podCount; pod++) {
    rotationAtoms.push_back(partitionRawRotation(*raw, tp, pod));
    CHECK(rotationAtoms.back().classPod.size() ==
          raw->clockwiseRotation[pod].size());
  }

  vector<vector<ParentFace>> parentFaces;
  vector<vector<int>> rankK;
  const vector<LevelK> levelKs = buildLevelKs(
      lhp, *raw, rawFaces, tp, graph, rotationAtoms, parentFaces, rankK, verbose);
  vector<RawIntervals> intervalsByPod(podCount);
  for (int bagId = 0; bagId < tp.numBags; bagId++) {
    for (int local = 0; local < levelKs[bagId].numReal; local++) {
      intervalsByPod[levelKs[bagId].podIds[local]] =
          buildIntervals(levelKs[bagId], local, *raw, tp);
    }
  }
  const QuotientOrder quotientOrder = buildQuotientOrder(
      *raw, tp, parentFaces, levelKs, rankK, intervalsByPod, verbose);
  CHECK(quotientOrder.podOrder.size() == lhp.pods.size());
  CHECK(quotientOrder.rawEdgeQueue.size() == raw->edges.size());
  const bool reorder = queueBound == 33;
  const auto pathOrder = buildPathOrderAndCheckPhases(
      lhp, *raw, tp, intervalsByPod, quotientOrder, reorder, reorder ? 2 : 3);
  CHECK(pathOrder.size() == lhp.pods.size());
  LOG_IF(verbose, "verified quotient stage: %d pods, %d retained edges, %d faces, %d level components",
         (int)lhp.pods.size(), (int)raw->edges.size(),
         (int)rawFaces.faceDarts.size(), tp.numBags);
  PPSLayout layout = buildOriginalLayout(
      lhp, graph, *raw, quotientOrder, pathOrder, queueBound,
      inputVertexCount, inputEdges);
  LOG_IF(verbose, "verified %d-queue layout: %d input vertices, %d input edges",
         queueBound, (int)layout.originalOrder.size(),
         (int)layout.originalEdgeQueue.size());
  return layout;
}

// A graph on at most two vertices: any order and one queue.
static void layoutTinyGraph(
    const PlanarGraph& graph,
    const vector<Edge*>& inputEdges,
    vector<int>& resultOrder,
    map<EdgeTy, int>& resultEdgeQueue) {
  const int inputVertexCount = graph.numberOfVertices();
  CHECK(inputEdges.size() <= 1,
        "a simple graph on at most two vertices has too many edges");
  for (int v = 0; v < inputVertexCount; v++) {
    CHECK(graph.vertices[v]->index == v);
    resultOrder.push_back(v);
  }
  for (Edge* edge : inputEdges) {
    const EdgeTy pair = make_edge(
        edge->source->index, edge->target->index);
    CHECK(pair.first != pair.second &&
          0 <= pair.first && pair.second < inputVertexCount);
    CHECK(resultEdgeQueue.emplace(pair, 0).second);
  }
  CHECK(countRainbow(
            inputEdges.empty() ? vector<EdgeTy>() :
                vector<EdgeTy>{resultEdgeQueue.begin()->first},
            resultOrder) <= 1);
}

// A disconnected input: lay out each connected component and concatenate the
// orders. Returns false for a connected input.
static bool layoutComponentsSeparately(
    PlanarGraph& graph,
    int queueBound,
    const vector<Edge*>& inputEdges,
    vector<int>& resultOrder,
    map<EdgeTy, int>& resultEdgeQueue,
    int verbose) {
  const int inputVertexCount = graph.numberOfVertices();
  vector<int> componentOf(inputVertexCount, -1);
  vector<vector<int>> connectedParts;
  for (int start = 0; start < inputVertexCount; start++) {
    if (componentOf[start] >= 0) continue;
    const int component = (int)connectedParts.size();
    connectedParts.emplace_back();
    queue<int> search;
    search.push(start);
    componentOf[start] = component;
    while (!search.empty()) {
      const int u = search.front();
      search.pop();
      connectedParts.back().push_back(u);
      for (Edge* edge : graph.vertices[u]->edges) {
        CHECK(edge->incident(graph.vertices[u]));
        const int v = edge->other(graph.vertices[u])->index;
        CHECK(0 <= v && v < inputVertexCount);
        if (componentOf[v] == -1) {
          componentOf[v] = component;
          search.push(v);
        }
      }
    }
  }
  if (connectedParts.size() <= 1) return false;
  {
    vector<vector<Edge*>> edgesInPart(connectedParts.size());
    for (Edge* edge : inputEdges) {
      const int u = edge->source->index;
      const int v = edge->target->index;
      CHECK(componentOf[u] == componentOf[v]);
      edgesInPart[componentOf[u]].push_back(edge);
    }
    for (int partId = 0; partId < (int)connectedParts.size(); partId++) {
      const vector<int>& vertices = connectedParts[partId];
      PlanarGraph part;
      map<int, int> local;
      for (int i = 0; i < (int)vertices.size(); i++) {
        CHECK(local.emplace(vertices[i], i).second);
        part.newVertex();
      }
      map<Edge*, Edge*> copiedEdge;
      for (Edge* original : edgesInPart[partId]) {
        const int u = original->source->index;
        const int v = original->target->index;
        if (!local.count(u)) continue;
        CHECK(local.count(v));
        Edge* copy = part.newEdge(
            part.vertices[local.at(u)], part.vertices[local.at(v)]);
        CHECK(copiedEdge.emplace(original, copy).second);
      }
      for (int i = 0; i < (int)vertices.size(); i++) {
        const int originalVertex = vertices[i];
        for (Edge* original : graph.vertices[originalVertex]->edges) {
          CHECK(copiedEdge.count(original));
          Vertex* vertex = part.vertices[i];
          vertex->addEdgeAfter(copiedEdge.at(original),
                              vertex->edges.empty() ? nullptr : vertex->edges.back());
        }
      }
      if (vertices.size() >= 2) {
        CHECK(!part.vertices[0]->edges.empty());
        part.outerFace = part.extractRightFace(
            part.vertices[0], part.vertices[0]->edges[0]);
      }
      vector<int> localOrder;
      map<EdgeTy, int> localEdgeQueue;
      buildPPSLayout(part, queueBound, localOrder, localEdgeQueue, verbose);
      CHECK(localOrder.size() == vertices.size() &&
            localEdgeQueue.size() == copiedEdge.size());
      for (int localVertex : localOrder) {
        CHECK(0 <= localVertex && localVertex < (int)vertices.size());
        resultOrder.push_back(vertices[localVertex]);
      }
      for (const auto& [edge, q] : localEdgeQueue) {
        CHECK(0 <= edge.first && edge.first < (int)vertices.size() &&
              0 <= edge.second && edge.second < (int)vertices.size());
        CHECK(resultEdgeQueue.emplace(
                  make_edge(vertices[edge.first], vertices[edge.second]),
                  q).second);
      }
    }
    CHECK(resultOrder.size() == graph.vertices.size() &&
          resultEdgeQueue.size() == inputEdges.size(),
          "disconnected layout merge did not cover the input");
    vector<vector<EdgeTy>> separatedQueues(queueBound);
    for (const auto& [edge, q] : resultEdgeQueue) {
      CHECK(0 <= q && q < queueBound);
      separatedQueues[q].push_back(edge);
    }
    for (int q = 0; q < queueBound; q++) {
      CHECK(countRainbow(separatedQueues[q], resultOrder) <= 1,
            "disconnected input has nested edges in queue %d", q);
    }
    return true;
  }
}

void buildPPSLayout(
    PlanarGraph& graph,
    int queueBound,
    vector<int>& resultOrder,
    map<EdgeTy, int>& resultEdgeQueue,
    int verbose) {
  CHECK(queueBound == 48 || queueBound == 33);
  CHECK(resultOrder.empty() && resultEdgeQueue.empty());
  const int inputVertexCount = graph.numberOfVertices();
  const vector<Edge*> inputEdges = graph.extractEdges();
  if (inputVertexCount <= 2) {
    layoutTinyGraph(graph, inputEdges, resultOrder, resultEdgeQueue);
    return;
  }
  if (layoutComponentsSeparately(graph, queueBound, inputEdges, resultOrder,
                                 resultEdgeQueue, verbose)) {
    return;
  }
  triangulateInput(graph);
  PPSLayout layout = runPPSPipeline(
      graph, verbose, queueBound, inputVertexCount, inputEdges);
  resultOrder = std::move(layout.originalOrder);
  resultEdgeQueue = std::move(layout.originalEdgeQueue);
}
