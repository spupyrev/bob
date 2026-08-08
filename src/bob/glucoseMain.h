#pragma once

#include "logging.h"
#include "adjacency.h"

#include <string>
#include <vector>
#include <map>

struct InputGraph {
  using EdgeTy = std::pair<int, int>;

  int nc = -1;
  // vertices are in [0..nc); first < second
  std::vector<EdgeTy> edges;

  // custom labels for edges
  std::map<int, std::string> id2label;
  // reverse mapping
  std::map<std::string, int> label2id;
  // clockwise order of edges (for planar graphs)
  std::map<int, std::vector<int>> planar_edges;
  // faces (for planar graphs)
  std::vector<std::vector<int>> planar_faces;
  // index of the outerface
  int outerFace = -1;
  // edge directions (true => first->second, false => second->first)
  std::vector<bool> direction;
  // vertex colors; vertices are in [0..nc)
  std::map<int, int> color;
  // whether an edge is allowed to be on multiple pages
  std::vector<bool> multiPage;

  // Constraints:
  // first node in the order
  int firstNode = 0;
  // pair<i, j>  ==>  node_i < node_j in the order
  std::vector<std::pair<int, int>> nodeRel;
  // pair<>  ==>  the two relations between the pairs of nodes are the same
  std::vector<std::pair<std::pair<int, int>, std::pair<int, int>>> sameRel;
  // edge_index ==> available colors are in [0..pages)
  std::map<int, std::vector<int>> edgePages;
  // pair<i, j>  ==>  edge_i and edge_j are in the same page
  std::vector<std::pair<int, int>> samePage;
  // pair<i, j>  ==>  edge_i and edge_j are in the distinct page
  std::vector<std::pair<int, int>> distinctPage;
  // k, edge_indices ==> specified edges are using at most k pages
  std::vector<std::pair<int, std::vector<int>>> groupEdgePages;
  // node ==> available tracks are in [0..pages)
  std::map<int, std::vector<int>> nodeTracks;

  InputGraph() {}

  InputGraph(int nc_, const std::vector<EdgeTy>& edges_) : nc(nc_), edges(edges_) {
    CHECK(edges_.size() > 0, "empty input graph");

    for (auto& edge : edges_) {
      CHECK(0 <= edge.first && edge.first < nc);
      CHECK(0 <= edge.second && edge.second < nc);
    }

    initLabels();
  }

  void initLabels() {
    for (int i = 0; i < nc; i++) {
      id2label[i] = std::to_string(i);
      label2id[std::to_string(i)] = i;
    }
  }

  size_t findEdgeIndex(int u, int v) const {
    for (size_t i = 0; i < edges.size(); i++) {
      if (edges[i].first == u && edges[i].second == v) {
        return i;
      }

      if (edges[i].first == v && edges[i].second == u) {
        return i;
      }
    }
    ERROR("edge (" + std::to_string(u) + ", " + std::to_string(v) + ") not found");
    return -1;
  }

  int findVertexIndex(std::string label) {
    for (int i = 0; i < nc; i++) {
      if (id2label[i] == label) {
        return i;
      }
    }
    ERROR("vertex " + label + " not found");
    return -1;
  }

  bool isDirected() {
    return !direction.empty();
  }

  std::vector<EdgeTy> directedEdges() const {
    if (direction.empty()) return edges;

    std::vector<EdgeTy> res;
    res.reserve(edges.size());
    for (size_t i = 0; i < edges.size(); i++) {
      if (direction[i]) res.push_back(edges[i]);
      else res.push_back(std::make_pair(edges[i].second, edges[i].first));
    }
    return res;
  }

  bool hasEdge(int u, int v) const {
    for (auto& edge : edges) {
      if (edge.first == u && edge.second == v) {
        return true;
      }

      if (edge.first == v && edge.second == u) {
        return true;
      }
    }

    return false;
  }

  int addVertex() {
    int id = nc;
    std::string label = "@" + std::to_string(id);
    CHECK(label2id.find(label) == label2id.end());
    id2label[id] = label;
    label2id[label] = id;
    nc++;
    return id;
  }

  std::string edge_to_string(int index) const {
    int u = edges[index].first;
    int v = edges[index].second;
    if (!direction.empty() && !direction[index]) std::swap(u, v);
    return "(" + id2label.find(u)->second + ", " + id2label.find(v)->second + ")";
  }

  void addNodeRel(int left, int right) {
    CHECK(left != right);
    CHECK(0 <= left && left < nc);
    CHECK(0 <= right && right < nc);
    nodeRel.push_back(std::make_pair(left, right));
  }

  void setNodeOrder(const std::vector<int>& order) {
    CHECK((int)order.size() == nc);
    for (size_t i = 0; i + 1 < order.size(); i++) {
      addNodeRel(order[i], order[i + 1]);
    }
  }

  void addSamePage(int edgeI, int edgeJ) {
    CHECK(edgeI != edgeJ);
    samePage.push_back(std::make_pair(edgeI, edgeJ));
  }

  void addSamePages(const std::vector<int>& edgeIndices) {
    for (size_t i = 0; i < edgeIndices.size(); i++) {
      for (size_t j = i + 1; j < edgeIndices.size(); j++) {
        addSamePage(edgeIndices[i], edgeIndices[j]);
      }
    }
  }

  void addSamePage(int u1, int v1, int u2, int v2) {
    int edgeI = findEdgeIndex(u1, v1);
    int edgeJ = findEdgeIndex(u2, v2);
    addSamePage(edgeI, edgeJ);
  }

  void addDistinctPage(int edgeI, int edgeJ) {
    CHECK(edgeI != edgeJ);
    distinctPage.push_back(std::make_pair(edgeI, edgeJ));
  }

  void addDistinctPage(int u1, int v1, int u2, int v2) {
    int edgeI = findEdgeIndex(u1, v1);
    int edgeJ = findEdgeIndex(u2, v2);
    addDistinctPage(edgeI, edgeJ);
  }

  void addSameRelation(int u1, int v1, int u2, int v2) {
    auto p1 = std::make_pair(u1, v1);
    auto p2 = std::make_pair(u2, v2);
    sameRel.push_back(std::make_pair(p1, p2));
  }

  void setEdgePages(int u, int v, const std::vector<int>& pages) {
    CHECK(hasEdge(u, v));
    size_t edgeIdx = findEdgeIndex(u, v);
    if (edgePages.find(edgeIdx) != edgePages.end()) {
      LOG("repeated setEdgePages for edge (%d, %d):  NEW = [%d]  OLD = [%d]", u, v, pages[0], edgePages[edgeIdx][0]);
    }
    CHECK(edgePages.find(edgeIdx) == edgePages.end() || edgePages[edgeIdx] == pages);
    edgePages[edgeIdx] = pages;
  }

  // specified edges use at most K pages in total
  void addGroupEdgePages(int k, const std::vector<int>& edgeIndices) {
    if (edgeIndices.empty()) return;
    CHECK(k > 0 && edgeIndices.size() > 0);
    CHECK(k <= 2, "larger values of group-edge-pages are not supported");
    groupEdgePages.push_back(make_pair(k, edgeIndices));
  }

  // specified edges use at most K pages in total
  void addGroupEdgePages(int k, const std::vector<EdgeTy>& edges) {
    std::vector<int> edgeIndices;
    for (auto e : edges) {
      edgeIndices.push_back(findEdgeIndex(e.first, e.second));
    }
    addGroupEdgePages(k, edgeIndices);
  }

  size_t numCustomConstraints() const {
    return nodeRel.size() + edgePages.size() + nodeTracks.size() + samePage.size() + distinctPage.size() + sameRel.size() + groupEdgePages.size();
  }
};

enum Embedding { STACK, QUEUE, TRACK, MIXED, MIXED_PAGES };

struct Params {
  Embedding embedding = STACK;

  int stacks = 0;
  int queues = 0;
  int tracks = 0;
  int mixedPages = 0;
  // max edge span (used for Track layouts only)
  int span = 0;
  // whether the graph is directed
  bool directed = false;
  // constraints
  std::string constraint = "";
  bool trees = false;
  bool adjacent = false;
  bool dispersible = false;
  // misc
  int colors = 0;
  // local pages
  int local = 0;
  // custom options (algorithm-dependent)
  std::string custom = "";
  // strict queue layouts
  bool strict = false;

  // SAT solver to use
  std::string solver;
  // whether to skip SAT model altogether
  bool skipSAT = false;
  // whether to skip SAT solving
  bool skipSolve = false;
  int verbose = 0;
  // whether to apply symmetry-breaking constraints using BreakID
  bool applyBreakID = false;
  // Dimacs input/output
  std::string modelFile = "";
  std::string resultFile = "";

  Params() {}

  bool isStack() const {
    return embedding == STACK;
  }
  bool isQueue() const {
    return embedding == QUEUE;
  }
  bool isTrack() const {
    return embedding == TRACK;
  }
  bool isMixed() const {
    return embedding == MIXED;
  }
  bool isMixedPages() const {
    return embedding == MIXED_PAGES;
  }

  std::string toString() const {
    std::string s = "";

    if (trees) {
      s += " trees";
    }

    if (adjacent) {
      s += " adjacent";
    }

    if (dispersible) {
      s += " dispersible";
    }

    if (directed) {
      s += " directed";
    }

    if (local > 0) {
      s += " local-" + std::to_string(local);
    }

    if (constraint != "") {
      s += " " + constraint;
    }

    if (s.length() > 0 && s[0] == ' ') {
      s = s.substr(1);
    }

    if (s.length() == 0) {
      s = " ";
    }

    return "[" + s + "]";
  }
};

struct Result {
  // 0 -- SAT
  // 1 -- UNSAT
  // 2 -- INDET
  // 3 -- ERROR
  int code;
  // vertices are in [0..nc)
  std::vector<int> order;
  // pages are in [0..pages); every edge can be on multiple pages
  std::vector<std::vector<int>> pages;
  // tracks are in [0..tracks)
  std::vector<int> tracks;
  // page types: true=stack, false=queue
  std::vector<bool> pageTypes;

  Result(int _code): code(_code) {}

  bool isOnPage(int edgeIdx, int page) const {
    for (auto p : pages[edgeIdx]) {
      if (p == page) return true;
    }
    return false;
  }

  int getPage(int edgeIdx) const {
    CHECK(pages[edgeIdx].size() == 1);
    return pages[edgeIdx][0];
  }
};

bool run(InputGraph& inputGraph, Params params);
