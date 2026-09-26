#pragma once

#include "logging.h"
#include "common.h"
#include "adjacency.h"

#include <string>
#include <vector>
#include <map>
#include <unordered_map>

struct InputGraph {
  // the number of vertices
  int nc = -1;
  // vertices are in [0..nc); first < second
  std::vector<EdgeTy> edges;

  // custom labels for edges
  std::unordered_map<int, std::string> id2label;
  // reverse mapping
  std::unordered_map<std::string, int> label2id;
  // clockwise order of edges (for planar graphs)
  std::unordered_map<int, std::vector<int>> planar_edges;
  // faces (for planar graphs)
  std::vector<std::vector<int>> planar_faces;
  // index of the outerface
  int outerFace = -1;
  // edge directions (true => first->second, false => second->first)
  std::vector<bool> direction;
  // vertex colors; vertices are in [0..nc)
  std::unordered_map<int, int> color;
  // whether an edge is allowed to be on multiple pages
  std::vector<bool> multiPage;
  // fixed vertex order
  std::vector<int> vertexOrder;
  std::vector<int> invVertexOrder;

  // Constraints:
  // first node in the order
  int firstNode = 0;
  // pair<i, j>  ==>  node_i < node_j in the order
  std::vector<std::pair<int, int>> nodeRel;
  // pair<>  ==>  the two relations between the pairs of nodes are the same
  std::vector<std::pair<std::pair<int, int>, std::pair<int, int>>> sameRel;
  // edge_index ==> admissible pages for the edge
  std::unordered_map<int, std::vector<int>> edgePages;
  // pair<i, j>  ==>  edge_i and edge_j are in the same page
  std::vector<std::pair<int, int>> samePage;
  // pair<i, j>  ==>  edge_i and edge_j are in the distinct page
  std::vector<std::pair<int, int>> distinctPage;
  // k, edge_indices ==> specified edges are using at most k pages
  std::vector<std::pair<int, std::vector<int>>> groupEdgePages;
  // node ==> available tracks are in [0..pages)
  std::unordered_map<int, std::vector<int>> nodeTracks;

  InputGraph() {}

  InputGraph(int nc, const std::vector<EdgeTy>& edges) : nc(nc), edges(edges) {
    CHECK(edges.size() > 0, "empty input graph");

    for (const auto& [u, v] : edges) {
      CHECK(0 <= u && u < nc);
      CHECK(0 <= v && v < nc);
      CHECK(u < v);
    }

    initLabels();
  }

  // Filter out isolated vertices
  InputGraph(const std::vector<EdgeTy>& allEdges) {
    CHECK(allEdges.size() > 0, "empty input graph");
    nc = 0;
    edges.reserve(allEdges.size());

    int mx = std::max(allEdges[0].first, allEdges[0].second);
    for (const auto& [u, v] : allEdges) {
      mx = std::max(mx, u);
      mx = std::max(mx, v);
    }
    std::vector<int> index(mx + 1, -1);
    for (const auto& [u, v] : allEdges) {
      if (index[u] == -1) {
        index[u] = nc;
        nc++;
      }
      if (index[v] == -1) {
        index[v] = nc;
        nc++;
      }
      const int iu = std::min(index[u], index[v]);
      const int iv = std::max(index[u], index[v]);
      edges.push_back({iu, iv});
    }
    CHECK(nc > 0);

    initLabels();
  }

  void initLabels() {
    for (int i = 0; i < nc; i++) {
      id2label[i] = std::to_string(i);
      label2id[std::to_string(i)] = i;
    }
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

  size_t addEdge(int u, int v) {
    CHECK(u < v);
    CHECK(0 <= u && u < nc);
    CHECK(0 <= v && v < nc);
    CHECK(!hasEdge(u, v));
    edges.push_back({u, v});
    return edges.size() - 1;
  }

  bool hasEdge(int u, int v) const {
    for (auto& edge : edges) {
      if ((edge.first == u && edge.second == v) || (edge.first == v && edge.second == u))
        return true;
    }
    return false;
  }

  size_t findEdgeIndex(int u, int v) const {
    for (size_t i = 0; i < edges.size(); i++) {
      if (edges[i].first == u && edges[i].second == v)
        return i;

      if (edges[i].first == v && edges[i].second == u)
        return i;
    }
    ERROR("edge (" + std::to_string(u) + ", " + std::to_string(v) + ") not found");
    return -1;
  }

  size_t findEdgeIndex(const EdgeTy& edge) const {
    return findEdgeIndex(edge.first, edge.second);
  }

  int findVertexIndex(std::string label) {
    for (int i = 0; i < nc; i++) {
      if (id2label[i] == label)
        return i;
    }
    ERROR("vertex " + label + " not found");
    return -1;
  }

  std::string getVertexLabel(int v) const {
    CHECK(id2label.find(v) != id2label.end());
    return id2label.at(v);
  }

  std::vector<int> getAdjacentVertices(const int v) const {
    std::vector<int> adjacent;
    for (const auto& [u1, u2]: edges) {
      CHECK(u1 < u2);
      if (u1 == v)
        adjacent.push_back(u2);
      if (u2 == v)
        adjacent.push_back(u1);
    }
    sort_unique(adjacent);
    return adjacent;
  }

  bool isDirected() const {
    return !direction.empty();
  }

  bool isMultiPage() const {
    CHECK(multiPage.size() == edges.size() || multiPage.empty());
    return !multiPage.empty();
  }

  bool isMultiPage(int edgeIdx) const {
    CHECK(multiPage.size() == edges.size() || multiPage.empty());
    return multiPage.size() == edges.size() && multiPage[edgeIdx];
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

  bool adjacent(int edgeI, int edgeJ) const {
    if (edges[edgeI].first == edges[edgeJ].first)
      return true;
    if (edges[edgeI].first == edges[edgeJ].second)
      return true;
    if (edges[edgeI].second == edges[edgeJ].first)
      return true;
    if (edges[edgeI].second == edges[edgeJ].second)
      return true;
    return false;
  }

  bool independent(int edgeI, int edgeJ) const {
    return !adjacent(edgeI, edgeJ);
  }

  bool edgesCross(int edgeI, int edgeJ) const {
    CHECK(!vertexOrder.empty());
    const int l1 = std::min(invVertexOrder[edges[edgeI].first], invVertexOrder[edges[edgeI].second]);
    const int r1 = std::max(invVertexOrder[edges[edgeI].first], invVertexOrder[edges[edgeI].second]);
    const int l2 = std::min(invVertexOrder[edges[edgeJ].first], invVertexOrder[edges[edgeJ].second]);
    const int r2 = std::max(invVertexOrder[edges[edgeJ].first], invVertexOrder[edges[edgeJ].second]);

    return cross(l1, r1, l2, r2);
  }

  bool edgesNest(int edgeI, int edgeJ) const {
    CHECK(!vertexOrder.empty());
    const int l1 = std::min(invVertexOrder[edges[edgeI].first], invVertexOrder[edges[edgeI].second]);
    const int r1 = std::max(invVertexOrder[edges[edgeI].first], invVertexOrder[edges[edgeI].second]);
    const int l2 = std::min(invVertexOrder[edges[edgeJ].first], invVertexOrder[edges[edgeJ].second]);
    const int r2 = std::max(invVertexOrder[edges[edgeJ].first], invVertexOrder[edges[edgeJ].second]);

    return nest(l1, r1, l2, r2);
  }

  int getFixedIndex(int v) const {
    CHECK(!vertexOrder.empty());
    CHECK(vertexOrder.size() == invVertexOrder.size());
    return invVertexOrder[v];
  }

  std::string edge_to_string(int edgeIdx) const {
    int u = edges[edgeIdx].first;
    int v = edges[edgeIdx].second;
    if (!direction.empty() && !direction[edgeIdx]) std::swap(u, v);
    return "(" + id2label.find(u)->second + ", " + id2label.find(v)->second + ")";
  }

  void addNodeRel(int left, int right) {
    CHECK(left != right);
    CHECK(0 <= left && left < nc);
    CHECK(0 <= right && right < nc);
    nodeRel.push_back({left, right});
  }

  void addNodeRel(const std::vector<int>& partialOrder) {
    for (size_t i = 0; i < partialOrder.size(); i++) {
      for (size_t j = i + 1; j < partialOrder.size(); j++) {
        addNodeRel(partialOrder[i], partialOrder[j]);
      }
    }
  }

  void setNodeOrder(const std::vector<int>& order) {
    CHECK((int)order.size() == nc);
    vertexOrder = order;
    invVertexOrder = inverse(vertexOrder);
  }

  void setPrefixOrder(const std::vector<int>& prefixOrder) {
    for (size_t i = 0; i < prefixOrder.size(); i++) {
      const int u = prefixOrder[i];
      CHECK(std::count(prefixOrder.begin(), prefixOrder.end(), u) == 1, "repeated element %d in the prefix order", u);
      // is it already in the order?
      for (int v = 0; v < nc; v++) {
        auto it = std::find(prefixOrder.begin(), prefixOrder.end(), v);
        if (it == prefixOrder.end()) {
          addNodeRel(u, v);
        } else {
          size_t j = it - prefixOrder.begin();
          if (i < j)
            addNodeRel(u, v);
        }
      }
    }
  }

  void addSamePage(int edgeI, int edgeJ) {
    if (edgeI != edgeJ)
      samePage.push_back(std::make_pair(edgeI, edgeJ));
  }

  void addSamePages(const std::vector<int>& edgeIndices) {
    for (size_t i = 0; i < edgeIndices.size(); i++) {
      for (size_t j = i + 1; j < edgeIndices.size(); j++) {
        addSamePage(edgeIndices[i], edgeIndices[j]);
      }
    }
  }

  void addSamePages(const std::vector<EdgeTy>& edges) {
    for (size_t i = 0; i < edges.size(); i++) {
      for (size_t j = i + 1; j < edges.size(); j++) {
        addSamePage(findEdgeIndex(edges[i]), findEdgeIndex(edges[j]));
      }
    }
  }

  void addSamePage(int u1, int v1, int u2, int v2) {
    size_t edgeI = findEdgeIndex(u1, v1);
    size_t edgeJ = findEdgeIndex(u2, v2);
    addSamePage(edgeI, edgeJ);
  }

  void addDistinctPage(int edgeI, int edgeJ) {
    if (edgeI != edgeJ)
      distinctPage.push_back(std::make_pair(edgeI, edgeJ));
  }

  void addDistinctPage(int u1, int v1, int u2, int v2) {
    size_t edgeI = findEdgeIndex(u1, v1);
    size_t edgeJ = findEdgeIndex(u2, v2);
    addDistinctPage(edgeI, edgeJ);
  }

  void addDistinctPage(const EdgeTy& edgeI, const EdgeTy& edgeJ) {
    addDistinctPage(edgeI.first, edgeI.second, edgeJ.first, edgeJ.second);
  }

  void addDistinctPages(const std::vector<EdgeTy>& edgesI, const std::vector<EdgeTy>& edgesJ) {
    for (auto& ei : edgesI) {
      for (auto& ej : edgesJ) {
        addDistinctPage(ei, ej);
      }
    }
  }

  void addSameRelation(int u1, int v1, int u2, int v2) {
    auto p1 = std::make_pair(u1, v1);
    auto p2 = std::make_pair(u2, v2);
    sameRel.push_back({p1, p2});
  }

  void setEdgePages(int u, int v, const std::vector<int>& pages) {
    CHECK(hasEdge(u, v));
    size_t edgeIdx = findEdgeIndex(u, v);
    setEdgePages(edgeIdx, pages);
  }

  void setEdgePages(const EdgeTy& edge, const std::vector<int>& pages) {
    size_t edgeIdx = findEdgeIndex(edge);
    setEdgePages(edgeIdx, pages);
  }

  void setEdgePages(size_t edgeIdx, const std::vector<int>& pages) {
    CHECK(edgeIdx < edges.size());
    // if (edgePages.find(edgeIdx) != edgePages.end()) {
    //   LOG("repeated setEdgePages for edge (%d, %d):  NEW = [%s]  OLD = [%s]", u, v, to_string(pages).c_str(), to_string(edgePages[edgeIdx]).c_str());
    // }
    CHECK(edgePages.find(edgeIdx) == edgePages.end() || edgePages[edgeIdx] == pages);
    edgePages[edgeIdx] = pages;
  }

  /// Specified edges use at most K pages in total
  void addGroupEdgePages(int k, const std::vector<int>& edgeIndices) {
    if (edgeIndices.empty()) return;
    CHECK(k > 0 && edgeIndices.size() > 0);
    CHECK(k <= 3, "larger values of group-edge-pages are not supported");
    groupEdgePages.push_back({k, edgeIndices});
  }

  /// Specified edges use at most K pages in total
  void addGroupEdgePages(int k, const std::vector<EdgeTy>& edges) {
    std::vector<int> edgeIndices;
    for (const EdgeTy& e : edges) {
      edgeIndices.push_back(findEdgeIndex(e.first, e.second));
    }
    addGroupEdgePages(k, edgeIndices);
  }

  size_t numCustomConstraints() const {
    return nodeRel.size() + edgePages.size() + nodeTracks.size() + samePage.size() + distinctPage.size() + sameRel.size() + groupEdgePages.size();
  }
};

enum Embedding { STACK, QUEUE, TWIST, TRACK, MIXED, MIXED_PAGES, RIQUE };

struct Params {
  Embedding embedding = STACK;

  int stacks = 0;
  int queues = 0;
  int twists = 0;
  int tracks = 0;
  int mixedPages = 0;
  int riques = 0;
  // enabled general constraints
  std::vector<std::string> constraints;
  // whether to include variables for adjacent vertices
  bool adjacent = false;
  // max edge span (used for Track layouts only)
  int span = 0;
  // local pages
  int local = 0;
  // strict (queue) layout
  bool strict = false;
  // custom options (algorithm-dependent)
  std::string custom = "";

  // whether to skip SAT model altogether
  bool skipSAT = false;
  // whether to skip SAT solving
  bool skipSolve = false;
  // Verbosity level
  int verbose = 0;
  // whether to apply Bob's built-in symmetry-breaking constraints
  bool applyBasicSymmetry = true;
  // whether to apply Satsuma symmetry-breaking constraints
  bool applySatsuma = false;
  // whether the vertex order is fixed
  bool fixedOrder = false;
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
  bool isTwist() const {
    return embedding == TWIST;
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
  bool isRique() const {
    return embedding == RIQUE;
  }

  int page_num() const {
    return stacks + queues + twists + mixedPages + tracks + riques;
  }

  int page_var_num() const {
    if (isTwist())
      return 0;
    if (isTrack())
      return stacks;
    return stacks + queues + mixedPages + riques;
  }

  static int page_num(int stacks, int queues, int twists, int mixedPages, int tracks, int riques = 0) {
    return stacks + queues + twists + mixedPages + tracks + riques;
  }

  static std::string page_name(int stacks, int queues, int twists, int mixedPages, int tracks, int riques = 0) {
    if (stacks > 0 && queues > 0)
      return "(stack+queue)";
    if (stacks > 0)
      return "stack";
    if (queues > 0)
      return "queue";
    if (twists > 0)
      return "twist";
    if (mixedPages > 0)
      return "mixed page";
    if (tracks > 0)
      return "track";
    if (riques > 0)
      return "rique";
    return "?";
  }

  std::string to_string() const {
    std::string s = "";

    if (adjacent)
      s += " adjacent";

    if (local > 0)
      s += " local-" + std::to_string(local);

    if (!constraints.empty())
      s += " " + ::to_string(constraints);

    if (s.length() > 0 && s[0] == ' ')
      s = s.substr(1);

    if (s.length() == 0)
      s = " ";

    return "[" + s + "]";
  }
};

enum class ResultCode : int {
  SAT = 0,
  UNSAT = 1,
  TIMEOUT = 2,
  ERROR = 3,
};

inline const char* resultCodeName(ResultCode code) {
  switch (code) {
    case ResultCode::SAT:
      return "SAT";
    case ResultCode::UNSAT:
      return "UNSAT";
    case ResultCode::TIMEOUT:
      return "TIMEOUT";
    case ResultCode::ERROR:
      return "ERROR";
  }
  return "UNKNOWN";
}

struct Result {
  ResultCode code;
  // vertices are in [0..nc)
  std::vector<int> order;
  // pages are in [0..pages); every edge can be on multiple pages
  std::vector<std::vector<int>> pages;
  // tracks are in [0..tracks)
  std::vector<int> tracks;
  // page types: true=stack, false=queue
  std::vector<bool> pageTypes;
  // printable name for each edge page
  std::vector<std::string> pageNames;

  explicit Result(ResultCode _code): code(_code) {}

  bool isSat() const {
    return code == ResultCode::SAT;
  }

  bool isUnsat() const {
    return code == ResultCode::UNSAT;
  }

  bool isTimeout() const {
    return code == ResultCode::TIMEOUT;
  }

  bool isError() const {
    return code == ResultCode::ERROR;
  }

  bool isDecided() const {
    return isSat() || isUnsat();
  }

  bool isOnPage(int edgeIdx, int page) const {
    for (auto p : pages[edgeIdx]) {
      if (p == page)
        return true;
    }
    return false;
  }

  int getPage(int edgeIdx) const {
    CHECK(pages[edgeIdx].size() == 1);
    return pages[edgeIdx][0];
  }

  std::string getPageName(int page) const {
    CHECK(0 <= page && page < (int) pageNames.size());
    return pageNames[page];
  }
};

Result run(InputGraph& inputGraph, Params& params);

//
void encodeEdgePagesSymmetry(InputGraph& inputGraph, const Params& params);
