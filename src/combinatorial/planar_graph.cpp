#include "planar_graph.h"
#include "planarity.hpp"
#include "bob/logging.h"
#include "bob/graph_parser.h"
#include "bob/graph_algorithms.h"

#include <fstream>
#include <iostream>
#include <algorithm>
#include <set>
#include <map>
#include <queue>
#include <charconv>
#include <unordered_map>
#include <unordered_set>

void convertGml2Planar(PlanarGraph& graph, IOGraph& dotGraph);

int Vertex::degree() const {
  return (int)edges.size();
}

void Vertex::addEdge(Edge* edge) {
  CHECK(edges.size() <= 1);
  edges.push_back(edge);
}

void Vertex::addEdges(std::vector<Edge*> newEdges) {
  CHECK(edges.size() <= 1);
  addEdgesAfter(newEdges, edges.empty() ? nullptr : edges[0]);
}

void Vertex::addEdgeAfter(Edge* edge, const Edge* prev) {
  if (prev == nullptr) {
    CHECK(edges.empty());
    edges.push_back(edge);
    return;
  }

  CHECK(edge->source == this || edge->target == this);
  int edgeIndex = findEdgeIndex(prev);
  CHECK(edgeIndex != -1);
  edges.insert(edges.begin() + edgeIndex + 1, edge);
}

void Vertex::addEdgeBefore(Edge* edge, const Edge* prev) {
  if (prev == nullptr) {
    CHECK(edges.empty());
    edges.push_back(edge);
    return;
  }

  CHECK(edge->source == this || edge->target == this);
  int edgeIndex = findEdgeIndex(prev);
  CHECK(edgeIndex != -1);
  edges.insert(edges.begin() + edgeIndex, edge);
}

void Vertex::addEdgesAfter(std::vector<Edge*> newEdges, const Edge* prev) {
  if (prev == nullptr) {
    CHECK(edges.empty());
  }

  for (size_t i = 0; i < newEdges.size(); i++) {
    addEdgeAfter(newEdges[i], prev);
    prev = newEdges[i];
  }
}

void Vertex::removeEdge(Edge* edge) {
  int edgeIndex = findEdgeIndex(edge);
  CHECK(edgeIndex != -1);
  edges.erase(edges.begin() + edgeIndex);
}

Edge* Vertex::findEdgeAfter(Edge* edge) const {
  int edgeIndex = findEdgeIndex(edge);
  CHECK(edgeIndex != -1, "edge (%d, %d) not found for vertex %d", edge->source->index, edge->target->index, index);

  if (edgeIndex == (int)edges.size() - 1) {
    return edges[0];
  } else {
    return edges[edgeIndex + 1];
  }
}

Edge* Vertex::findEdgeBefore(Edge* edge) const {
  int edgeIndex = findEdgeIndex(edge);
  CHECK(edgeIndex != -1, "edge (%d, %d) not found for vertex %d", edge->source->index, edge->target->index, index);

  if (edgeIndex == 0) {
    return edges.back();
  } else {
    return edges[edgeIndex - 1];
  }
}

int Vertex::findEdgeIndex(const Edge* edge) const {
  for (int i = 0; i < (int)edges.size(); i++) {
    if (edges[i] == edge) {
      return i;
    }
  }

  return -1;
}

vector<Vertex*> Vertex::neighbors() const {
  vector<Vertex*> result;

  for (size_t i = 0; i < edges.size(); i++) {
    result.push_back(edges[i]->other(this));
  }

  return result;
}

bool Vertex::adjacent(const Vertex* v) const {
  for (size_t i = 0; i < edges.size(); i++) {
    if (edges[i]->other(this) == v) {
      return true;
    }
  }

  return false;
}

Edge* Vertex::adjacentEdge(const Vertex* v) const {
  for (size_t i = 0; i < edges.size(); i++)
    if (edges[i]->other(this) == v) {
      return edges[i];
    }

  return nullptr;
}

int Vertex::commonNeighbors(const Vertex* u) const {
  int commonNeigCount = 0;

  for (int k = 0; k < (int)edges.size(); k++) {
    Vertex* w = edges[k]->other(this);

    if (this == w || u == w) {
      continue;
    }

    if (u->adjacent(w)) {
      commonNeigCount++;
    }
  }

  return commonNeigCount;
}

int Face::getIndex(Vertex* v) const {
  for (size_t i = 0; i < vertices.size(); i++) {
    if (vertices[i] == v) {
      return i;
    }
  }
  return -1;
}

bool Face::contains(Edge* edge) const {
  for (size_t i = 0; i < edges.size(); i++) {
    if (edges[i] == edge) {
      return true;
    }
  }
  return false;
}

bool Face::contains(Vertex* v) const {
  return getIndex(v) != -1;
}

Vertex* Face::opposite(const Vertex* v) const {
  CHECK(length() % 2 == 0);

  for (size_t i = 0; i < vertices.size(); i++) {
    if (vertices[i] == v) {
      int mid = length() / 2;
      return vertices[(i + mid) % length()];
    }
  }

  ERROR("vertex not found on the face");
  return nullptr;
}

string Face::to_string() const {
  string s = "";
  string sl = "";

  for (size_t k = 0; k < vertices.size(); k++) {
    s += ::to_string(vertices[k]->index);
    sl += ::to_string(vertices[k]->label);

    if (k + 1 != vertices.size()) {
      s += " ";
      sl += " ";
    }
  }
  if (s == sl) {
    return s;
  }
  return s + " (" + sl + ")";
}

void Face::reverse() {
  std::reverse(edges.begin(), edges.end());
  vector<Vertex*> resV2;
  resV2.push_back(vertices[0]);

  for (int i = 1; i < (int)vertices.size(); i++) {
    int idx = vertices.size() - i;
    resV2.push_back(vertices[idx]);
  }

  vertices = resV2;
}

std::string Face::hash() const {
  auto vi = vector<int>(vertices.size(), -1);

  for (size_t i = 0; i < vertices.size(); i++) {
    vi[i] = vertices[i]->index;
  }

  std::sort(vi.begin(), vi.end());
  std::string h = "";

  for (int idx : vi) {
    h += ::to_string(idx) + "#";
  }

  return h;
}

Edge* PlanarGraph::extractEdge(Vertex* v, Vertex* u) const {
  return v->adjacentEdge(u);
}

Face PlanarGraph::extractRightFace(Vertex* v, Edge* e) const {
  return extractFace(v, e, true);
}

Face PlanarGraph::extractLeftFace(Vertex* v, Edge* e) const {
  return extractFace(v, e, false);
}

Face PlanarGraph::extractFace(Vertex* v, Edge* e, bool right) const {
  vector<Vertex*> resV;
  vector<Edge*> resE;
  resV.push_back(v);
  resE.push_back(e);
  Edge* sourceEdge = e;
  Vertex* sourceVertex = v;
  Vertex* u = e->other(v);

  while (true) {
    Edge* e_next = (right ? u->findEdgeBefore(e) : u->findEdgeAfter(e));

    if (e_next == sourceEdge && u == sourceVertex)
      break;

    resV.push_back(u);
    resE.push_back(e_next);
    Vertex* v_next = u;
    Vertex* u_next = e_next->other(u);
    v = v_next;
    u = u_next;
    e = e_next;
  }

  // The walk leaves the start vertex along e, so it has at least two darts.
  CHECK(resV.size() >= 2, "face walk of a single dart");

  if (!right) {
    std::reverse(resE.begin(), resE.end());
    vector<Vertex*> resV2;
    resV2.push_back(resV[0]);

    for (int i = 1; i < (int)resV.size(); i++) {
      int idx = resV.size() - i;
      resV2.push_back(resV[idx]);
    }

    resV = resV2;
  }

  return Face(resV, resE);
}

Face PlanarGraph::extractFace(const vector<Vertex*>& in_vertices) const {
  for (auto v : in_vertices) {
    CHECK(v == vertices[v->index], "incorrect input vertex in PlanarGraph::extractFace");
  }

  auto& v = in_vertices[0];

  for (size_t j = 0; j < v->edges.size(); j++) {
    Face face = extractRightFace(v, v->edges[j]);
    bool found = true;

    for (auto v : in_vertices) {
      if (!face.contains(v)) {
        found = false;
      }
    }

    if (found) {
      return face;
    }
  }

  ERROR("face not found");
  return Face();
}

vector<Face> PlanarGraph::extractFaces(const vector<Vertex*>& in_vertices) const {
  for (auto v : in_vertices) {
    CHECK(v == vertices[v->index], "incorrect input vertex in PlanarGraph::extractFace");
  }

  vector<Face> result;
  auto& v = in_vertices[0];

  for (size_t j = 0; j < v->edges.size(); j++) {
    Face face = extractRightFace(v, v->edges[j]);
    bool found = true;

    for (auto v : in_vertices) {
      if (!face.contains(v)) {
        found = false;
      }
    }

    if (found) {
      result.push_back(face);
    }
  }

  return result;
}

Face PlanarGraph::extractFace(const vector<int>& idx_vertices) const {
  vector<Vertex*> in_vertices;

  for (int idx : idx_vertices) {
    in_vertices.push_back(vertices[idx]);
  }

  return extractFace(in_vertices);
}

vector<Face> PlanarGraph::extractFaces(const vector<int>& idx_vertices) const {
  vector<Vertex*> in_vertices;

  for (int idx : idx_vertices) {
    in_vertices.push_back(vertices[idx]);
  }

  return extractFaces(in_vertices);
}

Face PlanarGraph::extractLongestFace() const {
  auto faces = extractFaces();
  CHECK(!faces.empty(), "graph has no faces");
  Face res;

  for (auto& face : faces) {
    if (face.length() > res.length()) {
      res = face;
    }
  }

  return res;
}

vector<Face> PlanarGraph::extractFaces(Vertex* v) const {
  vector<Face> res;

  for (size_t j = 0; j < v->edges.size(); j++) {
    auto face = extractRightFace(v, v->edges[j]);
    res.push_back(face);
  }

  return res;
}

vector<Face> PlanarGraph::extractFaces(bool includeOuterface) const {
  vector<Face> faces;
  const vector<Edge*> allEdges = extractEdges();
  map<Edge*, int> edgeId;
  for (int i = 0; i < (int)allEdges.size(); i++) {
    CHECK(edgeId.emplace(allEdges[i], i).second);
  }
  vector<bool> seenDart(2 * allEdges.size(), false);
  for (Vertex* start : vertices) {
    for (Edge* edge : start->edges) {
      CHECK(edgeId.count(edge) && edge->incident(start));
      const int dart = 2 * edgeId.at(edge) +
          (edge->source == start ? 0 : 1);
      if (seenDart[dart]) continue;
      const Face face = extractRightFace(start, edge);
      CHECK(face.vertices.size() == face.edges.size());
      for (int i = 0; i < face.length(); i++) {
        Vertex* at = face.vertices[i];
        Edge* side = face.edges[i];
        CHECK(edgeId.count(side) && side->incident(at));
        const int sideDart = 2 * edgeId.at(side) +
            (side->source == at ? 0 : 1);
        CHECK(!seenDart[sideDart],
              "two face walks use the same directed edge side");
        seenDart[sideDart] = true;
      }
      if (includeOuterface || !(face == outerFace)) faces.push_back(face);
    }
  }
  for (bool seen : seenDart) {
    CHECK(seen, "a directed edge side has no face walk");
  }
  int n = numberOfVertices();
  int m = numberOfEdges();
  int f = (int)faces.size();
  if (n >= 2 && m > 0 && isConnected()) {
    const int expected = !includeOuterface && !outerFace.empty() ? 1 : 2;
    CHECK(n - m + f == expected,
          "connected embedding violates Euler's formula: n=%d m=%d f=%d",
          n, m, f);
  }
  return faces;
}

vector<vector<int>> PlanarGraph::extractFacesId() const {
  vector<vector<int>> ids;

  for (auto& face : extractFaces()) {
    vector<int> id;
    id.reserve(face.vertices.size());

    for (auto v : face.vertices) {
      id.push_back(v->index);
    }

    ids.push_back(id);
  }

  return ids;
}

vector<Edge*> PlanarGraph::extractEdges() const {
  vector<Edge*> edges;

  for (auto v : vertices) {
    for (auto e : v->edges) {
      if (v->index < e->other(v)->index) {
        edges.push_back(e);
      }
    }
  }

  return edges;
}

vector<pair<int, int>> PlanarGraph::extractEdgesId() const {
  vector<pair<int, int>> edges;

  for (auto v : vertices) {
    for (auto e : v->edges) {
      if (v->index < e->other(v)->index) {
        edges.push_back(make_pair(v->index, e->other(v)->index));
      }
    }
  }
  return edges;
}

Vertex* PlanarGraph::newVertex() {
  return newVertex(false);
}

Vertex* PlanarGraph::newVertex(bool generated) {
  Vertex* v = new Vertex(vertices.size());

  if (generated) {
    v->label = "@" + to_string(v->index);
  }

  vertices.push_back(v);
  return v;
}

Edge* PlanarGraph::newEdge(Vertex* v, Vertex* u) {
  return new Edge(v, u);
}

void PlanarGraph::removeVertex(Vertex* v) {
  vector<Edge*> edges = v->edges;

  for (size_t i = 0; i < edges.size(); i++) {
    Edge* edge = edges[i];
    removeEdge(edge);
  }

  vertices.erase(remove(vertices.begin(), vertices.end(), v), vertices.end());
  delete v;
}

void PlanarGraph::removeEdge(Edge* edge) {
  edge->source->removeEdge(edge);
  edge->target->removeEdge(edge);
  delete edge;
}

Vertex* PlanarGraph::randomVertex() const {
  return vertices[Rand::next(vertices.size())];
}

Edge* PlanarGraph::randomEdge() const {
  Vertex* v = randomVertex();
  return v->edges[Rand::next(v->edges.size())];
}

Edge* PlanarGraph::randomEdge(Vertex* v) const {
  return v->edges[Rand::next(v->edges.size())];
}

Face PlanarGraph::randomFace() const {
  Vertex* v = randomVertex();
  Edge* e = v->edges[Rand::next(v->edges.size())];
  return extractRightFace(v, e);
}

void PlanarGraph::write() const {
  writeStats();
  std::cout << "vertices:\n";

  for (int i = 0; i < (int)vertices.size(); i++) {
    auto v = vertices[i];
    std::cout << "  " << v->label << ":";

    for (int j = 0; j < (int)v->edges.size(); j++) {
      std::cout << " " << v->edges[j]->other(v)->label;
    }

    std::cout << "\n";
  }

  std::cout << "faces:\n";

  for (auto& face : extractFaces()) {
    std::cout << "  " << face.to_string() << "\n";
  }

  //printf("outerface: ");
  //outerFace.debugOutput();
}

void PlanarGraph::writeStats() const {
  cout << "|V|=" << numberOfVertices() << "  "
       << "|E|=" << numberOfEdges() << "  "
       << minDegree() << " <= deg <= " << maxDegree() << "\n";
}

int PlanarGraph::numberOfEdges() const {
  int m = 0;

  for (auto& v : vertices) {
    m += v->degree();
  }

  CHECK(m % 2 == 0, "the sum of degrees is not even");
  m /= 2;
  return m;
}

int PlanarGraph::numberOfVertices() const {
  return (int)vertices.size();
}

int PlanarGraph::maxDegree() const {
  int mx = 0;

  for (int i = 0; i < (int) vertices.size(); i++) {
    mx = max(mx, vertices[i]->degree());
  }

  return mx;
}

int PlanarGraph::minDegree() const {
  int mn = vertices[0]->degree();

  for (int i = 0; i < (int) vertices.size(); i++) {
    mn = min(mn, vertices[i]->degree());
  }

  return mn;
}

void PlanarGraph::writeDot(const string& filename) const {
  ofstream out;
  out.open(filename);
  out << "graph {\n";

  for (size_t i = 0; i < vertices.size(); i++) {
    Vertex* v = vertices[i];

    for (size_t j = 0; j < v->edges.size(); j++) {
      Vertex* u = v->edges[j]->other(v);

      if (v->index < u->index) {
        out << "  " << v->index << " -- " << u->index << ";\n";
      }
    }
  }

  out << "}\n";
  out.close();
}

void PlanarGraph::writeEdges(const string& filename) const {
  ofstream out(filename);
  CHECK(out.good(), "cannot open output file '%s'", filename.c_str());
  writeEdges(out);
  CHECK(out.good(), "failed to write output file '%s'", filename.c_str());
}

void PlanarGraph::writeGraphML(const string& filename) const {
  ofstream out;
  out.open(filename);
  out << "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n";
  out << "<graphml>\n";
  out << "<graph edgedefault=\"undirected\" id=\"G\">\n";

  for (size_t i = 0; i < vertices.size(); i++) {
    Vertex* v = vertices[i];
    out << "<node id=\"" << v->index << "\"/>\n";
  }

  int idx = 0;

  for (size_t i = 0; i < vertices.size(); i++) {
    Vertex* v = vertices[i];

    for (size_t j = 0; j < v->edges.size(); j++) {
      Vertex* u = v->edges[j]->other(v);

      if (v->index < u->index) {
        out << "<edge id=\"e" << idx << "\" source=\"" << v->index << "\" target=\"" << u->index << "\"/>\n";
        idx++;
      }
    }
  }

  out << "</graph>\n";
  out << "</graphml>\n";
  out.close();
}

void PlanarGraph::writeGML(const string& filename) {
  CHECK(vertices.size() == ioGraph.nodes.size(), "IOGraph is not initialized");
  CHECK(numberOfEdges() == (int)ioGraph.edges.size(), "incorrect number of edges in IOGraph");
  LOG(TextColor::blue, "writing planar gml graph to '%s'", filename.c_str());
  GraphParser parser;
  CHECK(parser.writeGmlGraph(filename, ioGraph), "writing gml file failed");
}

void PlanarGraph::readDOT(const std::string& filename) {
  CHECK(vertices.empty(), "DOT input requires an empty graph");
  IOGraph input;
  GraphParser parser;
  CHECK(parser.readDotGraph(filename, input), "parsing DOT file failed");
  const int n = input.nodes.size();
  CHECK(n > 0, "DOT input must contain at least one vertex");
  std::vector<std::pair<int, int>> edges;
  std::set<std::pair<int, int>> unique;
  for (const auto& edge : input.edges) {
    const int u = input.getNode(edge.source)->index;
    const int v = input.getNode(edge.target)->index;
    CHECK(u != v, "planar layouts require a simple graph: loop at %s", edge.source.c_str());
    const auto key = std::minmax(u, v);
    CHECK(unique.emplace(key.first, key.second).second,
          "planar layouts require a simple graph: repeated edge (%s,%s)",
          edge.source.c_str(), edge.target.c_str());
    edges.emplace_back(key.first, key.second);
  }
  const auto embedding = planarvibe::planarity::lr_test(n, edges);
  CHECK(embedding.ok, "DOT input is nonplanar: %s", embedding.reason.c_str());
  readEdges(embedding.rotation);
  for (int v = 0; v < n; ++v)
    vertices[v]->label = input.nodes[v].getAttr("label", input.nodes[v].id);
  // readEdges selects an outer face. Component preprocessing selects a face
  // independently for each other component before triangulating it.
  CHECK(checkConsistency(false), "computed DOT embedding is inconsistent");
}

void PlanarGraph::readGML(const string& filename) {
  LOG("parsing planar gml graph from '%s'", filename.c_str());
  GraphParser parser;
  CHECK(parser.readGmlGraph(filename, ioGraph), "parsing gml file failed");
  convertGml2Planar(*this, ioGraph);
}



bool PlanarGraph::isMaximal() const {
  if (outerFace.length() == numberOfVertices()) {
    return 2 * numberOfVertices() == numberOfEdges() + 3;
  }
  return 3 * numberOfVertices() == numberOfEdges() + 6;
}

bool PlanarGraph::isTriangulated() const {
  int outerFaceLength = outerFace.length();
  CHECK(outerFaceLength > 0, "outerface not found");
  return 3 * numberOfVertices() - 6 == numberOfEdges() + outerFaceLength - 3;
}

bool PlanarGraph::checkConsistency() const {
  return checkConsistency(true);
}

bool PlanarGraph::checkConsistency(bool threeConnected) const {
  CHECK(numberOfVertices() == (int)vertices.size());

  // check indices
  for (int i = 0; i < (int)vertices.size(); i++) {
    CHECK(vertices[i]->index == i, "index of vertex %d is not consistent", i);
  }

  //check all edges
  int m2 = 0;

  for (int i = 0; i < (int)vertices.size(); i++) {
    Vertex* v = vertices[i];

    for (int j = 0; j < (int)v->edges.size(); j++) {
      Vertex* u = v->edges[j]->other(v);
      CHECK((v->edges[j]->source == v && v->edges[j]->target == u) || (v->edges[j]->source == u && v->edges[j]->target == v));
      CHECK(v->edges[j]->source != v->edges[j]->target);
      m2++;
    }
  }

  CHECK(2 * numberOfEdges() == m2);

  //check simple
  for (int i = 0; i < (int)vertices.size(); i++) {
    Vertex* v = vertices[i];

    for (int j = 0; j < (int)v->edges.size(); j++)
      for (int k = j + 1; k < (int)v->edges.size(); k++) {
        if (v->edges[j]->other(v) == v->edges[k]->other(v)) {
          cerr << "problem with vertex " << v->label << ": ";
          cerr << "multi-edges " << v->edges[j]->to_string() << " and " << v->edges[k]->to_string() << "\n";
        }

        CHECK(v->edges[j]->other(v) != v->edges[k]->other(v));
      }
  }

  if (outerFace.length() > 0) {
    for (size_t i = 0; i < outerFace.vertices.size(); i++) {
      auto v = outerFace.vertices[i];
      auto u = outerFace.vertices[(i + 1) % outerFace.vertices.size()];
      CHECK(v->adjacent(u), "incorrect outerface; vertices %d and %d are not connected", v->index, u->index);
    }
    for (auto v : outerFace.vertices) {
      CHECK(v == vertices[v->index], "incorrect vertex on outerface with index %d", v->index);
    }
    // make sure it's a face
    auto v0 = outerFace.vertices[0];
    Face f1 = extractRightFace(v0, outerFace.edges[0]);
    Face f2 = extractLeftFace(v0, outerFace.edges[0]);
    CHECK(f1 == outerFace || f2 == outerFace, "outerface is not a face");
  }

  if (threeConnected) {
    //check faces
    for (int i = 0; i < (int)vertices.size(); i++) {
      Vertex* v = vertices[i];

      for (int j = 0; j < (int)v->edges.size(); j++) {
        Edge* e = v->edges[j];
        Vertex* u = e->other(v);
        Face f1 = extractRightFace(v, e);
        Face f2 = extractLeftFace(u, e);

        bool equalFaces = (f1 == f2);
        if (!equalFaces) {
          cerr << "not equal faces for edge " << e->to_string() << ":\n";
          cerr << f1.to_string() << " != " << f2.to_string() << "\n";
        }
        CHECK(equalFaces);

        int f1Length = f1.length();
        std::set<int> faceVertices;
        for (int k = 0; k < f1Length; k++) {
          Vertex* vf = f1.vertices[k];
          Edge* ef = f1.edges[k];
          // check all edges of the face are correct
          CHECK(ef->source == vf || ef->target == vf);

          // check the face contains unique vertices
          bool uniqueVertex = faceVertices.count(vf->index) == 0;
          if (!uniqueVertex) {
            cerr << "problem at face " << f1.to_string() << ": " << vf->index << "\n";
          }
          CHECK(uniqueVertex);
          faceVertices.insert(vf->index);
        }
      }
    }

    int faceLength = 0;
    auto faces = extractFaces();

    for (auto& f : faces) {
      faceLength += f.length();
    }

    CHECK(faceLength == m2);
  }

  if (!ioGraph.empty()) {
    CHECK(vertices.size() == ioGraph.nodes.size(), "incorrect number of vertices in IOGraph (%d)", ioGraph.nodes.size());
    CHECK(numberOfEdges() == (int)ioGraph.edges.size(), "incorrect number of edges in IOGraph");
    ioGraph.checkConsistency();
  }

  return true;
}

void PlanarGraph::readEdges(const string& filename) {
  // Format:
  // n m
  // v u_1,u_2,...,u_k (neighbors in clockwise order, ids are from 0 to n-1)
  // ...
  ifstream in(filename);
  CHECK(in.good(), "file not found: '%s'", filename.c_str());
  int n = -1, m = -1;
  CHECK(static_cast<bool>(in >> n >> m),
        "missing vertex/edge counts in '%s'", filename.c_str());
  CHECK(n >= 1 && m >= 0);
  vector<int> ids;
  vector<vector<int>> adj;

  for (int i = 0; i < n; i++) {
    string s;
    int id;
    in >> id >> s;
    CHECK(!in.fail(), "missing clockwise neighbor list for vertex row %d", i);
    vector<int> v;
    if (s != "-") {
      size_t begin = 0;
      while (begin < s.size()) {
        size_t end = s.find(',', begin);
        if (end == string::npos) end = s.size();
        CHECK(begin < end,
              "empty clockwise neighbor in vertex row %d", i);
        int neighbor = -1;
        const auto parsed = std::from_chars(
            s.data() + begin, s.data() + end, neighbor);
        CHECK(parsed.ec == std::errc{} &&
              parsed.ptr == s.data() + end,
              "invalid clockwise neighbor token in vertex row %d", i);
        v.push_back(neighbor);
        if (end == s.size()) break;
        begin = end + 1;
        CHECK(begin < s.size(),
              "trailing comma in vertex row %d", i);
      }
      CHECK(!v.empty(), "empty clockwise neighbor token in vertex row %d", i);
    }
    ids.push_back(id);
    adj.push_back(v);
  }

  string extra;
  CHECK(!(in >> extra), "extra data after %d clockwise rows", n);
  in.close();
  // check input
  map<int, int> all;

  for (size_t i = 0; i < ids.size(); i++) {
    CHECK(all.count(ids[i]) == 0);
    all[ids[i]] = i;
  }

  CHECK((int) all.size() == n);
  int am = 0;

  for (size_t i = 0; i < ids.size(); i++) {
    for (size_t j = 0; j < adj[i].size(); j++) {
      CHECK(all.count(adj[i][j]) != 0);
      CHECK(ids[i] != adj[i][j]);
      am++;

      for (size_t k = j + 1; k < adj[i].size(); k++) {
        CHECK(adj[i][j] != adj[i][k]);
      }
    }
  }

  CHECK(am == 2 * m);
  vector<int> orderedIds(n, -1);
  vector<vector<int>> orderedAdj(n);
  for (int row = 0; row < n; row++) {
    CHECK(0 <= ids[row] && ids[row] < n,
          "input vertex ID %d is outside 0..%d", ids[row], n - 1);
    orderedIds[ids[row]] = ids[row];
    orderedAdj[ids[row]] = std::move(adj[row]);
  }
  readEdges(orderedIds, orderedAdj);
}

void PlanarGraph::readEdges(const vector<vector<int>>& adj) {
  vector<int> ids;

  for (size_t i = 0; i < adj.size(); i++) {
    ids.push_back(i);
  }

  readEdges(ids, adj);
}

void PlanarGraph::readEdges(const vector<int>& ids, const vector<vector<int>>& adj) {
  int n = ids.size();
  int m = 0;
  // check input
  map<int, int> all;

  for (size_t i = 0; i < ids.size(); i++) {
    CHECK(ids[i] == (int)i,
          "clockwise adjacency rows must be indexed 0..n-1");
    CHECK(all.count(ids[i]) == 0);
    all[ids[i]] = i;
    m += adj[i].size();
  }

  CHECK((int) all.size() == n);

  for (size_t i = 0; i < ids.size(); i++) {
    for (size_t j = 0; j < adj[i].size(); j++) {
      CHECK(all.count(adj[i][j]) != 0);
      CHECK(ids[i] != adj[i][j]);

      for (size_t k = j + 1; k < adj[i].size(); k++) {
        CHECK(adj[i][j] != adj[i][k]);
      }
    }
  }

  CHECK(m % 2 == 0);
  m /= 2;

  // create vertices
  for (size_t i = 0; i < ids.size(); i++) {
    Vertex* v = new Vertex(ids[i]);
    vertices.push_back(v);
  }

  // create edges
  map<pair<int, int>, int> cnt;
  map<pair<int, int>, Edge*> allEdges;

  for (size_t i = 0; i < ids.size(); i++) {
    int vid = ids[i];
    Vertex* v = vertices[i];
    Edge* prev = nullptr;

    for (size_t j = 0; j < adj[i].size(); j++) {
      int uid = adj[i][j];
      Vertex* u = vertices[all[uid]];
      Edge* edge = nullptr;

      if (vid < uid) {
        edge = new Edge(v, u);
        auto pr = make_pair(vid, uid);
        CHECK(allEdges.count(pr) == 0);
        allEdges[pr] = edge;
        cnt[pr]++;
      } else {
        auto pr = make_pair(uid, vid);
        CHECK(allEdges.count(pr) == 1);
        edge = allEdges[pr];
        cnt[pr]++;
      }

      v->addEdgeAfter(edge, prev);
      prev = edge;
    }
  }

  for (auto it : cnt) {
    if (it.second != 2) {
      cerr << "missing edge (" << it.first.first << "," << it.first.second << ")\n";
    }

    CHECK(it.second == 2);
  }

  CHECK(checkConsistency(false), "parsed graph is not consistent");
  if (vertices.size() >= 2 && vertices[0]->adjacent(vertices[1])) {
    outerFace = extractRightFace(vertices[0], vertices[0]->adjacentEdge(vertices[1]));
    return;
  }
  if (numberOfEdges() > 0) {
    outerFace = extractLongestFace();
  }
}

vector<vector<int>> PlanarGraph::adjacencyList() const {
  vector<vector<int>> res;

  for (size_t i = 0; i < vertices.size(); i++) {
    vector<int> adj;
    Vertex* v = vertices[i];

    for (size_t j = 0; j < v->edges.size(); j++) {
      Vertex* u = v->edges[j]->other(v);
      adj.push_back(u->index);
    }

    res.push_back(adj);
  }

  return res;
}

void PlanarGraph::constructDual(PlanarGraph& dual) const {
  vector<Face> faces = extractFaces();

  for (int i = 0; i < (int)faces.size(); i++) {
    Vertex* dv = new Vertex(i);
    dual.vertices.push_back(dv);
  }

  vector<pair<Edge*, Edge*>> primeToDualEdges;

  for (int i = 0; i < (int)faces.size(); i++) {
    Vertex* dv = dual.vertices[i];
    Edge* prev = nullptr;
    int len = faces[i].length();

    for (int j = 0; j < len; j++) {
      Vertex* v = faces[i][j];
      Edge* uv = faces[i].edges[j];
      CHECK(extractRightFace(v, uv) == faces[i]);
      Face oppositeFace = extractLeftFace(v, uv);
      Vertex* du = nullptr;

      for (int k = 0; k < (int)faces.size(); k++)
        if (oppositeFace == faces[k]) {
          du = dual.vertices[k];
          break;
        }

      CHECK(du != nullptr);
      Edge* dualUV = nullptr;

      for (int k = 0; k < (int)primeToDualEdges.size(); k++)
        if (primeToDualEdges[k].first == uv) {
          dualUV = primeToDualEdges[k].second;
          break;
        }

      if (dualUV == nullptr) {
        dualUV = new Edge(dv, du);
        primeToDualEdges.push_back(make_pair(uv, dualUV));
      }

      dv->addEdgeAfter(dualUV, prev);
      prev = dualUV;
    }
  }

  CHECK(dual.checkConsistency());
}

void PlanarGraph::triangulate() {
  triangulateByAddingEdges();
  CHECK(numberOfEdges() == 3 * numberOfVertices() - 6);
}

void PlanarGraph::triangulateByStellation(bool ignoreOuterFace) {
  vector<Face> faces = extractFaces();

  for (size_t f = 0; f < faces.size(); f++) {
    if (faces[f].length() == 3) {
      continue;
    }

    const bool stellatesOuterFace = outerFace == faces[f];
    if (ignoreOuterFace && stellatesOuterFace) {
      continue;
    }

    // adding a vertex
    auto v = newVertex();
    Edge* prevEdge = nullptr;

    for (size_t i = 0; i < faces[f].vertices.size(); i++) {
      auto u = faces[f].vertices[i];
      auto edge = new Edge(v, u);
      v->addEdgeAfter(edge, prevEdge);
      u->addEdgeAfter(edge, faces[f].edges[i]);
      prevEdge = edge;
    }

    if (stellatesOuterFace) {
      outerFace = extractRightFace(faces[f].vertices[0], faces[f].edges[0]);
      CHECK(outerFace.length() == 3 && outerFace.contains(v),
            "stellated outerface is not triangular");
      CHECK(outerFace == extractRightFace(outerFace.vertices[0], outerFace.edges[0]),
            "outerface is not a face after stellation");
    }
  }

  CHECK(checkConsistency(), "graph is not consistent after triangulation");
}

void PlanarGraph::copy(const PlanarGraph& other) {
  CHECK(vertices.empty(), "graph is not empty");
  auto edges = other.adjacencyList();
  readEdges(edges);
  CHECK(vertices.size() == other.vertices.size());
  for (size_t i = 0; i < vertices.size(); i++) {
    vertices[i]->label = other.vertices[i]->label;
  }
}

vector<int> PlanarGraph::bfs(const std::vector<int>& start) const {
  CHECK(!start.empty());
  vector<int> depth(vertices.size(), -1);
  queue<int> q;
  for (int now : start) {
    depth[now] = 0;
    q.push(now);
  }

  while (!q.empty()) {
    int now = q.front();
    q.pop();

    for (auto adj : vertices[now]->neighbors()) {
      int next = adj->index;

      if (depth[next] != -1) {
      } else {
        depth[next] = depth[now] + 1;
        q.push(next);
      }
    }
  }

  return depth;
}

bool PlanarGraph::isConnected() const {
  const int n = numberOfVertices();
  const int m = numberOfEdges();
  if (n <= 1 || (n >= 3 && m == 3 * n - 6)) {
    return true;
  }
  if (m < n - 1) {
    return false;
  }

  auto color = bfs({0});

  for (size_t i = 0; i < vertices.size(); i++) {
    if (color[i] == -1) {
      return false;
    }
  }

  return true;
}

bool PlanarGraph::isBipartite() const {
  CHECK(isConnected());
  auto depth = bfs({0});
  auto edges = extractEdges();

  for (size_t i = 0; i < edges.size(); i++) {
    int color1 = depth[edges[i]->source->index] % 2;
    int color2 = depth[edges[i]->target->index] % 2;

    if (color1 == color2) {
      return false;
    }
  }

  return true;
}

bool PlanarGraph::is4Connected() const {
  int n = (int)vertices.size();
  vector<int> vList;
  vector<vector<int>> adj = vector<vector<int>>(n, vector<int>());;

  for (int i = 0; i < n; i++) {
    Vertex* v = vertices[i];
    vList.push_back(v->index);

    for (int j = 0; j < (int)v->edges.size(); j++) {
      Vertex* u = v->edges[j]->other(v);
      adj[v->index].push_back(u->index);
    }
  }

  for (int i = 0; i < (int)vList.size(); i++) {
    for (int j = 0; j < (int)adj[i].size(); j++)
      for (int k = j + 1; k < (int)adj[i].size(); k++) {
        set<int> removed;
        removed.insert(vList[i]);
        removed.insert(adj[i][j]);
        removed.insert(adj[i][k]);

        if (!::isConnected(vList, adj, removed)) {
          cerr << "separating triangle: " << vList[i] << ", " << adj[i][j] << ", " << adj[i][k] << "\n";
          return false;
        }
      }
  }

  return true;
}

bool PlanarGraph::is3Connected() const {
  const int n = numberOfVertices();
  const int m = numberOfEdges();
  if (n >= 4 && m == 3 * n - 6) {
    return true;
  }
  if (n < 4 || m < (3 * n + 1) / 2) {
    return false;
  }

  return ::is3Connected(numberOfVertices(), extractEdgesId());
}




bool Face::hasCorner(Vertex* center, Vertex* incoming, Vertex* outgoing) const {
  const int n = length();
  for (int i = 0; i < n; i++) {
    if (vertices[i] == center &&
        edges[i]->incident(center) &&
        edges[i]->other(center) == outgoing &&
        edges[(i + n - 1) % n]->incident(center) &&
        edges[(i + n - 1) % n]->other(center) == incoming) {
      return true;
    }
  }
  return false;
}


Face PlanarGraph::faceAtCorner(Vertex* center, Vertex* incoming, Vertex* outgoing) const {
  Edge* edge = extractEdge(center, outgoing);
  CHECK(edge != nullptr);
  Face face = extractRightFace(center, edge);
  CHECK(face.hasCorner(center, incoming, outgoing),
        "angle %d-%d-%d is not an actual face corner",
        incoming->index, center->index, outgoing->index);
  return face;
}


void PlanarGraph::removeIncidentEdges(Vertex* v) {
  vector<Edge*> incident = v->edges;
  for (Edge* edge : incident) {
    removeEdge(edge);
  }
  CHECK(v->edges.empty());
}


void PlanarGraph::writeEdges(std::ostream& out) const {
  // Format:
  // n m
  // v u_1,u_2,...,u_k (neighbors in clockwise order)
  // ...
  out << numberOfVertices() << " " << numberOfEdges() << "\n";

  for (size_t i = 0; i < vertices.size(); i++) {
    Vertex* v = vertices[i];
    out << v->index;
    if (v->edges.empty()) {
      out << " -";
    }
    bool first = true;

    for (size_t j = 0; j < v->edges.size(); j++) {
      Vertex* u = v->edges[j]->other(v);

      if (first) {
        out << " ";
      } else {
        out << ",";
      }

      out << u->index;
      first = false;
    }

    out << "\n";
  }
}


bool PlanarGraph::adjacent(int u, int v) const {
  CHECK(0 <= u && u < numberOfVertices());
  CHECK(0 <= v && v < numberOfVertices());
  return vertices[u]->adjacent(vertices[v]);
}


void PlanarGraph::triangulateByAddingEdges() {
  // Triangulate a connected simple plane graph on at least three vertices
  // by adding edges only, preserving the rotations of existing edges:
  //  1. Walk around every face; whenever a vertex x is seen a second time,
  //     join its current predecessor and successor on the walk. Afterwards
  //     every face is bounded by a cycle.
  //  2. Triangulate every face (v, w_1, ..., w_k) with k > 3 from v. If v has
  //     no neighbor w_x with 1 < x < k, add the star v w_2, ..., v w_{k-1}.
  //     Otherwise the edge v w_x outside the face separates w_1, ..., w_{x-1}
  //     from w_{x+1}, ..., w_k, so the bi-star w_1 w_i (x < i <= k) and
  //     w_j w_{x+1} (1 < j < x) adds no parallel edge.
  //
  // The rotations are kept as circular lists of darts. Dart 2e leaves the
  // source of edge e and dart 2e+1 its target. The face to the right of a
  // dart d continues with the dart preceding the twin of d in the clockwise
  // rotation at its head, as in extractRightFace.
  CHECK(numberOfVertices() >= 3, "triangulation needs at least three vertices");
  vector<Edge*> edges = extractEdges();
  std::unordered_map<Edge*, int> edgeId;
  for (int e = 0; e < (int)edges.size(); e++) edgeId[edges[e]] = e;
  vector<int> cwNext(2 * edges.size()), cwPrev(2 * edges.size());
  auto dartOf = [&](Vertex* v, Edge* e) { return 2 * edgeId.at(e) + (e->source == v ? 0 : 1); };
  for (Vertex* v : vertices) {
    CHECK(!v->edges.empty(), "vertex %d is isolated", v->index);
    const int degree = v->degree();
    for (int i = 0; i < degree; i++) {
      const int d = dartOf(v, v->edges[i]);
      const int next = dartOf(v, v->edges[(i + 1) % degree]);
      cwNext[d] = next;
      cwPrev[next] = d;
    }
  }
  auto tail = [&](int d) { return (d & 1) ? edges[d >> 1]->target : edges[d >> 1]->source; };
  auto faceNext = [&](int d) { return cwPrev[d ^ 1]; };
  auto key = [](const Vertex* a, const Vertex* b) {
    const uint64_t lo = std::min(a->index, b->index), hi = std::max(a->index, b->index);
    return (hi << 32) | lo;
  };
  std::unordered_set<uint64_t> adjacentPairs;
  for (Edge* e : edges) {
    CHECK(e->source != e->target && adjacentPairs.insert(key(e->source, e->target)).second,
          "triangulation needs a simple graph");
  }
  // Add an edge from the tail of dart a to the tail of dart c, placed just
  // after a and c in the clockwise rotations (that is, in the corners of the
  // face where a and c leave). Returns the dart leaving the tail of a.
  auto addChord = [&](int a, int c) {
    Vertex* from = tail(a);
    Vertex* to = tail(c);
    CHECK(from != to && adjacentPairs.insert(key(from, to)).second,
          "added edge (%d,%d) is a loop or a parallel edge", from->index, to->index);
    edges.push_back(new Edge(from, to));
    const int d = 2 * ((int)edges.size() - 1);
    cwNext.resize(d + 2);
    cwPrev.resize(d + 2);
    for (auto [dart, after] : {std::pair<int, int>{d, a}, {d + 1, c}}) {
      cwNext[dart] = cwNext[after];
      cwPrev[dart] = after;
      cwPrev[cwNext[after]] = dart;
      cwNext[after] = dart;
    }
    return d;
  };
  auto collectFaces = [&]() {
    vector<vector<int>> faces;
    vector<char> visited(edges.size() * 2, 0);
    for (int start = 0; start < 2 * (int)edges.size(); start++) {
      if (visited[start]) continue;
      faces.emplace_back();
      for (int d = start; !visited[d]; d = faceNext(d)) {
        visited[d] = 1;
        faces.back().push_back(d);
      }
    }
    return faces;
  };

  // Step 1: make every face a cycle. The current walk is the prefix of kept
  // vertices followed by the rest of the original walk; `out` is the dart of
  // the walk leaving its last kept vertex. A repeated vertex x of the current
  // walk is a cut vertex, so its predecessor and successor are distinct and
  // nonadjacent; the new edge cuts off the triangle (predecessor, x, successor).
  vector<int> seenInFace(vertices.size(), -1);
  vector<vector<int>> faces = collectFaces();
  for (int f = 0; f < (int)faces.size(); f++) {
    const vector<int>& walk = faces[f];
    const int length = (int)walk.size();
    seenInFace[tail(walk[0])->index] = f;
    int out = walk[0];
    for (int i = 1; i < length; i++) {
      Vertex* x = tail(walk[i]);
      if (seenInFace[x->index] != f) {
        seenInFace[x->index] = f;
        out = walk[i];
        continue;
      }
      out = addChord(out, walk[(i + 1) % length]);
    }
  }

  // Step 2: triangulate every face by a star or a bi-star.
  faces = collectFaces();
  seenInFace.assign(vertices.size(), -1);
  for (int f = 0; f < (int)faces.size(); f++) {
    const vector<int>& walk = faces[f];  // tail(walk[0]) = v, tail(walk[i]) = w_i
    const int length = (int)walk.size();
    for (int d : walk) {
      CHECK(seenInFace[tail(d)->index] != f, "face has a repeated vertex after step 1");
      seenInFace[tail(d)->index] = f;
    }
    if (length == 3) continue;
    const int k = length - 1;
    Vertex* v = tail(walk[0]);
    int x = -1;
    for (int i = 2; i < k && x == -1; i++) {
      if (adjacentPairs.count(key(v, tail(walk[i])))) x = i;
    }
    if (x == -1) {
      for (int i = 2, out = walk[0]; i < k; i++) out = addChord(out, walk[i]);
      continue;
    }
    // Star from w_1 to w_{x+1}, ..., w_k; it leaves the face (w_1, ..., w_{x+1}),
    // which the star from w_{x+1} to w_2, ..., w_{x-1} completes.
    const int first = addChord(walk[1], walk[x + 1]);
    for (int i = x + 2, out = first; i <= k; i++) out = addChord(out, walk[i]);
    for (int j = 2, out = first ^ 1; j < x; j++) out = addChord(out, walk[j]);
  }

  // Write the rotations back, starting each at its first original edge, and
  // check that the original rotation is a subsequence of the new one.
  for (Vertex* v : vertices) {
    const vector<Edge*> original = v->edges;
    const int start = dartOf(v, original[0]);
    v->edges.clear();
    size_t matched = 0;
    int d = start;
    do {
      v->edges.push_back(edges[d >> 1]);
      if (matched < original.size() && edges[d >> 1] == original[matched]) matched++;
      d = cwNext[d];
    } while (d != start);
    CHECK(matched == original.size(), "triangulation changed the rotation at vertex %d", v->index);
  }
  outerFace = extractRightFace(outerFace.vertices[0], outerFace.edges[0]);
  CHECK(outerFace.length() == 3, "outer face is not a triangle after triangulation");
  CHECK(checkConsistency(), "graph is not consistent after triangulation");
}


bool PlanarGraph::is2Connected() const {
  const int n = numberOfVertices();
  const int m = numberOfEdges();
  if (n >= 3 && m == 3 * n - 6) {
    return true;
  }
  if (n < 3 || m < n) {
    return false;
  }

  return ::is2Connected(numberOfVertices(), extractEdgesId());
}


bool drawingMatchesClockwiseRotations(
    const PlanarGraph& graph,
    const vector<int>& x,
    const vector<long long>& y,
    int* badVertex) {
  CHECK((int)x.size() == graph.numberOfVertices());
  CHECK((int)y.size() == graph.numberOfVertices());
  for (Vertex* vertex : graph.vertices) {
    struct Ray {
      Edge* edge;
      long long dx;
      long long dy;
    };
    vector<Ray> rays;
    for (Edge* edge : vertex->edges) {
      const int other = edge->other(vertex)->index;
      const long long dx = (long long)x[other] - x[vertex->index];
      const long long dy = (long long)y[other] - y[vertex->index];
      CHECK(dx != 0 || dy != 0,
            "drawing collapses edge (%d,%d)", vertex->index, other);
      rays.push_back({edge, dx, dy});
    }
    auto upper = [](const Ray& ray) {
      return ray.dy > 0 || (ray.dy == 0 && ray.dx > 0);
    };
    std::sort(rays.begin(), rays.end(), [&](const Ray& a, const Ray& b) {
      if (upper(a) != upper(b)) {
        return upper(a);
      }
      const __int128 cross =
          (__int128)a.dx * b.dy - (__int128)a.dy * b.dx;
      CHECK(cross != 0,
            "two drawing edges leave vertex %d on the same ray",
            vertex->index);
      return cross > 0;
    });
    std::reverse(rays.begin(), rays.end());
    CHECK(rays.size() == vertex->edges.size());
    if (rays.empty()) {
      continue;
    }
    int first = -1;
    for (int i = 0; i < (int)rays.size(); i++) {
      if (rays[i].edge == vertex->edges[0]) {
        first = i;
      }
    }
    CHECK(first >= 0);
    for (int i = 0; i < (int)rays.size(); i++) {
      if (rays[(first + i) % rays.size()].edge != vertex->edges[i]) {
        if (badVertex != nullptr) {
          *badVertex = vertex->index;
        }
        return false;
      }
    }
  }
  return true;
}
