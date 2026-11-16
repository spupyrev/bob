#pragma once

#include "bob/common.h"
#include "bob/logging.h"
#include "bob/io_graph.h"

#include <iostream>
#include <vector>
#include <map>
#include <algorithm>

using namespace std;

class Edge;
class Face;
class PlanarGraph;

class Vertex {
  friend class PlanarGraph;
  friend class Face;
  friend class Edge;

 public:
  Vertex(const Vertex&) = delete;
  Vertex& operator=(const Vertex&) = delete;

 public:
  // index in Graph.vertices
  int index;
  // label (typically, this is to_string(index))
  std::string label;
  // edges are in the clockwise order
  vector<Edge*> edges;

  int stNumber{-1};

 public:
  Vertex(int index): index(index) {
    label = ::to_string(index);
  }

  void addEdge(Edge* edge);
  void addEdges(std::vector<Edge*> newEdges);
  void addEdgeAfter(Edge* edge, const Edge* prev);
  void addEdgesAfter(std::vector<Edge*> newEdges, const Edge* prev);
  void addEdgeBefore(Edge* edge, const Edge* prev);
  void removeEdge(Edge* edge);
  void removeIncidentEdges(Vertex* v);

  Edge* findEdgeAfter(Edge* edge) const;
  Edge* findEdgeBefore(Edge* edge) const;
  int findEdgeIndex(const Edge* edge) const;

  int degree() const;
  std::vector<Vertex*> neighbors() const;
  bool adjacent(const Vertex* v) const;
  Edge* adjacentEdge(const Vertex* v) const;
  int commonNeighbors(const Vertex* v) const;
};

class Edge {
  friend class PlanarGraph;
  friend class Vertex;
  friend class Face;

 public:
  Edge(const Edge&) = delete;
  Edge& operator=(const Edge&) = delete;

 public:
  Vertex* source;
  Vertex* target;

 public:
  Edge(Vertex* source, Vertex* target): source(source), target(target) {}

  bool incident(const Vertex* v) const {
    return source == v || target == v;
  }

  Vertex* other(const Vertex* v) const {
    CHECK(source == v || target == v);

    if (source == v) {
      return target;
    } else {
      return source;
    }
  }

  void changeEndpoint(Vertex* orig, Vertex* newv) {
    CHECK(source == orig || target == orig);

    if (source == orig) {
      source = newv;
    } else {
      target = newv;
    }
  }

  std::string to_string() const  {
    return "(" + ::to_string(source->label) + "," + ::to_string(target->label) + ")";
  }
};

class Face {
  friend class PlanarGraph;

 public:
  // vertices and edges are in the clockwise order
  std::vector<Vertex*> vertices;
  std::vector<Edge*> edges;

 public:
  Face() {}
  Face(vector<Vertex*>& vertices, vector<Edge*>& edges): vertices(vertices), edges(edges) {}

  bool empty() const {
    return vertices.empty();
  }

  int length() const {
    return (int)vertices.size();
  }

  Vertex* operator [](int index) const {
    return vertices[index];
  }

  bool operator == (const Face& other) const {
    CHECK(vertices.size() == edges.size());
    CHECK(other.vertices.size() == other.edges.size());
    if (length() != other.length()) return false;
    const int n = length();
    if (n == 0) return true;
    for (int start = 0; start < n; start++) {
      bool matches = true;
      for (int i = 0; i < n; i++) {
        const int j = (start + i) % n;
        if (edges[i] != other.edges[j] || vertices[i] != other.vertices[j]) {
          matches = false;
          break;
        }
      }
      if (matches) return true;
    }
    return false;
  }

  bool operator != (const Face& other) const {
    return !(*this == other);
  }

  int getIndex(Vertex* v) const;

  bool contains(Edge* edge) const;

  bool contains(Vertex* v) const;

  bool hasCorner(Vertex* center, Vertex* incoming, Vertex* outgoing) const;

  Vertex* opposite(const Vertex* v) const;

  std::string to_string() const;

  void reverse();

  std::string hash() const;
};

class PlanarGraph {
 public:
  PlanarGraph(const PlanarGraph&) = delete;
  PlanarGraph& operator=(const PlanarGraph&) = delete;

  IOGraph ioGraph;
  vector<Vertex*> vertices;
  Face outerFace;
  bool directed;

 public:
  PlanarGraph(bool _directed = false): directed(_directed) {}
  ~PlanarGraph() {
    for (auto edge : extractEdges())
      delete edge;

    for (auto v : vertices)
      delete v;

    vertices.clear();
  }

  bool checkConsistency() const;
  bool checkConsistency(bool threeConnected) const;
  bool isMaximal() const;
  bool isTriangulated() const;

  void copy(const PlanarGraph& other);

  Vertex* newVertex();
  Vertex* newVertex(bool generated);
  Edge* newEdge(Vertex* v, Vertex* u);
  void removeVertex(Vertex* v);
  void removeEdge(Edge* edge);
  void removeIncidentEdges(Vertex* v);

  Vertex* randomVertex() const;
  Edge* randomEdge(Vertex* v) const;
  Edge* randomEdge() const;
  Face randomFace() const;

  std::vector<Edge*> extractEdges() const;
  vector<std::pair<int, int>> extractEdgesId() const;
  Edge* extractEdge(Vertex* v, Vertex* u) const;
  Face extractRightFace(Vertex* v, Edge* e) const;
  Face extractLeftFace(Vertex* v, Edge* e) const;
  Face faceAtCorner(Vertex* center, Vertex* incoming, Vertex* outgoing) const;
  Face extractFace(Vertex* v, Edge* e, bool) const;
  Face extractFace(const vector<Vertex*>& vertices) const;
  Face extractFace(const vector<int>& vertices) const;
  vector<Face> extractFaces(const vector<Vertex*>& vertices) const;
  vector<Face> extractFaces(const vector<int>& vertices) const;
  Face extractLongestFace() const;
  vector<Face> extractFaces(Vertex* v) const;
  vector<Face> extractFaces(bool includeOuterface=true) const;
  vector<vector<int>> extractFacesId() const;
  vector<vector<int>> adjacencyList() const;
  bool adjacent(int u, int v) const;

  void writeStats() const;
  // I/O
  void readEdges(const vector<int>& ids, const vector<vector<int>>& edges);
  void readEdges(const vector<vector<int>>& edges);
  void readEdges(const string& filename);
  void readGML(const string& filename);
  // Compute an embedding of the underlying undirected simple DOT graph.
  void readDOT(const string& filename);
  void write() const;
  void writeEdges(const string& filename) const;
  void writeEdges(std::ostream& out) const;
  void writeDot(const string& filename) const;
  void writeGraphML(const string& filename) const;
  void writeGML(const string& filename);

  int numberOfEdges() const;
  int numberOfVertices() const;
  int maxDegree() const;
  int minDegree() const;
  bool isConnected() const;
  bool is2Connected() const;
  bool is3Connected() const;
  bool is4Connected() const;
  bool isBipartite() const;

  void triangulate();
  // Add edges to triangulate a connected simple plane graph with at least three vertices.
  void triangulateByAddingEdges();
  void triangulateByStellation(bool ignoreOuterFace);
  void constructDual(PlanarGraph& dual) const;

  // BFS distances from the supplied roots; unreachable vertices have distance -1.
  std::vector<int> bfs(const std::vector<int>& start) const;
};

// Check whether coordinates indexed by vertex ID reproduce the clockwise
// rotations. On a mismatch, optionally report the vertex in badVertex.
// Collapsed edges and edges leaving a vertex along the same ray are rejected.
bool drawingMatchesClockwiseRotations(
    const PlanarGraph& graph,
    const std::vector<int>& x,
    const std::vector<long long>& y,
    int* badVertex = nullptr);
