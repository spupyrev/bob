#pragma once

#include <string>
#include <vector>
#include <map>

struct InputGraph {
  int nc;
  // vertices are in [0..nc)
  std::vector<std::pair<int, int>> edges;

  // Constraints:
  // first node in the order
  int firstNode;
  // pair<i, j>  ==>  node_i < node_j in the order
  std::vector<std::pair<int, int>> nodeRel;
  // edge_index -> available colors are in [0..pages)
  std::map<int, std::vector<int>> edgePages;
  // node -> available tracks are in [0..pages)
  std::map<int, std::vector<int>> nodeTracks;

  InputGraph() {
    nc = -1;
    firstNode = 0;
  }

  int findEdgeIndex(int u, int v) {
    for (int i = 0; i < (int)edges.size(); i++) {
      if (edges[i].first == u && edges[i].second == v) return i;
      if (edges[i].first == v && edges[i].second == u) return i;
    }
    throw 1;
  }
};

enum Embedding { STACK, QUEUE, TRACK, MIXED };

struct Params {
  Embedding embedding;

  bool trees;
  bool dispersible;
  int pages;
  int tracks;
  // max edge span (used for Track layouts only)
  int span;

  std::string modelFile;
  bool verb;

  Params() {
    embedding = STACK;
    trees = false;
    dispersible = false;
    pages = 0;
    tracks = 0;
    span = 0;
    modelFile = "";
    verb = false;
  }

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
};

bool run(InputGraph inputGraph, Params params);
