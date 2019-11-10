#pragma once

#include "logging.h"

#include <string>
#include <vector>
#include <map>

struct InputGraph {
  int nc = -1;
  // vertices are in [0..nc); first < second
  std::vector<std::pair<int, int>> edges;

  // custom labels for edges
  std::map<int, std::string> id2label;
  // reverse mapping
  std::map<std::string, int> label2id;

  // whether an edge is allowed to be on multiple pages
  std::vector<bool> multiPage;

  // Constraints:
  // first node in the order
  int firstNode = 0;
  // pair<i, j>  ==>  node_i < node_j in the order
  std::vector<std::pair<int, int>> nodeRel;
  // edge_index -> available colors are in [0..pages)
  std::map<int, std::vector<int>> edgePages;
  // pair<i, j>  ==>  edge_i and edge_j are in the same page
  std::vector<std::pair<int, int>> samePage;
  // node -> available tracks are in [0..pages)
  std::map<int, std::vector<int>> nodeTracks;

  InputGraph() {}

  void addNodeRel(int left, int right) {
    CHECK(left != right);
    CHECK(0 <= left && left < nc);
    CHECK(0 <= right && right < nc);
    nodeRel.push_back(std::make_pair(left, right));
  }
};

enum Embedding { STACK, QUEUE, TRACK, MIXED };

struct Params {
  Embedding embedding = STACK;

  int stacks = 0;
  int queues = 0;
  int tracks = 0;

  bool trees = false;
  bool dispersible = false;
  int verbose = 0;
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

  std::string toString() const {
    std::string s = "";
    if (trees) s += " trees";
    if (dispersible) s += " dispersible";

    if (s.length() > 0 && s[0] == ' ') s = s.substr(1);
    if (s.length() == 0) s = " ";
    return "[" + s + "]";
  }
};

bool run(InputGraph& inputGraph, Params params);
