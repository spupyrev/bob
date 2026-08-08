#pragma once

#include "common.h"

#include <string>
#include <vector>
#include <map>
#include <cassert>

class Attr {
 public:
  std::map<std::string, std::string> attr;

 public:
  std::string getAttr(const std::string& key) const {
    if (attr.count(key) == 0) {
      std::cerr << "attribute '" << key << "' not found" << "\n";
    }

    auto it = attr.find(key);
    assert(it != attr.end());
    return it->second;
  }

  std::string getAttr(const std::string& key, const std::string& defaultValue) const {
    if (attr.count(key) == 0) {
      return defaultValue;
    }

    auto it = attr.find(key);
    assert(it != attr.end());
    return it->second;
  }

  double getDoubleAttr(const std::string& key) const {
    auto value = getAttr(key);
    return to_double(value);
  }

  void setDoubleAttr(const std::string& key, double value) {
    setAttr(key, to_string(value));
  }

  void setAttr(const std::string& key, const std::string& value) {
    attr[key] = value;
  }

  void setAttr(const std::map<std::string, std::string>& attr_) {
    attr = attr_;
  }

  bool hasAttr(const std::string& key) const {
    return (attr.find(key) != attr.end());
  }

  void removeAttr(const std::string& key) {
    if (attr.find(key) != attr.end()) {
      attr.erase(attr.find(key));
    }
  }
};

class IONode : public Attr {
 public:
  IONode(const IONode&) = delete;
  IONode(IONode&&) = default;
  IONode& operator=(const IONode&) = delete;
  IONode& operator=(IONode&&) = default;

  int index;
  std::string id;

  IONode(int index, const std::string& id): index(index), id(id) {}

  void setX(double x) {
    setDoubleAttr("x", x);
  }
  void setY(double y) {
    setDoubleAttr("y", y);
  }
};

class IOEdge : public Attr {
 public:
  IOEdge(const IOEdge&) = delete;
  IOEdge(IOEdge&&) = default;
  IOEdge& operator=(const IOEdge&) = delete;
  IOEdge& operator=(IOEdge&&) = default;

  std::string source;
  std::string target;

  IOEdge(const std::string& source, const std::string& target): source(source), target(target) {}
};

class IOGraph {
 public:
  IOGraph(const IOGraph&) = delete;
  IOGraph& operator = (const IOGraph&) = delete;

  IOGraph() {}
  ~IOGraph() {}

  void clear() {
    id2styleIdx.clear();
    id2nodeIdx.clear();
    id2edgeIdx.clear();
    style.clear();
    nodes.clear();
    edges.clear();
  }

  std::vector<IONode> style;
  std::vector<IONode> nodes;
  std::vector<IOEdge> edges;

  std::map<std::string, size_t> id2styleIdx;
  std::map<std::string, size_t> id2nodeIdx;
  std::map<std::pair<std::string, std::string>, size_t> id2edgeIdx;

  IONode* addNode(const std::string& id) {
    assert(getNode(id) == nullptr);
    nodes.emplace_back((int)nodes.size(), id);
    id2nodeIdx[id] = nodes.size() - 1;
    return &nodes.back();
  }

  IOEdge* addEdge(const std::string& source, const std::string& target) {
    assert(getOrCreateNode(source) != nullptr);
    assert(getOrCreateNode(target) != nullptr);
    edges.emplace_back(source, target);
    id2edgeIdx[std::make_pair(source, target)] = edges.size() - 1;
    return &edges.back();
  }

  IONode* getOrCreateNode(const std::string& id) {
    auto it = id2nodeIdx.find(id);
    return it == id2nodeIdx.end() ? addNode(id) : &nodes[it->second];
  }

  IONode* getNode(const std::string& id) {
    auto it = id2nodeIdx.find(id);
    return it == id2nodeIdx.end() ? nullptr : &nodes[it->second];
  }

  IOEdge* getEdge(const std::string& source, const std::string& target) {
    auto pair = std::make_pair(source, target);
    auto it = id2edgeIdx.find(pair);

    if (it == id2edgeIdx.end()) {
      pair = std::make_pair(target, source);
      it = id2edgeIdx.find(pair);
    }

    return it == id2edgeIdx.end() ? nullptr : &edges[it->second];
  }

  IONode* addStyle(const std::string& id) {
    auto it = id2styleIdx.find(id);
    assert(it == id2styleIdx.end());
    style.emplace_back((int)style.size(), id);
    id2styleIdx[id] = style.size() - 1;
    return &style.back();
  }

  void checkConsistency() const {
    for (size_t i = 0; i < nodes.size(); i++) {
      auto& node = nodes[i];
      assert(node.index == (int)i);
      assert(id2nodeIdx.find(node.id)->second == i);
    }

    for (auto& edge : edges) {
      assert(id2nodeIdx.find(edge.source) != id2nodeIdx.end());
      assert(id2nodeIdx.find(edge.target) != id2nodeIdx.end());
    }
  }

  bool empty() const {
    return nodes.size() == 0;
  }
};
