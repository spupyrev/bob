#pragma once

#include <string>
#include <iostream>
#include <fstream>
#include <functional>

class GraphParser {
  GraphParser(const GraphParser&);
  GraphParser& operator = (const GraphParser&);

 public:
  GraphParser() {}

  bool readGraph(const std::string& filename, IOGraph& graph) const {
    auto func = static_cast<bool (GraphParser::*)(std::istream&, IOGraph&) const>(&GraphParser::readGraph);
    return wrapRead(func, filename, graph);
  }
  bool readGraph(std::istream& in, IOGraph& graph) const {
    std::stringstream input;
    input << in.rdbuf();
    input.clear();
    input.seekg(0, std::ios::beg);
    graph.clear();
    bool res = readDotGraph(input, graph);

    if (res) {
      return true;
    }

    input.clear();
    input.seekg(0, std::ios::beg);
    graph.clear();
    res = readGmlGraph(input, graph);

    if (res) {
      return true;
    }

    return false;
  }

  bool readDotGraph(const std::string& filename, IOGraph& graph) const {
    auto func = static_cast<bool (GraphParser::*)(std::istream&, IOGraph&) const>(&GraphParser::readDotGraph);
    return wrapRead(func, filename, graph);
  }
  bool readDotGraph(std::istream& in, IOGraph& graph) const;

  bool readGmlGraph(const std::string& filename, IOGraph& graph) const {
    auto func = static_cast<bool (GraphParser::*)(std::istream&, IOGraph&) const>(&GraphParser::readGmlGraph);
    return wrapRead(func, filename, graph);
  }
  bool readGmlGraph(std::istream& in, IOGraph& graph) const;

  bool writeDotGraph(const std::string& filename, IOGraph& graph) const {
    auto func = static_cast<bool (GraphParser::*)(std::ostream&, IOGraph&) const>(&GraphParser::writeDotGraph);
    return wrapWrite(func, filename, graph);
  }
  bool writeDotGraph(std::ostream& out, IOGraph& graph) const;

  bool writeGmlGraph(const std::string& filename, IOGraph& graph) const {
    auto func = static_cast<bool (GraphParser::*)(std::ostream&, IOGraph&) const>(&GraphParser::writeGmlGraph);
    return wrapWrite(func, filename, graph);
  }
  bool writeGmlGraph(std::ostream& out, IOGraph& graph) const;

 private:
  void checkFile(const std::string& filename) const {
    if (filename != "") {
      std::ifstream fileStream;
      fileStream.open(filename.c_str(), std::ios::in);

      if (!fileStream) {
        std::cerr << "input file '" << filename << "' doesn't exist\n";
        throw 20;
      }

      fileStream.close();
    }
  }

  bool wrapRead(std::function<bool(const GraphParser&, std::istream&, IOGraph&)> func, const std::string& filename, IOGraph& graph) const {
    checkFile(filename);

    if (filename != "") {
      std::ifstream fileStream;
      fileStream.open(filename.c_str(), std::ios::in);
      bool result = func(*this, fileStream, graph);
      fileStream.close();
      return result;
    } else {
      return func(*this, std::cin, graph);
    }
  }

  bool wrapWrite(std::function<bool(const GraphParser&, std::ostream&, IOGraph&)> func, const std::string& filename, IOGraph& graph) const {
    if (filename != "") {
      std::ofstream fileStream;
      fileStream.open(filename.c_str(), std::ios::out);
      bool result = func(*this, fileStream, graph);
      fileStream.close();
      return result;
    } else {
      return func(*this, std::cout, graph);
    }
  }
};
