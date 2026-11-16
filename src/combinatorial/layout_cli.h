#pragma once

#include "bob/cmd_options.h"
#include "bob/graph_algorithms.h"
#include "planar_graph.h"
#include <functional>

// Common plane-graph input, generation, layout display and exclusive file output.
struct LayoutCLI {
  std::string name;
  std::function<void(CMDOptions&)> options;
  std::function<int(const CMDOptions&)> pageBound;
  std::function<std::string(const CMDOptions&)> format;
  std::function<void(PlanarGraph&, CMDOptions&, std::vector<int>&, std::map<EdgeTy, int>&)> build;
  std::function<void(const std::vector<EdgeTy>&, const std::vector<int>&)> statistics;
  std::function<void(CMDOptions&)> test;
};
int runLayoutCLI(int argc, char* argv[], const LayoutCLI& cli);
