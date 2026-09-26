#pragma once

#include "glucoseMain.h"

#include <ostream>
#include <string>

void createNodeRel(InputGraph& inputGraph, const std::string& order);
void createNodeRel(InputGraph& inputGraph, const std::string& pred,
                   const std::string& succ);
void applyNodeRelOption(InputGraph& inputGraph, const std::string& specification);
void applyEdgePagesOption(InputGraph& inputGraph, const std::string& specification);

bool checkSAT(const InputGraph& inputGraph, const Params& params, const Result& result);
void printLayoutStatistics(std::ostream& out, const InputGraph& inputGraph,
                           const Params& params, const Result& result);
Result runWithTimeout(const InputGraph& inputGraph, const Params& params,
                      int timeoutSeconds);
