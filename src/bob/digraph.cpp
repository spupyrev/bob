#include "common.h"
#include "logging.h"
#include "glucoseMain.h"
#include "sat_model.h"

#include <algorithm>
#include <vector>

using namespace std;

void encodeDirectedConstraints(SATModel& model, InputGraph& inputGraph, Params& params) {
  CHECK(inputGraph.edges.size() == inputGraph.direction.size(), "no edge directions");

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    if (inputGraph.direction[i]) {
      inputGraph.addNodeRel(inputGraph.edges[i].first, inputGraph.edges[i].second);
    } else {
      inputGraph.addNodeRel(inputGraph.edges[i].second, inputGraph.edges[i].first);
    }
  }
}
