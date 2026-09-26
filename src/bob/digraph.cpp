#include "common.h"
#include "logging.h"
#include "glucoseMain.h"
#include "sat_model.h"

#include <algorithm>
#include <vector>

using namespace std;

void encodeDirectedConstraints(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(inputGraph.edges.size() == inputGraph.direction.size(), "no edge directions");

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    int u = inputGraph.edges[i].first;
    int v = inputGraph.edges[i].second;
    if (!inputGraph.direction[i]) 
      swap(u, v);

    if (params.fixedOrder) {
      CHECK(inputGraph.getFixedIndex(u) < inputGraph.getFixedIndex(v), "fixed order does not agree with edge directions");
    } else {
      inputGraph.addNodeRel(u, v);
      // std::cerr << " encodeDirectedConstraints: (" << inputGraph.getVertexLabel(u) << ", " << inputGraph.getVertexLabel(v) << ")\n";
    }
  }
}
