#include "logging.h"
#include "glucoseMain.h"
#include "sat_model.h"

#include <vector>

using namespace std;

void addRelClause(SATModel& model, const vector<int>& v1, const vector<int>& v2, const vector<int>& v3, const vector<int>& v4) {
  MClause clause;
  for (int a : v1) {
    for (int b : v2) {
      clause.addVar( model.getRelVar(a, b, false) );
    }
  }
  for (int a : v2) {
    for (int b : v3) {
      clause.addVar( model.getRelVar(a, b, false) );
    }
  }
  for (int a : v3) {
    for (int b : v4) {
      clause.addVar( model.getRelVar(a, b, false) );
    }
  }
  model.addClause(clause);
}

void encodeDispersible(SATModel& model, InputGraph& inputGraph, Params& params) {
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();
  CHECK(n > 0 && m > 0);

  // adjacent edges on different pages
  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      int i1 = inputGraph.edges[i].first;
      int i2 = inputGraph.edges[i].second;
      CHECK(i1 < i2);

      int j1 = inputGraph.edges[j].first;
      int j2 = inputGraph.edges[j].second;
      CHECK(j1 < j2);

      if (i1 != j1 && i1 != j2 && i2 != j1 && i2 != j2) continue;

      model.addClause( MClause(model.getSamePageVar(i, j, false)) );
    }
  }
}

