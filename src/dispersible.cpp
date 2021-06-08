#include "logging.h"
#include "glucoseMain.h"
#include "sat_model.h"

#include <vector>

using namespace std;

void addRelClause(SATModel& model, const vector<int>& v1, const vector<int>& v2, const vector<int>& v3, const vector<int>& v4) {
  MClause clause;

  for (int a : v1) {
    for (int b : v2) {
      clause.addVar(model.getRelVar(a, b, false));
    }
  }

  for (int a : v2) {
    for (int b : v3) {
      clause.addVar(model.getRelVar(a, b, false));
    }
  }

  for (int a : v3) {
    for (int b : v4) {
      clause.addVar(model.getRelVar(a, b, false));
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

      if (i1 != j1 && i1 != j2 && i2 != j1 && i2 != j2) {
        continue;
      }

      model.addClause(MClause(model.getSamePageVar(i, j, false)));
    }
  }
}

void genSubsetsRec(int n, int k, int index, int cnt, vector<int>& cur, vector<vector<int>>& res) {
  if (cnt == k) {
    res.push_back(cur);
    return;
  }

  if (index >= n) {
    return;
  }

  // current is included, put next at next location
  cur[cnt] = index;
  genSubsetsRec(n, k, index + 1, cnt + 1, cur, res);
  // current is excluded
  genSubsetsRec(n, k, index + 1, cnt, cur, res);
}

// gen all subsets of n elements of size k
vector<vector<int>> genSubsets(int n, int k) {
  vector<vector<int>> res;
  auto cur = vector<int>(k, -1);
  genSubsetsRec(n, k, 0, 0, cur, res);
  //LOG("generated %d subsets for n = %d and k = %d", res.size(), n, k);
  return res;
}

void encodeLocal(SATModel& model, InputGraph& inputGraph, Params& params) {
  auto& edges = inputGraph.edges;
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();
  CHECK(n > 0 && m > 0);
  int local = params.local;
  CHECK(local > 0);
  int pages = params.stacks + params.queues;
  CHECK(local <= pages);

  // all vertices have adjacent edges on at most local pages
  for (int v = 0; v < n; v++) {
    vector<int> adjEdges;

    for (int j = 0; j < m; j++) {
      if (edges[j].first == v || edges[j].second == v) {
        adjEdges.push_back(j);
      }
    }

    int na = (int)adjEdges.size();

    if (na <= local) {
      continue;
    }

    CHECK(na <= 40, "large-degree graphs are not supported");
    // variable: v is adjacent to page X
    vector<int> vAdjVar;

    for (int p = 0; p < pages; p++) {
      int var = model.addVar();
      vAdjVar.push_back(var);
      MClause clause = MClause(MVar(var, false));

      for (int edgeIdx : adjEdges) {
        model.addClause(MClause(model.getPageVar(edgeIdx, p, false), MVar(var, true)));
        clause.addVar(model.getPageVar(edgeIdx, p, true));
      }

      model.addClause(clause);
    }

    // check subsets of size local+1
    auto subsets = genSubsets(pages, local + 1);

    for (auto& subset : subsets) {
      CHECK((int)subset.size() == local + 1);
      MClause clause;

      for (int p : subset) {
        clause.addVar(MVar(vAdjVar[p], false));
      }

      model.addClause(clause);
    }

    // among every subset of edges of size (local+1), two are on the same page
    auto subsets2 = genSubsets(na, local + 1);

    for (auto& subset : subsets2) {
      CHECK((int)subset.size() == local + 1);
      MClause clause;

      for (int e1 : subset) {
        for (int e2 : subset) {
          if (e1 >= e2) {
            continue;
          }

          clause.addVar(model.getSamePageVar(adjEdges[e1], adjEdges[e2], true));
        }
      }

      model.addClause(clause);
    }
  }

  if (m == n * (n - 1) / 2) {
    // complete graph
    for (int v = 0; v < n; v++) {
      for (int u = v + 1; u < n; u++) {
        inputGraph.addNodeRel(v, u);
      }
    }

    // first vertex attached to pages [0..local)
    for (int i = 1; i < n; i++) {
      for (int p = local; p < pages; p++) {
        int edgeIdx = inputGraph.findEdgeIndex(0, i);
        model.addClause(MClause(model.getPageVar(edgeIdx, p, false)));
      }
    }
  }

  // inputGraph.edgePages[0] = {0};
  for (int i = 2; i <= pages; i++) {
    for (int j = 0; j <= i - 2; j++) {
      inputGraph.edgePages[i - 2].push_back(j);
    }
  }
}
