#include "logging.h"
#include "io_graph.h"
#include "glucoseMain.h"
#include "sat_model.h"

#include <iostream>
#include <fstream>
#include <algorithm>
#include <vector>

using namespace std;

void encodeTrees(SATModel& model, const InputGraph& inputGraph, const Params& params) {
  const int pageCount = params.stacks + params.queues;
  CHECK(pageCount == params.page_num());
  CHECK(pageCount > 0);

  const int n = inputGraph.nc;
  const int m = (int)inputGraph.edges.size();

  using AdjTy = std::vector<std::vector<int>>;
  // ancestorVar(p, i, j) <=> node_i is ancestor of node_j on page p
  vector<AdjTy> ancestorVar;

  // Create variables
  for (int p = 0; p < pageCount; p++) {
    ancestorVar.push_back(AdjTy(n, std::vector<int>(n, -1)));
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i != j) {
          ancestorVar[p][i][j] = model.addVar();
          // LOG("ancestorVar[%d][%d][%d] = %d", p, i, j, ancestorVar[p][i][j]);
        }
      }
    }
  }

  // Clause1: Either i is ancestor of j or vice versa
  for (int p = 0; p < pageCount; p++) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i < j)
          model.addClause( MClause(MVar(ancestorVar[p][i][j], false), MVar(ancestorVar[p][j][i], false)) );
      }
    }
  }

  // Clause2: If there is an edge (i,j) on page p, then either i is ancestor of j or vice versa
  for (int p = 0; p < pageCount; p++) {
    for (int j = 0; j < m; j++) {
      int en1 = inputGraph.edges[j].first;
      int en2 = inputGraph.edges[j].second;
      CHECK(en1 < en2);

      model.addClause( MClause(model.getPageVar(j, p, false), MVar(ancestorVar[p][en1][en2], true), MVar(ancestorVar[p][en2][en1], true)) );
    }
  }

  // Clause3: Transitivity for ancestors
  for (int p = 0; p < pageCount; p++) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        if (i == j) continue;
        for (int k = 0; k < n; k++) {
          if (i == k || j == k) continue;
          model.addClause( MClause(MVar(ancestorVar[p][i][j], false), MVar(ancestorVar[p][j][k], false), MVar(ancestorVar[p][i][k], true)) );
        }
      }
    }
  }

  // Clause4: At most one direct ancestor on every page
  for (int p = 0; p < pageCount; p++) {
    for (int i = 0; i < n; i++) {
      std::vector<int> preds = inputGraph.getAdjacentVertices(i);    
      if (preds.size() <= 1)
        continue;

      if (preds.size() <= 5) {
        for (size_t j1 = 0; j1 < preds.size(); j1++) {
          for (size_t j2 = j1 + 1; j2 < preds.size(); j2++) {
            int e1 = inputGraph.findEdgeIndex(i, preds[j1]);
            int e2 = inputGraph.findEdgeIndex(i, preds[j2]);

            model.addClause( MClause(
              model.getPageVar(e1, p, false),
              model.getPageVar(e2, p, false),
              MVar(ancestorVar[p][preds[j1]][i], false), 
              MVar(ancestorVar[p][preds[j2]][i], false) 
            ));
          }
        }        
      } else {
        // new vars: https://www.cs.cmu.edu/~15414/s21/lectures/13-sat-encodings.pdf
        //   (ancestorVar[p][preds[0]][i], ancestorVar[p][preds[1]][i], ... )
        std::vector<int> Svars;
        for (size_t j = 0; j + 1 < preds.size(); j++) {
          Svars.push_back(model.addVar());
        }
        // rule 1
        for (size_t j = 0; j + 1 < Svars.size(); j++) {
          model.addClause( MClause(
              MVar(Svars[j], false), 
              MVar(Svars[j + 1], true)) 
          );
        }
        // rule 2
        for (size_t j = 0; j + 1 < preds.size(); j++) {
          int e = inputGraph.findEdgeIndex(preds[j], i);
          model.addClause( MClause(
              model.getPageVar(e, p, false),
              MVar(ancestorVar[p][preds[j]][i], false), 
              MVar(Svars[j], true)) 
          );
        }
        // rule 3
        for (size_t j = 0; j + 1 < preds.size(); j++) {
          int e = inputGraph.findEdgeIndex(preds[j + 1], i);
          model.addClause( MClause(
              model.getPageVar(e, p, false),
              MVar(ancestorVar[p][preds[j + 1]][i], false), 
              MVar(Svars[j], false)) 
          );
        }
      }
    }
  }

  // Clause5: disable triangles on the same page
  for (int p = 0; p < pageCount; p++) {
    for (int i = 0; i < n; i++) {
      for (int j = 0; j < n; j++) {
        for (int k = 0; k < n; k++) {
          if (i == j || i == k || j == k)
            continue;
          if (!inputGraph.hasEdge(i, j) || !inputGraph.hasEdge(i, k) || !inputGraph.hasEdge(j, k))
            continue;
          int e1 = inputGraph.findEdgeIndex(i, j);
          int e2 = inputGraph.findEdgeIndex(i, k);
          int e3 = inputGraph.findEdgeIndex(j, k);
          model.addClause( MClause(
            model.getPageVar(e1, p, false),
            model.getPageVar(e2, p, false),
            model.getPageVar(e3, p, false)
          ));
        }
      }
    }
  }
}

// every (queue) page is a star forest with roots being the leftmost
void encodeStarConstraints(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isQueue());

  // symmetry
  inputGraph.setEdgePages(inputGraph.edges[0].first, inputGraph.edges[0].second, {0});

  Adjacency adj(inputGraph.nc, inputGraph.edges);

  int n = inputGraph.nc;
  for (int v = 0; v < n; v++) {
    auto neigh = adj.getAdjacent(v);
    for (size_t j1 = 0; j1 < neigh.size(); j1++) {
      for (size_t j2 = 0; j2 < neigh.size(); j2++) {
        if (j1 == j2) continue;
        int u = neigh[j1];
        int w = neigh[j2];
        CHECK(u != w && u != v && v != w);

        int e1 = inputGraph.findEdgeIndex(v, u);
        int e2 = inputGraph.findEdgeIndex(v, w);

        // star
        model.addClause(MClause(model.getRelVar(u, v, false), model.getRelVar(v, w, false), model.getSamePageVar(e1, e2, false)));
        model.addClause(MClause(model.getRelVar(w, v, false), model.getRelVar(v, u, false), model.getSamePageVar(e1, e2, false)));
        // forward
        model.addClause(MClause(model.getRelVar(u, v, false), model.getRelVar(w, v, false), model.getSamePageVar(e1, e2, false)));
      }
    }
  }
}
