#include "logging.h"
#include "io_graph.h"
#include "glucoseMain.h"
#include "sat_model.h"

#include <iostream>
#include <fstream>
#include <algorithm>
#include <vector>
#include <cassert>
#include <queue>
#include <map>

using namespace std;

bool findBipartitionT(InputGraph& inputGraph, vector<int>& color, bool verbose) {
  int n = inputGraph.nc;
  int m = inputGraph.edges.size();
  vector<int> isolated = vector<int>(n, 0);
  // 1. run bfs
  color = vector<int>(n, -1);

  for (int i = 0; i < n; i++) {
    if (color[i] != -1) {
      continue;
    }

    int cnt = 0;
    color[i] = 0;
    queue<int> q;
    q.push(i);

    while (!q.empty()) {
      int now = q.front();
      assert(color[now] != -1);
      q.pop();
      cnt++;

      for (int i = 0; i < m; i++) {
        int i1 = inputGraph.edges[i].first;
        int i2 = inputGraph.edges[i].second;

        if (i1 == now || i2 == now) {
          int other = (i1 == now ? i2 : i1);

          if (color[other] != -1) {
            if (color[now] == color[other]) {
              return false;
            }
          } else {
            color[other] = 1 - color[now];
            q.push(other);
          }
        }
      }
    }

    if (cnt == 1) {
      isolated[i] = 1;
    }
  }

  int numWhite = 0, numBlack = 0;
  int numIsolated = 0;

  for (int i = 0; i < n; i++) {
    assert(color[i] != -1);

    if (isolated[i]) {
      numIsolated++;
      continue;
    }

    if (color[i] == 0) {
      numWhite++;
    } else {
      numBlack++;
    }
  }

  while (numWhite + numBlack < n) {
    for (int i = 0; i < n; i++) {
      if (isolated[i]) {
        if (numWhite < numBlack) {
          color[i] = 0;
          numWhite++;
        } else {
          color[i] = 1;
          numBlack++;
        }

        isolated[i] = 0;
        break;
      }
    }
  }

  return true;
}

void encodeTrees(SATModel& model, InputGraph& inputGraph, Params& params) {
  int pageCount = params.stacks + params.queues;
  CHECK(pageCount > 0);
  vector<int> firstVarFather;
  vector<int> firstVarAncestor;
  int n = inputGraph.nc;
  int m = inputGraph.edges.size();

  //create father variables
  for (int j = 0; j < pageCount; j++) {
    firstVarFather.push_back(model.addVar());
    model.addVar();

    for (int i = 1; i < m; i++) {
      model.addVar();
      model.addVar();
    }
  }

  //create ancestor variables
  for (int j = 0; j < pageCount; j++) {
    firstVarAncestor.push_back(model.addVar());

    for (int i = 0; i < n; i++) {
      for (int k = 0; k < n; k++) {
        if (i == 0 && k == 0) {
          continue;
        }

        model.addVar();
      }
    }
  }

  //create root variables
  int firstVarRoot = model.addVar();

  for (int i = 0; i < n; i++) {
    for (int j = 0; j < pageCount; j++) {
      if (i == 0 && j == 0) {
        continue;
      }

      model.addVar();
    }
  }

  //clauses:
  for (int page = 0; page < pageCount; page++) {
    for (int j = 0; j < m; j++) {
      int en1 = inputGraph.edges[j].first;
      int en2 = inputGraph.edges[j].second;
      //when an edge i is not on page page j, then both father  variables are false
      model.addClause(MClause(model.getPageVar(j, page, true), MVar(firstVarFather[page] + (2 * j), false)));
      model.addClause(MClause(model.getPageVar(j, page, true), MVar(firstVarFather[page] + (2 * j) + 1, false)));
      //when an edge is on page j, than exactly one father variable has to be true
      model.addClause(MClause(model.getPageVar(j, page, false), MVar(firstVarFather[page] + (2 * j), true), MVar(firstVarFather[page] + (2 * j) + 1, true)));
      model.addClause(MClause(model.getPageVar(j, page, false), MVar(firstVarFather[page] + (2 * j), false), MVar(firstVarFather[page] + (2 * j) + 1, false)));
      //if any node has a father it cannot be the root in tree k
      model.addClause(MClause(MVar(firstVarFather[page] + (2 * j), false), MVar(firstVarRoot + (en2 * pageCount) + page, false)));
      model.addClause(MClause(MVar(firstVarFather[page] + (2 * j) + 1, false), MVar(firstVarRoot + (en1 * pageCount) + page, false)));
    }
  }

  for (int i = 0; i < pageCount; i++) {
    for (int j = 0; j < n; j++) {
      //first: get the incident edges
      int countIEdges = 0;
      vector<int> incidentEdges;

      for (int k = 0; k < m; k++) {
        if (inputGraph.edges[k].first == j || inputGraph.edges[k].second == j) {
          incidentEdges.push_back(k);
          countIEdges++;
        }
      }

      // when no father and at least one child, it is the root
      for (int k = 0; k < countIEdges; k++) {
        MClause clause;

        for (int l = 0; l < countIEdges; l++) {
          if (inputGraph.edges[incidentEdges[l]].first == j) {
            clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[l]) + 1, true));
          } else {
            clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[l]), true));
          }
        }

        if (inputGraph.edges[incidentEdges[k]].first == j) {
          clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[k]), false));
        } else {
          clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[k]) + 1, false));
        }

        clause.addVar(MVar(firstVarRoot + (j * pageCount) + i, true));
        model.addClause(clause);
      }

      //when no child, then node is not root on page
      MClause clause;

      for (int k = 0; k < countIEdges; k++) {
        if (inputGraph.edges[incidentEdges[k]].first == j) {
          clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[k]), true));
        } else {
          clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[k]) + 1, true));
        }
      }

      clause.addVar(MVar(firstVarRoot + (j * pageCount) + i, false));
      model.addClause(clause);

      //one node cannot have two fathers
      for (int k = 0; k < countIEdges; k++) {
        for (int l = k + 1; l < countIEdges; l++) {
          MClause clause;

          if (inputGraph.edges[incidentEdges[k]].first == j) {
            clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[k]) + 1, false));
          } else {
            clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[k]), false));
          }

          if (inputGraph.edges[incidentEdges[l]].first == j) {
            clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[l]) + 1, false));
          } else {
            clause.addVar(MVar(firstVarFather[i] + (2 * incidentEdges[l]), false));
          }

          model.addClause(clause);
        }
      }
    }
  }

  for (int i = 0; i < pageCount; i++) {
    for (int j = 0; j < m; j++) {
      //ancestor relation
      int en1 = inputGraph.edges[j].first;
      int en2 = inputGraph.edges[j].second;
      //if a is father of b, then a is ancestor of b as well
      model.addClause(MClause(MVar(firstVarFather[i] + (2 * j), false), MVar(firstVarAncestor[i] + (en1 * n) + en2, true)));
      model.addClause(MClause(MVar(firstVarFather[i] + (2 * j) + 1, false), MVar(firstVarAncestor[i] + (en2 * n) + en1, true)));
    }

    //transitivity of ancestor relation
    for (int j = 0; j < n; j++) {
      for (int k = j + 1; k < n; k++) {
        for (int l = k + 1; l < n; l++) {
          model.addClause(MClause(MVar(firstVarAncestor[i] + (j * n) + k, false), MVar(firstVarAncestor[i] + (k * n) + l, false), MVar(firstVarAncestor[i] + (j * n) + l, true)));
          model.addClause(MClause(MVar(firstVarAncestor[i] + (j * n) + l, false), MVar(firstVarAncestor[i] + (l * n) + k, false), MVar(firstVarAncestor[i] + (j * n) + k, true)));
          model.addClause(MClause(MVar(firstVarAncestor[i] + (k * n) + j, false), MVar(firstVarAncestor[i] + (j * n) + l, false), MVar(firstVarAncestor[i] + (k * n) + l, true)));
          model.addClause(MClause(MVar(firstVarAncestor[i] + (k * n) + l, false), MVar(firstVarAncestor[i] + (l * n) + j, false), MVar(firstVarAncestor[i] + (k * n) + j, true)));
          model.addClause(MClause(MVar(firstVarAncestor[i] + (l * n) + j, false), MVar(firstVarAncestor[i] + (j * n) + k, false), MVar(firstVarAncestor[i] + (l * n) + k, true)));
          model.addClause(MClause(MVar(firstVarAncestor[i] + (l * n) + k, false), MVar(firstVarAncestor[i] + (k * n) + j, false), MVar(firstVarAncestor[i] + (l * n) + j, true)));
        }

        //antisymmetric relation
        model.addClause(MClause(MVar(firstVarAncestor[i] + (j * n) + k, false), MVar(firstVarAncestor[i] + (k * n) + j, false)));
      }
    }

    //if one node is root it cannot be a descendent of anyone else
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        if (j == k) {
          continue;
        }

        model.addClause(MClause(MVar(firstVarRoot + (j * pageCount) + i, false), MVar(firstVarAncestor[i] + (k * n) + j, false)));
      }
    }

    //for every page only trees: number of roots=1
    for (int j = 0; j < n; j++) {
      for (int k = j + 1; k < n; k++) {
        model.addClause(MClause(MVar(firstVarRoot + (j * pageCount) + i, false), MVar(firstVarRoot + (k * pageCount) + i, false)));
      }
    }
  }
}

void encodeAltTrees(SATModel& model, InputGraph& inputGraph, int pageCount) {
  CHECK(pageCount == 2, "only two trees are supported");
  int n = inputGraph.nc;
  int m = inputGraph.edges.size();
  CHECK(2 * n - 4 == m, "input graph is not maximal bipartite");
  vector<int> colors;
  CHECK(findBipartitionT(inputGraph, colors, pageCount), "input graph is not maximal bipartite");

  for (int i = 0; i < n; i++) {
    CHECK(colors[i] == 0 || colors[i] == 1);

    for (int j = 0; j < m; j++) {
      auto e = inputGraph.edges[j];

      if (e.first != i && e.second != i) {
        continue;
      }

      int other = -1;

      if (e.first == i) {
        other = e.second;
      }

      if (e.second == i) {
        other = e.first;
      }

      CHECK(other != -1);

      if (colors[i] == 0) {
        CHECK(colors[i] == 0 && colors[other] == 1);
        model.addClause(MClause(model.getPageVar(j, 0, false), model.getRelVar(i, other, true)));
      } else {
        CHECK(colors[i] == 1 && colors[other] == 0);
        model.addClause(MClause(model.getPageVar(j, 1, false), model.getRelVar(i, other, true)));
      }
    }
  }
}

void encodeSeparatingDecomposition(SATModel& model, InputGraph& inputGraph, Params& params) {
  CHECK(params.stacks == 2, "only two trees are supported");
  CHECK(!inputGraph.planar_edges.empty(), "planar edges are not provided");
  // source and sink on one face
  /*auto outerFace = inputGraph.planar_faces[0];
  int s = outerFace[0];
  int t = outerFace[2];
  CHECK(s != t);
  for (auto& ns : inputGraph.planar_edges[s]) {
    int e_index = inputGraph.findEdgeIndex(s, ns);
    model.addClause( MClause(model.getPageVar(e_index, 0, true)) );
  }
  for (auto& ns : inputGraph.planar_edges[t]) {
    int e_index = inputGraph.findEdgeIndex(t, ns);
    model.addClause( MClause(model.getPageVar(e_index, 1, true)) );
  }*/
  int n = inputGraph.nc;

  for (int i = 0; i < n; i++) {
    auto& adj = inputGraph.planar_edges[i];
    vector<int> edges;

    for (size_t j = 0; j < adj.size(); j++) {
      int ind = inputGraph.findEdgeIndex(i, adj[j]);
      CHECK(ind != -1);
      edges.push_back(ind);
    }

    for (size_t i1 = 0; i1 < edges.size(); i1++) {
      for (size_t i2 = i1 + 1; i2 < edges.size(); i2++) {
        for (size_t i3 = i2 + 1; i3 < edges.size(); i3++) {
          for (size_t i4 = i3 + 1; i4 < edges.size(); i4++) {
            model.addClause(MClause(model.getPageVar(edges[i1], 0, false), model.getPageVar(edges[i2], 1, false), model.getPageVar(edges[i3], 0, false), model.getPageVar(edges[i4], 1, false)));
            model.addClause(MClause(model.getPageVar(edges[i1], 1, false), model.getPageVar(edges[i2], 0, false), model.getPageVar(edges[i3], 1, false), model.getPageVar(edges[i4], 0, false)));
          }
        }
      }
    }
  }
}

// every (queue) page is a star forest with roots being the leftmost
void encodeStarConstraints(SATModel& model, InputGraph& inputGraph, Params& params) {
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
