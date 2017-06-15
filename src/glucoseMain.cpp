#include "glucoseMain.h"
#include "logging.h"
#include "sat_model.h"

#include <iostream>
#include <fstream>
#include <algorithm>
#include <vector>
#include <set>
#include <queue>
#include <map>

using namespace std;

void encodeRelative(SATModel& model, InputGraph& inputGraph) {
  int n = inputGraph.nc;

  //create variables
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      model.addRelVar(i, j);
    }
  }

  //ensure transitivity
  for (int i = 0; i < n; i++) {
    for (int j = i + 1; j < n; j++) {
      for (int k = j + 1; k < n; k++) {
        model.addClause( MClause(model.getRelVar(i, j, false), model.getRelVar(j, k, false), model.getRelVar(i, k, true)) );
        model.addClause( MClause(model.getRelVar(i, j, true), model.getRelVar(j, k, true), model.getRelVar(i, k, false)) );
      }
    }
  }
}

void encodePageVariables(SATModel& model, InputGraph& inputGraph, int pageCount) {
  int m = inputGraph.edges.size();

  // create variables
  for (int i = 0; i < m; i++) {
    for (int j = 0; j < pageCount; j++) {
      model.addPageVar(i, j);
    }
  }

  // at least one page
  for (int i = 0; i < m; i++) {
    MClause clause;
    for (int j = 0; j < pageCount; j++) {
      clause.addVar( model.getPageVar(i, j, true) );
    }

    model.addClause( clause );
  }

  // at most one page
  for (int i = 0; i < m; i++) {
    MClause clause;
    for (int j = 0; j < pageCount; j++) {
      for (int k = j + 1; k < pageCount; k++) {
        model.addClause( MClause(model.getPageVar(i, j, false), model.getPageVar(i, k, false)) );
      }
    }
  }

  // set same-page variables
  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      // add var
      model.addSamePageVar(i, j);
      //set on same page var
      for (int j1 = 0; j1 < pageCount; j1++) {
        for (int j2 = 0; j2 < pageCount; j2++) {
          model.addClause( MClause(model.getPageVar(i, j1, false), model.getPageVar(j, j2, false), model.getSamePageVar(i, j, (j1 == j2))) );
        }
      }
    }
  }
}

void encodeTrackVariables(SATModel& model, InputGraph& inputGraph, int trackCount) {
  int n = inputGraph.nc;

  // create variables
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < trackCount; j++) {
      model.addTrackVar(i, j);
    }
  }

  // at least one page
  for (int i = 0; i < n; i++) {
    MClause clause;
    for (int j = 0; j < trackCount; j++) {
      clause.addVar( model.getTrackVar(i, j, true) );
    }

    model.addClause( clause );
  }

  // at most one page
  for (int i = 0; i < n; i++) {
    MClause clause;
    for (int j = 0; j < trackCount; j++) {
      for (int k = j + 1; k < trackCount; k++) {
        model.addClause( MClause(model.getTrackVar(i, j, false), model.getTrackVar(i, k, false)) );
      }
    }
  }

  // same track variables
  for (int i = 0; i < n; i++) {
    for (int j = i + 1; j < n; j++) {
      // add var
      model.addSameTrackVar(i, j);
      //set on same track var
      for (int k = 0; k < trackCount; k++) {
        model.addClause( MClause(model.getTrackVar(i, k, false), model.getTrackVar(j, k, false), model.getSameTrackVar(i, j, true)) );
      }
    }
  }
}

void encodeTrees(SATModel& model, InputGraph& inputGraph, int pageCount) {
  if (pageCount > 3) {
  	ERROR("more than 3 trees is not supported");
  }

  vector<int> firstVarFather;
  vector<int> firstVarAncestor;

  int n = inputGraph.nc;
  int m = inputGraph.edges.size();

  //create father variables
  for (int j = 0; j < pageCount; j++) {
    firstVarFather.push_back( model.addVar() );
    model.addVar();
    for (int i = 1; i < m; i++) {
      model.addVar();
      model.addVar();
    }
  }

  //create ancestor variables
  for (int j = 0; j < pageCount; j++) {
    firstVarAncestor.push_back( model.addVar() );
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
      model.addClause( MClause(model.getPageVar(j, page, true), MVar(firstVarFather[page] + (2 * j), false)) );
      model.addClause( MClause(model.getPageVar(j, page, true), MVar(firstVarFather[page] + (2 * j) + 1, false)) );

      //when an edge is on page j, than exactly one father variable has to be true
      model.addClause( MClause(model.getPageVar(j, page, false), MVar(firstVarFather[page] + (2 * j), true), MVar(firstVarFather[page] + (2 * j) + 1, true)) );
      model.addClause( MClause(model.getPageVar(j, page, false), MVar(firstVarFather[page] + (2 * j), false), MVar(firstVarFather[page] + (2 * j) + 1, false)) );

      //if any node has a father it cannot be the root in tree k
      model.addClause( MClause(MVar(firstVarFather[page] + (2 * j), false), MVar(firstVarRoot + (en2 * pageCount) + page, false)) );
      model.addClause( MClause(MVar(firstVarFather[page] + (2 * j) + 1, false), MVar(firstVarRoot + (en1 * pageCount) + page, false)) );
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
            clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[l]) + 1, true ));
          }
          else {
            clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[l]), true ));
          }
        }

        if (inputGraph.edges[incidentEdges[k]].first == j) {
          clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[k]), false ));
        }
        else {
          clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[k]) + 1, false ));
        }

        clause.addVar(MVar( firstVarRoot + (j * pageCount) + i, true ));
        model.addClause( clause );
      }

      //when no child, then node is not root on page
      MClause clause;
      for (int k = 0; k < countIEdges; k++) {
        if (inputGraph.edges[incidentEdges[k]].first == j) {
          clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[k]), true ));
        }
        else {
          clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[k]) + 1, true ));
        }
      }
      clause.addVar(MVar( firstVarRoot + (j * pageCount) + i, false ));
      model.addClause( clause );

      //one node cannot have two fathers
      for (int k = 0; k < countIEdges; k++) {
        for (int l = k + 1; l < countIEdges; l++) {
          MClause clause;
          if (inputGraph.edges[incidentEdges[k]].first == j) {
            clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[k]) + 1, false ));
          }
          else {
            clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[k]), false ));
          }

          if (inputGraph.edges[incidentEdges[l]].first == j) {
            clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[l]) + 1, false ));
          }
          else {
            clause.addVar(MVar( firstVarFather[i] + (2 * incidentEdges[l]), false ));
          }

          model.addClause( clause );
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
      model.addClause( MClause(MVar(firstVarFather[i] + (2 * j), false), MVar(firstVarAncestor[i] + (en1 * n) + en2, true)) );

      model.addClause( MClause(MVar(firstVarFather[i] + (2 * j) + 1, false), MVar(firstVarAncestor[i] + (en2 * n) + en1, true)) );
    }

    //transitivity of ancestor relation
    for (int j = 0; j < n; j++) {
      for (int k = j + 1; k < n; k++) {
        for (int l = k + 1; l < n; l++) {
          model.addClause( MClause(MVar(firstVarAncestor[i] + (j * n) + k, false), MVar(firstVarAncestor[i] + (k * n) + l, false), MVar(firstVarAncestor[i] + (j * n) + l, true)) );

          model.addClause( MClause(MVar(firstVarAncestor[i] + (j * n) + l, false), MVar(firstVarAncestor[i] + (l * n) + k, false), MVar(firstVarAncestor[i] + (j * n) + k, true)) );

          model.addClause( MClause(MVar(firstVarAncestor[i] + (k * n) + j, false), MVar(firstVarAncestor[i] + (j * n) + l, false), MVar(firstVarAncestor[i] + (k * n) + l, true)) );

          model.addClause( MClause(MVar(firstVarAncestor[i] + (k * n) + l, false), MVar(firstVarAncestor[i] + (l * n) + j, false), MVar(firstVarAncestor[i] + (k * n) + j, true)) );

          model.addClause( MClause(MVar(firstVarAncestor[i] + (l * n) + j, false), MVar(firstVarAncestor[i] + (j * n) + k, false), MVar(firstVarAncestor[i] + (l * n) + k, true)) );

          model.addClause( MClause(MVar(firstVarAncestor[i] + (l * n) + k, false), MVar(firstVarAncestor[i] + (k * n) + j, false), MVar(firstVarAncestor[i] + (l * n) + j, true)) );
        }

        //antisymmetric relation
        model.addClause( MClause(MVar(firstVarAncestor[i] + (j * n) + k, false), MVar(firstVarAncestor[i] + (k * n) + j, false)) );
      }
    }

    //if one node is root it cannot be a descendent of anyone else
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < n; k++) {
        if (j == k) {
          continue;
        }

        model.addClause( MClause(MVar(firstVarRoot + (j * pageCount) + i, false), MVar(firstVarAncestor[i] + (k * n) + j, false)) );
      }
    }

    //for every page only trees: number of roots=1
    for (int j = 0; j < n; j++) {
      for (int k = j + 1; k < n; k++) {
        model.addClause( MClause(MVar(firstVarRoot + (j * pageCount) + i, false), MVar(firstVarRoot + (k * pageCount) + i, false)) );
      }
    }
  }
}

MClause crossingClause(SATModel& model, int edge1, int edge2, int a, int b, int c, int d) {
  // returns a clause forbidding pattern a < b < c < d
  return MClause(model.getSamePageVar(edge1, edge2, false), model.getRelVar(a, b, true), model.getRelVar(b, c, true), model.getRelVar(c, d, true));
}

MClause XClause(SATModel& model, int edge1, int edge2, int x, int y, int u, int v) {
  // returns a clause forbidding an X-cross
  return MClause(model.getSamePageVar(edge1, edge2, false), model.getSameTrackVar(x, v, false), model.getSameTrackVar(y, u, false), model.getRelVar(x, v, true), model.getRelVar(u, y, true));
}

void encodeStackEdge(SATModel& model, InputGraph& inputGraph, int index, Params params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (e1n1 == e2n1 || e1n1 == e2n2 || e1n2 == e2n1 || e1n2 == e2n2) {
      continue;
    }

    // forbid crossings between i-th and index-th
    model.addClause( crossingClause(model, i, index, e1n1, e2n1, e1n2, e2n2) );
    model.addClause( crossingClause(model, i, index, e1n1, e2n2, e1n2, e2n1) );
    model.addClause( crossingClause(model, i, index, e1n2, e2n1, e1n1, e2n2) );
    model.addClause( crossingClause(model, i, index, e1n2, e2n2, e1n1, e2n1) );

    model.addClause( crossingClause(model, i, index, e2n1, e1n1, e2n2, e1n2) );
    model.addClause( crossingClause(model, i, index, e2n1, e1n2, e2n2, e1n1) );
    model.addClause( crossingClause(model, i, index, e2n2, e1n1, e2n1, e1n2) );
    model.addClause( crossingClause(model, i, index, e2n2, e1n2, e2n1, e1n1) );
  }
}

void encodeQueueEdge(SATModel& model, InputGraph& inputGraph, int index, Params params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (e1n1 == e2n1 || e1n1 == e2n2 || e1n2 == e2n1 || e1n2 == e2n2) {
      continue;
    }

    // forbid nestings between i-th and index-th
    model.addClause( crossingClause(model, i, index, e1n1, e2n1, e2n2, e1n2) );
    model.addClause( crossingClause(model, i, index, e1n1, e2n2, e2n1, e1n2) );
    model.addClause( crossingClause(model, i, index, e1n2, e2n1, e2n2, e1n1) );
    model.addClause( crossingClause(model, i, index, e1n2, e2n2, e2n1, e1n1) );

    model.addClause( crossingClause(model, i, index, e2n1, e1n1, e1n2, e2n2) );
    model.addClause( crossingClause(model, i, index, e2n1, e1n2, e1n1, e2n2) );
    model.addClause( crossingClause(model, i, index, e2n2, e1n1, e1n2, e2n1) );
    model.addClause( crossingClause(model, i, index, e2n2, e1n2, e1n1, e2n1) );
  }
}

void encodeTrackEdge(SATModel& model, InputGraph& inputGraph, int index, Params params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  // every edge spans two tracks
  model.addClause( MClause(model.getSameTrackVar(e1n1, e1n2, false)) );

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (e1n1 == e2n1 || e1n1 == e2n2 || e1n2 == e2n1 || e1n2 == e2n2) {
      continue;
    }

    // forbid x-crosses
    model.addClause( XClause(model, i, index, e1n1, e1n2, e2n1, e2n2) );
    model.addClause( XClause(model, i, index, e1n1, e1n2, e2n2, e2n1) );
    model.addClause( XClause(model, i, index, e1n2, e1n1, e2n1, e2n2) );
    model.addClause( XClause(model, i, index, e1n2, e1n1, e2n2, e2n1) );

    model.addClause( XClause(model, i, index, e2n1, e2n2, e1n1, e1n2) );
    model.addClause( XClause(model, i, index, e2n1, e2n2, e1n2, e1n1) );
    model.addClause( XClause(model, i, index, e2n2, e2n1, e1n1, e1n2) );
    model.addClause( XClause(model, i, index, e2n2, e2n1, e1n2, e1n1) );
  }
}

void encodeMixedEdge(SATModel& model, InputGraph& inputGraph, int index, Params params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no constraints for adjacent edges
    if (!params.dispersible && (e1n1 == e2n1 || e1n1 == e2n2 || e1n2 == e2n1 || e1n2 == e2n2)) {
      continue;
    }

    // forbid crossings between i-th and index-th on page 0
    model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n1, e1n2, e2n2), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n2, e1n2, e2n1), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n1, e1n1, e2n2), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n2, e1n1, e2n1), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );

    model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n1, e2n2, e1n2), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n2, e2n2, e1n1), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n1, e2n1, e1n2), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n2, e2n1, e1n1), model.getPageVar(i, 0, false), model.getPageVar(index, 0, false)) );

    // forbid nestings between i-th and index-th on page 1
    model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n1, e2n2, e1n2), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n2, e2n1, e1n2), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n1, e2n2, e1n1), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n2, e2n1, e1n1), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );

    model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n1, e1n2, e2n2), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n2, e1n1, e2n2), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n1, e1n2, e2n1), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
    model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n2, e1n1, e2n1), model.getPageVar(i, 1, false), model.getPageVar(index, 1, false)) );
  }
}

void encodeStack(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isStack());
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.pages);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeStackEdge(model, inputGraph, i, params);
  }
}

void encodeQueue(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isQueue());
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.pages);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeQueueEdge(model, inputGraph, i, params);
  }
}

void encodeTrack(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isTrack());
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.pages);
  encodeTrackVariables(model, inputGraph, params.tracks);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeTrackEdge(model, inputGraph, i, params);
  }

  if (params.span > 0) {
    // adding span constraints
    CHECK(params.span <= params.tracks - 1);
    for (auto& edge : inputGraph.edges) {
      int u = edge.first;
      int v = edge.second;
      for (int i = 0; i < params.tracks; i++) {
        for (int j = i + 1; j < params.tracks; j++) {
          if (j - i > params.span) {
            model.addClause( MClause(model.getTrackVar(u, i, false), model.getTrackVar(v, j, false)) );
            model.addClause( MClause(model.getTrackVar(u, j, false), model.getTrackVar(v, i, false)) );
          }
        }
      }
    }
  }
}

void encodeMixed(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isMixed());
  CHECK(params.pages == 2, "mixed layouts are supported for two pages only");
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.pages);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeMixedEdge(model, inputGraph, i, params);
  }
}

void encodeSymmetryConstraints(SATModel& model, InputGraph& inputGraph, Params params) {
  int n = inputGraph.nc;

  map<int, vector<int> > adj;
  for (auto& edge : inputGraph.edges) {
    int u = edge.first;
    int v = edge.second;
    adj[u].push_back(v);
    adj[v].push_back(u);
  }
  // (ignoring nodes 0, 1 and 2)
  map<vector<int>, vector<int> > groups;
  for (int i = 3; i < n; i++) {
    std::sort(adj[i].begin(), adj[i].end());
    groups[adj[i]].push_back(i);
  }

  int cnt = 0;
  for (auto& pr : groups) {
    auto group = pr.second;
    if (group.size() <= 1) continue;

    cnt++;
    sort(group.begin(), group.end());
    for (size_t i = 0; i < group.size(); i++) {
      for (size_t j = i + 1; j < group.size(); j++) {
        //cerr << (group[i] + 1) << " " << (group[j] + 1) << "\n";
        model.addClause( MClause(model.getRelVar(group[i], group[j], true)) );
      }
    }
  }
  LOG_IF(params.verb && cnt > 0, "identified %d similarity groups...", cnt);
}

void encodeConstraints(SATModel& model, InputGraph& inputGraph, Params params) {
  int pageCount = params.pages;
  int n = inputGraph.nc;

  // Basic Constraints
  if (inputGraph.nodeRel.empty() && inputGraph.edgePages.empty() && inputGraph.nodeTracks.empty()) {
    LOG_IF(params.verb, "adding basic constraints to break symmetry");

    // STACK
    if (params.isStack()) {
      // set node 1 as the first one on the spine
      for (int i = 0; i < n; i++) {
        if (i == inputGraph.firstNode) continue;
        auto rel = make_pair(inputGraph.firstNode, i);
        inputGraph.nodeRel.push_back(rel);
      }

      // set the direction of the spine: 1 < 2
      if (n >= 3) {
        auto rel = make_pair(1, 2);
        inputGraph.nodeRel.push_back(rel);
      }

      // edge 0 on the last page
      if (!params.dispersible) {
        inputGraph.edgePages[0].push_back(pageCount - 1);
      }
    }
    // QUEUE
    if (params.isQueue()) {
      // set the direction of the spine: 1 < 2
      if (n >= 3) {
        auto rel = make_pair(1, 2);
        inputGraph.nodeRel.push_back(rel);
      }
      // edge 0 on the last page
      if (!params.dispersible) {
	      inputGraph.edgePages[0].push_back(pageCount - 1);
	    }
    }
    // TRACK
    if (params.isTrack()) {
      // set node 1 on the first track, adjacent node x on the second and assume 1 < x

      if (params.span == 0) {
        int f = inputGraph.firstNode;
        inputGraph.nodeTracks[f].push_back(0);

        int x = -1;
        for (auto e : inputGraph.edges) {
          if (e.first == f) {x = e.second; break;}
          if (e.second == f) {x = e.first; break;}
        }
        if (x != -1) {
          inputGraph.nodeTracks[x].push_back(1);
        }
      }
    }
    // MIXED
    if (params.isMixed()) {
      // set the direction of the spine: 1 < 2
      if (n >= 3) {
        auto rel = make_pair(1, 2);
        inputGraph.nodeRel.push_back(rel);
      }
    }

    // breaking symmetry: relative order for isomorphic vertices
    encodeSymmetryConstraints(model, inputGraph, params);
  }

  // Custom Constraints
  for (size_t i = 0; i < inputGraph.nodeRel.size(); i++) {
    auto pr = inputGraph.nodeRel[i];
    CHECK(0 <= pr.first && pr.first < n);
    CHECK(0 <= pr.second && pr.second < n);
    CHECK(pr.first != pr.second);

    model.addClause( MClause(model.getRelVar(pr.first, pr.second, true)) );
  }

  for (auto pr : inputGraph.edgePages) {
    int index = pr.first;
    auto& pages = pr.second;
    MClause clause;
    for (int page : pages) {
      CHECK(0 <= pr.first && pr.first < (int)inputGraph.edges.size());
      CHECK(0 <= page && page < pageCount);

      clause.addVar( model.getPageVar(index, page, true));
    }
    model.addClause( clause );
  }

  for (auto pr : inputGraph.nodeTracks) {
    CHECK(0 <= pr.first && pr.first < inputGraph.nc);

    int index = pr.first;
    auto& tracks = pr.second;
    MClause clause;
    for (int track : tracks) {
      CHECK(0 <= track && track < params.tracks);

      clause.addVar( model.getTrackVar(index, track, true));
    }
    model.addClause( clause );
  }
}

void encodeDispersible(SATModel& model, InputGraph& inputGraph, Params& params);

int dispersibleLowerBound(InputGraph& inputGraph, Params& params) {
  // maxdegree
  int lb = 0;
  vector<int> degree(inputGraph.nc, 0);
  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    int i1 = inputGraph.edges[i].first;
    int i2 = inputGraph.edges[i].second;
    degree[i1]++;
    degree[i2]++;
    lb = max(lb, degree[i1]);
    lb = max(lb, degree[i2]);
  }
  return lb;
}

int stackLowerBound(InputGraph& inputGraph, Params& params) {
  set<pair<int, int> > edges;
  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    int i1 = inputGraph.edges[i].first;
    int i2 = inputGraph.edges[i].second;
    if (i1 == i2) continue;
    if (i1 > i2) swap(i1, i2);
    edges.insert(make_pair(i1, i2));
  }

  int n = inputGraph.nc;
  int m = edges.size();
  int lb = (m - n + n - 4) / (n - 3);
  lb = max(lb, 1);

  if (params.dispersible) {
  	lb = max(lb, dispersibleLowerBound(inputGraph, params));
  }

  return lb;
}

int queueLowerBound(InputGraph& inputGraph, Params& params) {
  int n = inputGraph.nc;
  int m = inputGraph.edges.size();
  for (int k = 0; k <= params.pages; k++) {
    int maxEdges = 2*k*n - k*(2*k+1);
    if (maxEdges >= m) return max(k, dispersibleLowerBound(inputGraph, params));
  }
  return max(params.pages + 1, dispersibleLowerBound(inputGraph, params));
}

int trackLowerBound(InputGraph& inputGraph, Params& params) {
  int n = inputGraph.nc;
  int m = inputGraph.edges.size();
  for (int k = 1; k <= params.tracks; k++) {
    int maxEdges = (k - 1) * n - k * (k - 1) / 2;
    if (maxEdges >= m) return k;
  }
  return params.tracks + 1;
}

int mixedLowerBound(InputGraph& inputGraph, Params& params) {
	if (params.pages > 2 || (params.dispersible && dispersibleLowerBound(inputGraph, params) > 2)) {
		return params.pages + 1;
	}
	return 2;
}

bool runInternal(InputGraph& inputGraph, Params params) {
  int lbPages = -1;
  int ubPages = params.pages;
  if (params.isStack()) {
  	lbPages = stackLowerBound(inputGraph, params);
    LOG_IF(params.verb, "lower bound for stack thickness: %d", lbPages);
  } else if (params.isQueue()) {
    lbPages = queueLowerBound(inputGraph, params);
    LOG_IF(params.verb, "lower bound for queue thickness: %d", lbPages);
  } else if (params.isTrack()) {
    lbPages = trackLowerBound(inputGraph, params);
    ubPages = params.tracks;
    LOG_IF(params.verb, "lower bound for track thickness: %d", lbPages);
  } else if (params.isMixed()) {
    lbPages = mixedLowerBound(inputGraph, params);
    LOG_IF(params.verb, "lower bound for mixed thickness: %d", lbPages);
  } else {
    ERROR("wrong type of layout");
  }

	if (lbPages > ubPages) {
    LOG_IF(params.verb, "lower bound exceeds input parameter");
  	return false;
	}

  SATModel model;

  // encoding
  if (params.isStack()) {
    LOG_IF(params.verb, "encoding model for stack embedding...");
    encodeStack(model, inputGraph, params);
  } else if (params.isQueue()) {
    LOG_IF(params.verb, "encoding model for queue embedding...");
    encodeQueue(model, inputGraph, params);
  } else if (params.isTrack()) {
    LOG_IF(params.verb, "encoding model for track embedding...");
    encodeTrack(model, inputGraph, params);
  } else if (params.isMixed()) {
    LOG_IF(params.verb, "encoding model for mixed embedding...");
    encodeMixed(model, inputGraph, params);
  }

  if (params.trees) {
    LOG_IF(params.verb, "encoding trees...");
    encodeTrees(model, inputGraph, params.pages);
  }

  LOG_IF(params.verb, "encoding constraints...");
  encodeConstraints(model, inputGraph, params);

  if (params.dispersible) {
    LOG_IF(params.verb, "encoding dispersible constraints...");
    encodeDispersible(model, inputGraph, params);
  }

  LOG_IF(params.verb, "encoded %d variables and %d constraints", model.varCount(), model.clauseCount());
  model.toDimacs(params.modelFile);
  LOG_IF(params.verb, "SAT model in dimacs format saved to '%s'", params.modelFile.c_str());
  return true;
}

bool run(InputGraph inputGraph, Params params) {
	bool res;
  try {
    res = runInternal(inputGraph, params);
  } catch (...) {
  	res = false;
  	ERROR("exception during SAT model construction");
  }
  return res;
}
