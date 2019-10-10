#include "logging.h"
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

void encodeTrees(SATModel& model, InputGraph& inputGraph, Params& params) {
  int pageCount = params.stacks + params.queues;
  CHECK(pageCount > 0);

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
