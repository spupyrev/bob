#include "common.h"
#include "glucoseMain.h"
#include "logging.h"
#include "sat_model.h"
#include "sat_utils.h"
#include "stacks.h"

#include "glucose/SolverSimp21.h"

#include <iostream>
#include <algorithm>
#include <vector>
#include <set>
#include <queue>
#include <map>
#include <functional>

using namespace std;

void encodeRelative(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (params.fixedOrder)
    return;

  int n = inputGraph.nc;

  // Create variables
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      model.addRelVar(i, j);
    }
  }

  // Ensure transitivity
  for (int i = 0; i < n; i++) {
    for (int j = i + 1; j < n; j++) {
      for (int k = j + 1; k < n; k++) {
        model.addClause(MClause(model.getRelVar(i, j, false), model.getRelVar(j, k, false), model.getRelVar(i, k, true)));
        model.addClause(MClause(model.getRelVar(i, j, true), model.getRelVar(j, k, true), model.getRelVar(i, k, false)));
      }
    }
  }
}

void encodePageVariables(SATModel& model, InputGraph& inputGraph, const Params& params, int pageCount) {
  const int m = (int)inputGraph.edges.size();

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
      clause.addVar(model.getPageVar(i, j, true));
    }

    model.addClause(clause);
  }

  // at most one page
  for (int e = 0; e < m; e++) {
    if (inputGraph.isMultiPage(e))
      continue;

    for (int j = 0; j < pageCount; j++) {
      for (int k = j + 1; k < pageCount; k++) {
        model.addClause(MClause(model.getPageVar(e, j, false), model.getPageVar(e, k, false)));
      }
    }
  }

  // TODO: implement a more granular skip based on the type of layout
  auto needSamePageVarsFunc = [&]() {
    if (!inputGraph.samePage.empty())
      return true;
    if (!inputGraph.distinctPage.empty())
      return true;
    if (params.local)
      return true;
    if (contains(params.constraints, "dispersable"))
      return true;
    if (params.strict)
      return true;
    if (contains(params.constraints, "star"))
      return true;
    return false;
  };

  const bool needSamePageVars = needSamePageVarsFunc();

  // Set same-page variables
  for (int i = 0; i < m; i++) {
    for (int j = i + 1; j < m; j++) {
      // Skip creation of variables, if possible
      if (!needSamePageVars) {
        // The RIQUE encoding uses page variables directly.
        if (params.isRique())
          continue;
        // Do not create variables for adjacent edges, since they never cross/nest each other
        if (inputGraph.adjacent(i, j))
          continue;
        // For a fixed order, do not create constraints for non-nested/non-crossed edges
        if (params.fixedOrder && !inputGraph.edgesNest(i, j) && !inputGraph.edgesCross(i, j))
          continue;
      }

      // add var
      model.addSamePageVar(i, j);

      if (!inputGraph.isMultiPage()) {
        // set on same page var (TODO: need to use this, when distinctPages are on)
        for (int p1 = 0; p1 < pageCount; p1++) {
          for (int p2 = 0; p2 < pageCount; p2++) {
            if (p1 == p2)
              model.addClause( MClause(model.getPageVar(i, p1, false), model.getPageVar(j, p2, false), model.getSamePageVar(i, j, true)) );
            else
              model.addClause( MClause(model.getPageVar(i, p1, false), model.getPageVar(j, p2, false), model.getSamePageVar(i, j, false)) );
          }
        }
        // // page_i & page_i => same_page
        // for (int k = 0; k < pageCount; k++) {
        //   model.addClause( MClause(model.getPageVar(i, k, false), model.getPageVar(j, k, false), model.getSamePageVar(i, j, true)) );
        // }
      } else {
        // add vars onSamePageK
        vector<int> pageKVar;
        for (int page = 0; page < pageCount; page++) {
          int var = model.addVar();
          pageKVar.push_back(var);
          // both on page K        => i on page K and j on page K
          model.addClause(MClause(MVar(var, false), model.getPageVar(i, page, true)));
          model.addClause(MClause(MVar(var, false), model.getPageVar(j, page, true)));
          // at most one on page K => either i not page K or j not on page K
          model.addClause(MClause(MVar(var, true), model.getPageVar(i, page, false), model.getPageVar(j, page, false)));
        }

        // Set samePageVar
        // - samePage=true  => at least one common page
        MClause clause(model.getSamePageVar(i, j, false));
        for (int page = 0; page < pageCount; page++) {
          clause.addVar(MVar(pageKVar[page], true));
        }
        model.addClause(clause);

        // - samePage=false => no common pages
        for (int page = 0; page < pageCount; page++) {
          model.addClause(MClause(model.getSamePageVar(i, j, true), model.getPageVar(i, page, false), model.getPageVar(j, page, false)));
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

  // at least one track per vertex
  for (int i = 0; i < n; i++) {
    MClause clause;

    for (int j = 0; j < trackCount; j++) {
      clause.addVar(model.getTrackVar(i, j, true));
    }

    model.addClause(clause);
  }

  // at most one track per vertex
  for (int i = 0; i < n; i++) {
    MClause clause;

    for (int j = 0; j < trackCount; j++) {
      for (int k = j + 1; k < trackCount; k++) {
        model.addClause(MClause(model.getTrackVar(i, j, false), model.getTrackVar(i, k, false)));
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
        model.addClause(MClause(model.getTrackVar(i, k, false), model.getTrackVar(j, k, false), model.getSameTrackVar(i, j, true)));
      }
    }
  }

  // track i before track j for all i < j
  /*for (int i = 0; i < trackCount; i++) {
    for (int j = i + 1; j < trackCount; j++) {
      for (int v = 0; v < n; v++) {
        for (int u = 0; u < n; u++) {
          if (v == u) continue;
          // u on track_i && v on track_j => u < v
          model.addClause( MClause(model.getTrackVar(u, i, false), model.getTrackVar(v, j, false), model.getRelVar(u, v, true)) );
        }
      }
    }
  }*/
}

MClause crossingClause(SATModel& model, InputGraph& inputGraph, const Params& params, int edge1, int edge2, int a, int b, int c, int d) {
  if (params.fixedOrder) {
    const int aIdx = inputGraph.getFixedIndex(a);
    const int bIdx = inputGraph.getFixedIndex(b);
    const int cIdx = inputGraph.getFixedIndex(c);
    const int dIdx = inputGraph.getFixedIndex(d);
    if (aIdx < bIdx && bIdx < cIdx && cIdx < dIdx) {
      return MClause(model.getSamePageVar(edge1, edge2, false));
    } else {
      return MClause(model.trueVar());
    }
  }
  // returns a clause forbidding pattern a < b < c < d
  return MClause(model.getSamePageVar(edge1, edge2, false), model.getRelVar(a, b, true), model.getRelVar(b, c, true), model.getRelVar(c, d, true));
}

MClause strictClause(SATModel& model, int edge1, int edge2, int u, int v1, int v2, bool left) {
  // forbids u < v1,v2 on the same page [with left = true]
  // forbids v1,2 < u on the same page [with left = false]
  if (left) {
    return MClause(model.getSamePageVar(edge1, edge2, false), model.getRelVar(u, v1, false), model.getRelVar(u, v2, false));
  } else {
    return MClause(model.getSamePageVar(edge1, edge2, false), model.getRelVar(v1, u, false), model.getRelVar(v2, u, false));
  }
}

MClause XClause(SATModel& model, int edge1, int edge2, int x, int y, int u, int v) {
  // returns a clause forbidding an X-cross
  return MClause(model.getSamePageVar(edge1, edge2, false), model.getSameTrackVar(x, v, false), model.getSameTrackVar(y, u, false), model.getRelVar(x, v, true), model.getRelVar(u, y, true));
}

void encodeStackEdge(SATModel& model, InputGraph& inputGraph, int index, const Params& params) {
  const int e1n1 = inputGraph.edges[index].first;
  const int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  for (int i = 0; i < index; i++) {
    const int e2n1 = inputGraph.edges[i].first;
    const int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (inputGraph.adjacent(index, i))
      continue;
    // skip creating constraints for non-crossing edges
    if (params.fixedOrder && !inputGraph.edgesCross(index, i))
      continue;

    // forbid crossings between i-th and index-th
    model.addClause(crossingClause(model, inputGraph, params, i, index, e1n1, e2n1, e1n2, e2n2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e1n1, e2n2, e1n2, e2n1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e1n2, e2n1, e1n1, e2n2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e1n2, e2n2, e1n1, e2n1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e2n1, e1n1, e2n2, e1n2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e2n1, e1n2, e2n2, e1n1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e2n2, e1n1, e2n1, e1n2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, e2n2, e1n2, e2n1, e1n1));
  }
}

void encodeQueueEdge(SATModel& model, InputGraph& inputGraph, int index, const Params& params) {
  int u1 = inputGraph.edges[index].first;
  int v1 = inputGraph.edges[index].second;
  CHECK(u1 < v1);

  for (int i = 0; i < index; i++) {
    int u2 = inputGraph.edges[i].first;
    int v2 = inputGraph.edges[i].second;
    CHECK(u2 < v2);

    // skip creating constraints for non-nesting edges
    if (params.fixedOrder && !inputGraph.edgesNest(index, i))
      continue;

    // no need to worry about adjacent edges (unless this is a strict layout)
    if (inputGraph.adjacent(index, i)) {
      if (params.strict) {
        if (u1 == u2) {
          CHECK(v1 != v2);
          model.addClause(strictClause(model, index, i, u1, v1, v2, true));
          model.addClause(strictClause(model, index, i, u1, v1, v2, false));
        }
        if (u1 == v2) {
          CHECK(v1 != u2);
          model.addClause(strictClause(model, index, i, u1, v1, u2, true));
          model.addClause(strictClause(model, index, i, u1, v1, u2, false));
        }
        if (v1 == u2) {
          CHECK(u1 != v2);
          model.addClause(strictClause(model, index, i, v1, u1, v2, true));
          model.addClause(strictClause(model, index, i, v1, u1, v2, false));
        }
        if (v1 == v2) {
          CHECK(u1 != u2);
          model.addClause(strictClause(model, index, i, v1, u1, u2, true));
          model.addClause(strictClause(model, index, i, v1, u1, u2, false));
        }
      }
      continue;
    }

    // forbid nestings between i-th and index-th
    model.addClause(crossingClause(model, inputGraph, params, i, index, u1, u2, v2, v1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, u1, v2, u2, v1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, v1, u2, v2, u1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, v1, v2, u2, u1));
    model.addClause(crossingClause(model, inputGraph, params, i, index, u2, u1, v1, v2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, u2, v1, u1, v2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, v2, u1, v1, u2));
    model.addClause(crossingClause(model, inputGraph, params, i, index, v2, v1, u1, u2));
  }
}

void encodeTrackEdge(SATModel& model, InputGraph& inputGraph, int index, const Params& params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);
  // every edge spans two tracks
  model.addClause(MClause(model.getSameTrackVar(e1n1, e1n2, false)));

  // one page => fix
  if (params.stacks + params.queues == 1) {
    model.addClause(MClause(model.getPageVar(index, 0, true)));
  }

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (inputGraph.adjacent(index, i)) {
      continue;
    }

    // forbid x-crosses
    model.addClause(XClause(model, i, index, e1n1, e1n2, e2n1, e2n2));
    model.addClause(XClause(model, i, index, e1n1, e1n2, e2n2, e2n1));
    model.addClause(XClause(model, i, index, e1n2, e1n1, e2n1, e2n2));
    model.addClause(XClause(model, i, index, e1n2, e1n1, e2n2, e2n1));
    model.addClause(XClause(model, i, index, e2n1, e2n2, e1n1, e1n2));
    model.addClause(XClause(model, i, index, e2n1, e2n2, e1n2, e1n1));
    model.addClause(XClause(model, i, index, e2n2, e2n1, e1n1, e1n2));
    model.addClause(XClause(model, i, index, e2n2, e2n1, e1n2, e1n1));
  }
}

void encodeMixedEdge(SATModel& model, InputGraph& inputGraph, int index, const Params& params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (inputGraph.adjacent(index, i)) {
      continue;
    }

    // forbid crossings between i-th and index-th edges on pages [0, params.stacks)
    for (int page = 0; page < params.stacks; page++) {
      // skip creating constraints for non-crossing edges
      if (params.fixedOrder && !inputGraph.edgesCross(index, i)) {
        continue;
      }

      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n1, e2n1, e1n2, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n1, e2n2, e1n2, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n2, e2n1, e1n1, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n2, e2n2, e1n1, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n1, e1n1, e2n2, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n1, e1n2, e2n2, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n2, e1n1, e2n1, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n2, e1n2, e2n1, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
    }

    // forbid nestings between i-th and index-th edges on pages [params.stacks, params.stacks + params.queues)
    for (int page = params.stacks; page < params.stacks + params.queues; page++) {
      // skip creating constraints for non-nesting edges
      if (params.fixedOrder && !inputGraph.edgesNest(index, i)) {
        continue;
      }
      
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n1, e2n1, e2n2, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n1, e2n2, e2n1, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n2, e2n1, e2n2, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e1n2, e2n2, e2n1, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n1, e1n1, e1n2, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n1, e1n2, e1n1, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n2, e1n1, e1n2, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
      model.addClause(MClause(crossingClause(model, inputGraph, params, i, index, e2n2, e1n2, e1n1, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)));
    }
  }
}

void encodeMixedPageEdge(SATModel& model, InputGraph& inputGraph, int index, const Params& params) {
  int e1n1 = inputGraph.edges[index].first;
  int e1n2 = inputGraph.edges[index].second;
  CHECK(e1n1 < e1n2);

  for (int i = 0; i < index; i++) {
    int e2n1 = inputGraph.edges[i].first;
    int e2n2 = inputGraph.edges[i].second;
    CHECK(e2n1 < e2n2);

    // no need to worry about adjacent edges
    if (inputGraph.adjacent(index, i)) {
      continue;
    }
    // for a fixed order, do not create constraints for non-nested/non-crossed edges
    if (params.fixedOrder && !inputGraph.edgesNest(index, i) && !inputGraph.edgesCross(index, i)) {
      continue;
    }

    for (int page = 0; page < params.mixedPages; page++) {      
      // forbid crossings between i-th and index-th edges, if the page is a stack
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n1, e2n1, e1n2, e2n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n1, e2n2, e1n2, e2n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n2, e2n1, e1n1, e2n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n2, e2n2, e1n1, e2n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n1, e1n1, e2n2, e1n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n1, e1n2, e2n2, e1n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n2, e1n1, e2n1, e1n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n2, e1n2, e2n1, e1n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false),
        model.getPageTypeVar(page, false)
      ));

      // forbid nestings between i-th and index-th edges on pages, if the page is a queue
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n1, e2n1, e2n2, e1n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n1, e2n2, e2n1, e1n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n2, e2n1, e2n2, e1n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e1n2, e2n2, e2n1, e1n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n1, e1n1, e1n2, e2n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n1, e1n2, e1n1, e2n2), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n2, e1n1, e1n2, e2n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
      model.addClause(MClause(
        crossingClause(model, inputGraph, params, i, index, e2n2, e1n2, e1n1, e2n1), 
        model.getPageVar(i, page, false), 
        model.getPageVar(index, page, false), 
        model.getPageTypeVar(page, true)
      ));
    }
  }
}

void encodeAdjacent(SATModel& model, InputGraph& inputGraph, int pageCount) {
  const int n = inputGraph.nc;

  //create variables
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      if (i == j) {
        continue;
      }

      model.addAdjVar(i, j);
    }
  }

  // v(i,j) => i < j
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      if (i == j) {
        continue;
      }

      model.addClause(MClause(model.getAdjVar(i, j, false), model.getRelVar(i, j, true)));
    }
  }

  // at least one is set
  for (int j = 1; j < n; j++) {
    MClause clause;

    for (int i = 0; i < n; i++) {
      if (i == j) {
        continue;
      }

      clause.addVar(model.getAdjVar(i, j, true));
    }

    model.addClause(clause);
  }

  // nothing is between a pair
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      if (i == j) {
        continue;
      }

      for (int x = 0; x < n; x++) {
        if (i == x || j == x) {
          continue;
        }

        model.addClause(MClause(model.getRelVar(i, x, false), model.getRelVar(x, j, false), model.getAdjVar(i, j, false)));
      }
    }
  }
}

void encodeStackLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isStack());
  encodeRelative(model, inputGraph, params);
  encodePageVariables(model, inputGraph, params, params.stacks);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeStackEdge(model, inputGraph, i, params);
  }
}

void encodeQueueLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isQueue());
  encodeRelative(model, inputGraph, params);
  encodePageVariables(model, inputGraph, params, params.queues);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeQueueEdge(model, inputGraph, i, params);
  }
}

void encodeFixedRiqueLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.fixedOrder);
  const int m = (int) inputGraph.edges.size();
  const int k = params.riques;
  std::vector<int> left(m), right(m);

  for (int e = 0; e < m; e++) {
    const int u = inputGraph.getFixedIndex(inputGraph.edges[e].first);
    const int v = inputGraph.getFixedIndex(inputGraph.edges[e].second);
    left[e] = std::min(u, v);
    right[e] = std::max(u, v);
  }

  std::vector<std::vector<int>> nesters(m), rightCrossers(m);
  for (int middle = 0; middle < m; middle++) {
    for (int other = 0; other < m; other++) {
      if (middle == other)
        continue;
      if (left[other] < left[middle] && right[middle] < right[other])
        nesters[middle].push_back(other);
      if (left[middle] < left[other] && left[other] < right[middle] &&
          right[middle] < right[other])
        rightCrossers[middle].push_back(other);
    }
  }

  size_t auxiliaryCount = 0;
  size_t implicationCount = 0;
  for (int middle = 0; middle < m; middle++) {
    if (nesters[middle].empty() || rightCrossers[middle].empty())
      continue;

    for (int page = 0; page < k; page++) {
      const int nesterVar = model.addVar();
      const int crosserVar = model.addVar();
      auxiliaryCount += 2;

      for (int edge : nesters[middle]) {
        model.addClause(MClause(
            model.getPageVar(edge, page, false),
            MVar(nesterVar, true)));
        implicationCount++;
      }
      for (int edge : rightCrossers[middle]) {
        model.addClause(MClause(
            model.getPageVar(edge, page, false),
            MVar(crosserVar, true)));
        implicationCount++;
      }

      model.addClause(MClause(
          model.getPageVar(middle, page, false),
          MVar(nesterVar, false),
          MVar(crosserVar, false)));
    }
  }

  LOG_IF(params.verbose >= 2,
         "fixed-order rique encoding: %zu auxiliary variables, %zu implication clauses",
         auxiliaryCount, implicationCount);
}

void encodeVariableRiqueLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(!params.fixedOrder);
  const int m = (int) inputGraph.edges.size();
  const int k = params.riques;
  const auto& edges = inputGraph.edges;
  size_t auxiliaryCount = 0;
  size_t implicationCount = 0;

  // For each orientation b < b' of a potential middle edge, record whether
  // its page contains a nester a < b < b' < a' and a right-crosser
  // b < c < b' < c'. Exactly one orientation of the middle edge is active.
  for (int middle = 0; middle < m; middle++) {
    for (int middleOrientation = 0; middleOrientation < 2; middleOrientation++) {
      const int b = middleOrientation == 0 ? edges[middle].first : edges[middle].second;
      const int bp = middleOrientation == 0 ? edges[middle].second : edges[middle].first;

      for (int page = 0; page < k; page++) {
        const int nesterVar = model.addVar();
        const int crosserVar = model.addVar();
        auxiliaryCount += 2;

        for (int edge = 0; edge < m; edge++) {
          if (edge == middle || inputGraph.adjacent(edge, middle))
            continue;

          for (int orientation = 0; orientation < 2; orientation++) {
            const int first = orientation == 0 ? edges[edge].first : edges[edge].second;
            const int second = orientation == 0 ? edges[edge].second : edges[edge].first;

            // edge on page and a < b < b' < a' implies nesterVar
            model.addClause(MClause(
                model.getPageVar(edge, page, false),
                model.getRelVar(first, b, false),
                model.getRelVar(b, bp, false),
                model.getRelVar(bp, second, false),
                MVar(nesterVar, true)));

            // edge on page and b < c < b' < c' implies crosserVar
            model.addClause(MClause(
                model.getPageVar(edge, page, false),
                model.getRelVar(b, first, false),
                model.getRelVar(first, bp, false),
                model.getRelVar(bp, second, false),
                MVar(crosserVar, true)));
            implicationCount += 2;
          }
        }

        model.addClause(MClause(
            model.getPageVar(middle, page, false),
            MVar(nesterVar, false),
            MVar(crosserVar, false)));
      }
    }
  }

  LOG_IF(params.verbose >= 2,
         "variable-order rique encoding: %zu auxiliary variables, %zu implication clauses",
         auxiliaryCount, implicationCount);
}

void encodeRiqueLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isRique());
  encodeRelative(model, inputGraph, params);
  encodePageVariables(model, inputGraph, params, params.riques);

  if (params.fixedOrder)
    encodeFixedRiqueLayout(model, inputGraph, params);
  else
    encodeVariableRiqueLayout(model, inputGraph, params);
}

void encodeTwistLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isTwist());
  encodeRelative(model, inputGraph, params);

  const int m = (int)inputGraph.edges.size();
  const int k = params.twists;
  const std::vector<EdgeTy> edges = inputGraph.edges;

  // Special care for a fixed order
  if (params.fixedOrder) {
    const int maxTwist = countTwist(edges, inputGraph.vertexOrder);
    // If the set of edges is a twist, then there is no solution
    if (maxTwist > k) {
      const int dummyVar = model.addVar();
      model.addClause( MClause(MVar(dummyVar, true) ));
      model.addClause( MClause(MVar(dummyVar, false) ));
    }
    // Otherwise, just skip processing
    return;
  }

  // Construct all subsets of k+1 independent edges and forbid mutual crossings
  std::vector<int> chosenEdges(k + 1, -1);
  int numSets = 0;
  auto independent = [&](int edgeI, int edgeJ) {
    if (edges[edgeI].first == edges[edgeJ].first)
      return false;
    if (edges[edgeI].first == edges[edgeJ].second)
      return false;
    if (edges[edgeI].second == edges[edgeJ].first)
      return false;
    if (edges[edgeI].second == edges[edgeJ].second)
      return false;
    return true;
  };  
  auto addCrossClause = [&](int crossVar, int a, int b, int c, int d) {
    model.addClause( MClause(MVar(crossVar, true), model.getRelVar(a, b, false), model.getRelVar(b, c, false), model.getRelVar(c, d, false)) );
  };
  auto recCollect = [&](int curIdx, int numTaken, auto&& recCollect) {
    if (numTaken == k + 1) {
      numSets++;

      // At least one pair is not crossing
      MClause allClause;
      for (size_t ei = 0; ei < chosenEdges.size(); ei++) {
        for (size_t ej = ei + 1; ej < chosenEdges.size(); ej++) {
          CHECK(chosenEdges[ei] < chosenEdges[ej]);

          const int crossIJVar = model.addVar();
          allClause.addVar(MVar(crossIJVar, false));

          const int i1 = edges[chosenEdges[ei]].first;
          const int i2 = edges[chosenEdges[ei]].second;
          CHECK(i1 < i2);
          const int j1 = edges[chosenEdges[ej]].first;
          const int j2 = edges[chosenEdges[ej]].second;
          CHECK(j1 < j2);

          // i1 < j1 < i2 < j2 => crossIJVar
          addCrossClause(crossIJVar, i1, j1, i2, j2);
          // i1 < j2 < i2 < j1 => crossIJVar
          addCrossClause(crossIJVar, i1, j2, i2, j1);
          // i2 < j1 < i1 < j2 => crossIJVar
          addCrossClause(crossIJVar, i2, j1, i1, j2);
          // i2 < j2 < i1 < j1 => crossIJVar
          addCrossClause(crossIJVar, i2, j2, i1, j1);
          // j1 < i1 < j2 < i2 => crossIJVar
          addCrossClause(crossIJVar, j1, i1, j2, i2);
          // j1 < i2 < j2 < i1 => crossIJVar
          addCrossClause(crossIJVar, j1, i2, j2, i1);
          // j2 < i1 < j1 < i2 => crossIJVar
          addCrossClause(crossIJVar, j2, i1, j1, i2);
          // j2 < i2 < j1 < i1 => crossIJVar
          addCrossClause(crossIJVar, j2, i2, j1, i1);
        }
      }
      model.addClause(allClause);
      return;
    }
    if (curIdx >= m)
      return;
    // Skip it
    recCollect(curIdx + 1, numTaken, recCollect);
    // Take it if the new edge is independent with already taken
    if (std::all_of(chosenEdges.begin(), chosenEdges.begin() + numTaken, [&](int ei) { return independent(ei, curIdx); })) {
      chosenEdges[numTaken] = curIdx;
      recCollect(curIdx + 1, numTaken + 1, recCollect);
      chosenEdges[numTaken] = -1;
    }
  };

  CHECK(!params.fixedOrder);
  recCollect(0, 0, recCollect);
  LOG_IF(params.verbose, "generated %'d subsets of size %d", numSets, k + 1);
}

void encodeTrackLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isTrack());
  encodeRelative(model, inputGraph, params);
  CHECK(params.stacks > 0, "hmm");
  encodePageVariables(model, inputGraph, params, params.stacks);
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
            model.addClause(MClause(model.getTrackVar(u, i, false), model.getTrackVar(v, j, false)));
            model.addClause(MClause(model.getTrackVar(u, j, false), model.getTrackVar(v, i, false)));
          }
        }
      }
    }
  }
}

void encodeMixedLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isMixed());
  CHECK(params.stacks >= 1 && params.queues >= 1, "incorrect page number for mixed layout");
  encodeRelative(model, inputGraph, params);
  encodePageVariables(model, inputGraph, params, params.stacks + params.queues);

  // page assignment:
  //   [0, params.stacks) are for stacks
  //   [params.stacks, params.stacks + params.queues) are for queues
  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeMixedEdge(model, inputGraph, i, params);
  }
}

void encodeMixedPageLayout(SATModel& model, InputGraph& inputGraph, const Params& params) {
  CHECK(params.isMixedPages());
  CHECK(params.stacks == 0 && params.queues == 0, "incorrect page number for mixed-page layout");

  encodeRelative(model, inputGraph, params);
  encodePageVariables(model, inputGraph, params, params.mixedPages);

  // add page types
  for (int i = 0; i < params.mixedPages; i++) {
    model.addPageTypeVar(i);
  }

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeMixedPageEdge(model, inputGraph, i, params);
  }
}

void encodeAutomorphismConstraints(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (params.fixedOrder)
    return;

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

    if (group.size() <= 1) {
      continue;
    }

    cnt++;
    sort(group.begin(), group.end());

    for (size_t i = 0; i + 1 < group.size(); i++) {
      model.addClause(MClause(model.getRelVar(group[i], group[i + 1], true)));
    }
  }

  LOG_IF(params.verbose >= 2 || (params.verbose >= 1 && cnt > 0), "identified %d similarity groups...", cnt);
}

/// Edge 0 on the first page, edge 1 on the first or second page, and so on
void encodeEdgePagesSymmetry(InputGraph& inputGraph, const Params& params) {
  const int numPages = params.page_num();
  for (int edgeIdx = 0; edgeIdx < numPages && edgeIdx < (int)inputGraph.edges.size(); edgeIdx++) {
    inputGraph.setEdgePages(edgeIdx, identity(edgeIdx + 1));
  }
}

void encodeStackSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (!params.fixedOrder) {
    // set a node as the first one on the spine
    for (int i = 0; i < inputGraph.nc; i++) {
      if (i == inputGraph.firstNode)
        continue;
      inputGraph.addNodeRel(inputGraph.firstNode, i);
    }

    // set the direction of the spine: 1 < 2
    if (inputGraph.nc >= 3)
      inputGraph.addNodeRel(1, 2);
  }

  if (!contains(params.constraints, "dispersable")) {
    encodeEdgePagesSymmetry(inputGraph, params);
  }
}

void encodeQueueSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (!params.fixedOrder) {
    // set the direction of the spine: 1 < 2
    if (inputGraph.nc >= 3) {
      inputGraph.addNodeRel(1, 2);
    }
  }

  if (!contains(params.constraints, "dispersable")) {
    encodeEdgePagesSymmetry(inputGraph, params);
  }
}

void encodeRiqueSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (!inputGraph.isMultiPage())
    encodeEdgePagesSymmetry(inputGraph, params);
}

void encodeTwistSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (params.fixedOrder)
    return;
  CHECK(!contains(params.constraints, "dispersable"));

  // set a node as the first one on the spine
  for (int i = 0; i < inputGraph.nc; i++) {
    if (i == inputGraph.firstNode)
      continue;
    inputGraph.addNodeRel(inputGraph.firstNode, i);
  }

  // set the direction of the spine: 1 < 2
  if (inputGraph.nc >= 3)
    inputGraph.addNodeRel(1, 2);
}

void encodeTrackSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  // set node 1 on the first track, adjacent node x on the second and assume 1 < x
  if (params.fixedOrder)
    return;

  if (params.span == 0) {
    for (int i = 0; i < min(inputGraph.nc, params.tracks); i++) {
      for (int t = 0; t <= i; t++) {
        inputGraph.nodeTracks[i].push_back(t);
      }
    }

    // set the direction of the spine: 1 < 2
    inputGraph.addNodeRel(1, 2);
  }
}

void encodeMixedSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (params.fixedOrder)
    return;

  // set the direction of the spine: 1 < 2
  if (inputGraph.nc >= 3) {
    inputGraph.addNodeRel(1, 2);
  }
}

void encodeMixedPagesSymmetry(SATModel& model, InputGraph& inputGraph, const Params& params) {
  if (params.fixedOrder)
    return;

  // set the direction of the spine: 1 < 2
  if (inputGraph.nc >= 3) {
    inputGraph.addNodeRel(1, 2);
  }
}

/// Constraints
void encodeTrees(SATModel& model, const InputGraph& inputGraph, const Params& params);
void encodeDispersable(SATModel& model, InputGraph& inputGraph, const Params& params);
void encodeLocal(SATModel& model, InputGraph& inputGraph, const Params& params);
void encodeDirectedConstraints(SATModel& model, InputGraph& inputGraph, const Params& params);
void encodeStarConstraints(SATModel& model, InputGraph& inputGraph, const Params& params);

void encodeAdditionalCustomConstraints(SATModel&, InputGraph&, const Params&) {
  }

bool hasAdditionalSymmetry(const Params&) {
  return false;
}

void encodeCustomConstraints(SATModel& model, InputGraph& inputGraph, const Params& params) {
  // Basic symmetry-breaking constraints
  if (params.applyBasicSymmetry && inputGraph.numCustomConstraints() == 0 &&
      !hasAdditionalSymmetry(params) && !params.applySatsuma && params.constraints.empty()) {
    LOG_IF(params.verbose, "adding symmetry-breaking constraints");

    if (params.isStack()) {
      encodeStackSymmetry(model, inputGraph, params);
    } else if (params.isQueue()) {
      encodeQueueSymmetry(model, inputGraph, params);
    } else if (params.isRique()) {
      encodeRiqueSymmetry(model, inputGraph, params);
    } else if (params.isTwist()) {
      encodeTwistSymmetry(model, inputGraph, params);
    } else if (params.isTrack()) {
      encodeTrackSymmetry(model, inputGraph, params);
    } else if (params.isMixed()) {
      encodeMixedSymmetry(model, inputGraph, params);
    } else if (params.isMixedPages()) {
      encodeMixedPagesSymmetry(model, inputGraph, params);
    }

    // breaking symmetry: relative order for isomorphic vertices
    encodeAutomorphismConstraints(model, inputGraph, params);
  } else if (inputGraph.numCustomConstraints() > 0) {
    std::sort(inputGraph.nodeRel.begin(), inputGraph.nodeRel.end());
    inputGraph.nodeRel.erase(std::unique(inputGraph.nodeRel.begin(), inputGraph.nodeRel.end()), inputGraph.nodeRel.end());   

    size_t numCons = inputGraph.numCustomConstraints();
    LOG_IF(params.verbose, "encoding %zu custom constraints...", numCons);
  }

  // Custom Constraints
  CHECK(!params.fixedOrder || inputGraph.nodeRel.empty(),
        "node-rel cannot be used with a fixed vertex order");
  LOG_IF(params.verbose >= 2 && !inputGraph.nodeRel.empty(), "  encoding %zu nodeRel constraints...", inputGraph.nodeRel.size());
  for (size_t i = 0; i < inputGraph.nodeRel.size(); i++) {
    auto rel = inputGraph.nodeRel[i];
    int l = rel.first;
    int r = rel.second;
    CHECK(0 <= l && l < inputGraph.nc, "incorrect nodeRel (%d, %d)", l, r);
    CHECK(0 <= r && r < inputGraph.nc, "incorrect nodeRel (%d, %d)", l, r);
    CHECK(l != r, "incorrect nodeRel (%d, %d)", l, r);
    LOG_IF(params.verbose >= 4, "   nodeRel constraint: (%s, %s)", inputGraph.getVertexLabel(l).c_str(), inputGraph.getVertexLabel(r).c_str());

    model.addClause(MClause(model.getRelVar(l, r, true)));
  }

  LOG_IF(params.verbose >= 2 && !inputGraph.edgePages.empty(), "  encoding %zu edgePages constraints...", inputGraph.edgePages.size());
  for (auto pr : inputGraph.edgePages) {
    const int index = pr.first;
    const auto& pages = pr.second;
    MClause clause;
    vector<bool> allowed(params.page_var_num(), false);

    for (int page : pages) {
      CHECK(0 <= pr.first && pr.first < (int)inputGraph.edges.size(), "incorrect edgePages");
      CHECK(0 <= page && page < params.page_var_num(),
            "incorrect edgePage %d >= %d", page, params.page_var_num());
      clause.addVar(model.getPageVar(index, page, true));
      allowed[page] = true;
    }

    model.addClause(clause);
    for (int page = 0; page < params.page_var_num(); page++) {
      if (!allowed[page])
        model.addClause(MClause(model.getPageVar(index, page, false)));
    }
  }

  LOG_IF(params.verbose >= 2 && !inputGraph.samePage.empty(), "  encoding %zu samePage constraints...", inputGraph.samePage.size());
  for (auto pr : inputGraph.samePage) {
    int e1 = pr.first;
    int e2 = pr.second;
    model.addClause(MClause(model.getSamePageVar(e1, e2, true)));
  }

  LOG_IF(params.verbose >= 2 && !inputGraph.distinctPage.empty(), "  encoding %zu distinctPage constraints...", inputGraph.distinctPage.size());
  for (auto pr : inputGraph.distinctPage) {
    int e1 = pr.first;
    int e2 = pr.second;
    model.addClause(MClause(model.getSamePageVar(e1, e2, false)));
  }

  LOG_IF(params.verbose >= 2 && !inputGraph.nodeTracks.empty(), "  encoding %zu nodeTracks constraints...", inputGraph.nodeTracks.size());
  for (auto pr : inputGraph.nodeTracks) {
    CHECK(0 <= pr.first && pr.first < inputGraph.nc);
    int index = pr.first;
    auto& tracks = pr.second;
    MClause clause;

    for (int track : tracks) {
      CHECK(0 <= track && track < params.tracks);
      clause.addVar(model.getTrackVar(index, track, true));
    }

    model.addClause(clause);
  }

  LOG_IF(params.verbose >= 2 && !inputGraph.sameRel.empty(), "  encoding %zu sameRel constraints...", inputGraph.sameRel.size());
  for (auto pr : inputGraph.sameRel) {
    int u1 = pr.first.first;
    int v1 = pr.first.second;
    int u2 = pr.second.first;
    int v2 = pr.second.second;
    CHECK(0 <= u1 && u1 < inputGraph.nc);
    CHECK(0 <= v1 && v1 < inputGraph.nc);
    CHECK(0 <= u2 && u2 < inputGraph.nc);
    CHECK(0 <= v2 && v2 < inputGraph.nc);

    model.addClause(MClause(model.getRelVar(u1, v1, true), model.getRelVar(u2, v2, false)));
    model.addClause(MClause(model.getRelVar(u1, v1, false), model.getRelVar(u2, v2, true)));
  }  

  LOG_IF(params.verbose >= 2 && !inputGraph.groupEdgePages.empty(), "  encoding %zu groupEdgePages constraints...", inputGraph.groupEdgePages.size());
  const int pageCount = params.page_var_num();
  for (auto& [k, edgeIndices] : inputGraph.groupEdgePages) {
    sort_unique(edgeIndices);

    // std::cerr << "group-page-" << k << "[" << edgeIndices.size() << "]:\n";
    // for (int ei : edgeIndices) {
    //   std::cerr << "  " << inputGraph.edge_to_string(ei) << "\n";
    // }
    if (k == 1) {
      // add vars for all edges pinned to page K
      MClause clause;
      for (int page = 0; page < pageCount; page++) {
        int allOnKVar = model.addVar();
        // all on page K     => i on page K and j on page K
        for (int edgeIdx : edgeIndices) {
          model.addClause(MClause(MVar(allOnKVar, false), model.getPageVar(edgeIdx, page, true)));
        }
        clause.addVar(MVar(allOnKVar, true));
      }
      model.addClause(clause);
    } else if (k == 2) {
      MClause clause;
      for (int p1 = 0; p1 < pageCount; p1++) {
        for (int p2 = 0; p2 < pageCount; p2++) {
          int allOn12Var = model.addVar();
          // all on pages p1,p2     => edge on page p1 or edge on page p2
          for (int edgeIdx : edgeIndices) {
            model.addClause(MClause(MVar(allOn12Var, false), model.getPageVar(edgeIdx, p1, true), model.getPageVar(edgeIdx, p2, true)));
          }
          clause.addVar(MVar(allOn12Var, true));
        }
      }
      model.addClause(clause);
    } else if (k == 3) {
      MClause clause;
      for (int p1 = 0; p1 < pageCount; p1++) {
        for (int p2 = 0; p2 < pageCount; p2++) {
          for (int p3 = 0; p3 < pageCount; p3++) {
            int allOn123Var = model.addVar();
            // all on pages p1,p2,p3     => edge on page p1 or edge on page p2 or edge on page p3
            for (int edgeIdx : edgeIndices) {
              model.addClause(MClause(MVar(allOn123Var, false), model.getPageVar(edgeIdx, p1, true), model.getPageVar(edgeIdx, p2, true), model.getPageVar(edgeIdx, p3, true)));
            }
            clause.addVar(MVar(allOn123Var, true));
          }
        }
      }
      model.addClause(clause);
    } else {
      ERROR("larger values of k are not implemented");
    }
  }


  encodeAdditionalCustomConstraints(model, inputGraph, params);
        }


using FuncPreTy = std::function<void(InputGraph&, Params&)>;
using FuncPostTy = std::function<void(SATModel&, InputGraph&, const Params&)>;

void prepareConstraints(
    std::unordered_map<std::string, FuncPreTy>& preConstraints,
    std::unordered_map<std::string, FuncPostTy>& postConstraints) {
  postConstraints["trees"]         = encodeTrees;
  postConstraints["directed"]      = encodeDirectedConstraints;
  postConstraints["dispersable"]   = encodeDispersable;
  postConstraints["local"]         = encodeLocal;
  postConstraints["star"]          = encodeStarConstraints;
}

template<class T>
void fillResult(SATModel& model, const InputGraph& inputGraph, const Params& params, T& solver, Result& result) {
  // LOG("var[%d] = %d", 7, model.value(solver, 7));
  // LOG("var[%d] = %d", 8, model.value(solver, 8));

  // Fill order
  if (params.fixedOrder) {
    result.order = inputGraph.vertexOrder;
  } else {
    result.order = std::vector<int>(inputGraph.nc, -1);

    for (int i = 0; i < inputGraph.nc; i++) {
      int countSmaller = 0;

      for (int j = 0; j < inputGraph.nc; j++) {
        if (i != j && model.value(solver, model.getRelVar(i, j, true))) {
          countSmaller++;
        }
      }

      CHECK(result.order[inputGraph.nc - countSmaller - 1] == -1);
      result.order[inputGraph.nc - countSmaller - 1] = i;
    }
  }

  // Fill edge pages
  if (!params.isTwist()) {
    for (size_t j = 0; j < inputGraph.edges.size(); j++) {
      vector<int> edgePages;
      for (int k = 0; k < params.page_var_num(); k++) {
        if (model.value(solver, model.getPageVar(j, k, true))) {
          edgePages.push_back(k);
        }
      }

      if (edgePages.size() > 1 && !inputGraph.isMultiPage(j)) {
        result.code = ResultCode::ERROR;
        std::cerr << "multiple pages for edge " << inputGraph.edge_to_string(j) << "\n";
        break;
      }

      if (edgePages.empty()) {
        result.code = ResultCode::ERROR;
        std::cerr << "page not found for edge " << inputGraph.edge_to_string(j) << "\n";
        break;
      }

      result.pages.push_back(edgePages);
    }
  }

  // Fill page types
  for (int i = 0; i < params.stacks + params.queues + params.mixedPages; i++) {
    if (params.isStack() || params.isTrack()) {
      result.pageTypes.push_back(true);
    } else if (params.isQueue()) {
      result.pageTypes.push_back(false);
    } else if (params.isMixed()) {      
      result.pageTypes.push_back(i < params.stacks);
    } else if (params.isMixedPages()) {
      result.pageTypes.push_back(model.value(solver, model.getPageTypeVar(i, true)));
    } else {
      ERROR("wrong type of layout");
    }
  }

  for (int page = 0; page < params.page_var_num(); page++) {
    if (params.isRique()) {
      result.pageNames.push_back("rique");
    } else {
      CHECK(page < (int) result.pageTypes.size());
      result.pageNames.push_back(result.pageTypes[page] ? "stack" : "queue");
    }
  }

  // verify same-page variables
  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    for (size_t j = i + 1; j < inputGraph.edges.size(); j++) {
      if (inputGraph.isMultiPage(i) || inputGraph.isMultiPage(j)) continue;
      if (!model.hasSamePageVar(i, j)) continue;

      int pageI = result.getPage(i);
      int pageJ = result.getPage(j);
      bool samePage = model.value(solver, model.getSamePageVar(i, j, true));

      if (pageI == pageJ) {
        if (!samePage) {
          result.code = ResultCode::ERROR;
          std::cerr << "same-page variable is not correct for edges " << inputGraph.edge_to_string(i) << " and " << inputGraph.edge_to_string(j) << "\n";
        }
      } else {
        // maybe not checking this, since we relax the constraint
        if (samePage) {
          result.code = ResultCode::ERROR;
          std::cerr << "distinct-page variable is not correct for edges " << inputGraph.edge_to_string(i) << " and " << inputGraph.edge_to_string(j) << "\n";
        }
      }
    }
  }

  // verify group-edges
  if (!inputGraph.isMultiPage()) {
    for (auto group : inputGraph.groupEdgePages) {
      set<int> groupPages;
      for (int edgeIdx : group.second) {
        groupPages.insert(result.getPage(edgeIdx));
      }
      if ((int)groupPages.size() > group.first) {
        result.code = ResultCode::ERROR;
        std::cerr << "group-edge-pages are not correct for edges (" << ::to_string(group.second) << "): groupPages.size() = " << groupPages.size() << "\n";
      }
    }
  }

  // fill vertex tracks
  if (params.isTrack()) {
    for (size_t i = 0; i < inputGraph.edges.size(); i++) {
      auto e = inputGraph.edges[i];
      CHECK(!model.value(solver, model.getSameTrackVar(e.first, e.second, true)));
    }

    for (int j = 0; j < inputGraph.nc; j++) {
      int track = -1;
      int cnt = 0;

      for (int k = 0; k < params.tracks; k++) {
        if (model.value(solver, model.getTrackVar(j, k, true))) {
          track = k;
          cnt++;
        }
      }

      if (cnt > 1) {
        result.code = ResultCode::ERROR;
        std::cerr << "multiple tracks for node " << j << "\n";
        break;
      }

      if (track == -1) {
        result.code = ResultCode::ERROR;
        std::cerr << "track not found for node " << j << "\n";
        break;
      }

      result.tracks.push_back(track);
    }
  }

  // Check constraints
  for (auto rel : inputGraph.nodeRel) {
    int l = rel.first;
    int r = rel.second;
    int pos1 = -1, pos2 = -1;

    for (size_t j = 0; j < result.order.size(); j++) {
      if (result.order[j] == l) {
        pos1 = j;
      }

      if (result.order[j] == r) {
        pos2 = j;
      }
    }

    if (!params.isTrack() || result.tracks[l] == result.tracks[r]) {
      CHECK(pos1 != -1 && pos2 != -1 && pos1 < pos2, "nodeRel is not satisfied");
    }
  }

  for (auto pr : inputGraph.edgePages) {
    int index = pr.first;
    auto& pages = pr.second;
    for (int page : result.pages[index]) {
      CHECK(find(pages.begin(), pages.end(), page) != pages.end(),
            "edgePages constraint is not satisfied");
    }
  }

  for (auto pr : inputGraph.samePage) {
    int e1 = pr.first;
    int e2 = pr.second;
    CHECK(result.pages[e1] == result.pages[e2], "samePage is not satisfied");
  }

  for (auto pr : inputGraph.distinctPage) {
    int e1 = pr.first;
    int e2 = pr.second;
    CHECK(result.pages[e1] != result.pages[e2], "distinctPage is not satisfied");
  }

  for (auto pr : inputGraph.nodeTracks) {
    int index = pr.first;
    auto& tracks = pr.second;
    int track = result.tracks[index];
    CHECK(find(tracks.begin(), tracks.end(), track) != tracks.end());
  }

  if (params.adjacent) {
    for (int j = 1; j < inputGraph.nc; j++) {
      int cnt = 0;

      for (int i = 0; i < inputGraph.nc; i++) {
        if (i == j) {
          continue;
        }

        if (model.value(solver, model.getAdjVar(i, j, true))) {
          cnt++;
        }
      }

      CHECK(cnt > 0);
    }

    for (int i = 0; i < inputGraph.nc; i++) {
      int countAdj = 0;

      for (int j = 0; j < inputGraph.nc; j++) {
        if (i == j) {
          continue;
        }

        if (model.value(solver, model.getAdjVar(i, j, true))) {
          countAdj++;
        }
      }

      bool satis = (i == result.order[inputGraph.nc - 1] ? countAdj == 0 : countAdj == 1);
      CHECK(satis, "wrong adjacent variable for vertex %d: %d", i, countAdj);
    }
  }
}

int dispersableLowerBound(InputGraph& inputGraph, const Params& params) {
  // max degree
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

int stackLowerBound(InputGraph& inputGraph, const Params& params) {
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size(); 
  int lb = (m - n + n - 4) / max(n - 3, 1);
  lb = max(lb, 1);

  if (contains(params.constraints, "dispersable")) {
    lb = max(lb, dispersableLowerBound(inputGraph, params));
  }

  return lb;
}

int queueLowerBound(InputGraph& inputGraph, const Params& params) {
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();
  int lb = params.queues + 1;

  for (int k = 0; k <= params.queues; k++) {
    if (n >= 2 * k) {
      int maxEdges = 2 * k * n - k * (2 * k + 1);

      if (maxEdges >= m) {
        lb = k;
        break;
      }
    }
  }

  if (contains(params.constraints, "dispersable")) {
    lb = max(lb, dispersableLowerBound(inputGraph, params));
  }

  return lb;
}

int riqueLowerBound(InputGraph& inputGraph, const Params& params) {
  const int n = inputGraph.nc;
  const int m = (int) inputGraph.edges.size();
  if (m == 0)
    return 0;

  int lowerBound = params.riques + 1;
  for (int k = 1; k <= params.riques; k++) {
    const long long planarPerPage =
        n >= 3 ? 3LL * n - 6 : 1LL * n * (n - 1) / 2;
    if (k * planarPerPage < m)
      continue;

    // The proof of the RIQUE density theorem gives
    //   m <= (2n - 4)k - k^2 + (n - 1).
    if (n >= 3) {
      const long long densityMax =
          (2LL * n - 4) * k - 1LL * k * k + (n - 1);
      if (densityMax < m)
        continue;
    }

    lowerBound = k;
    break;
  }

  return lowerBound;
}

int twistLowerBound(InputGraph& inputGraph, const Params& params) {
  CHECK(!contains(params.constraints, "dispersable"));

  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();
  int lb = params.twists + 1;

  // twist-number k => max_edges = 2kn - (2k+1)k when n >= 2k+1, and n*(n-1)/2 when n <= 2k+1
  //  k=1 => 2n-3
  //  k=2 => 4n-10

  for (int k = 0; k <= params.twists; k++) {
    if (n >= 2 * k + 1) {
      int maxEdges = 2 * k * n - (2 * k + 1) * k;
      if (maxEdges >= m) {
        lb = k;
        break;
      }
    }
  }

  return lb;
}

int trackLowerBound(InputGraph& inputGraph, const Params& params) {
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();

  for (int k = 1; k <= params.tracks; k++) {
    int maxEdges = (k - 1) * n - k * (k - 1) / 2;

    if (maxEdges >= m)
      return k;
  }

  return params.tracks + 1;
}

int mixedLowerBound(InputGraph& inputGraph, const Params& params) {
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();

  int kq = params.queues;
  int maxEdgesQ = 2 * kq * n - kq * (2 * kq + 1);

  int ks = params.stacks;
  int maxEdgesS = n * (ks + 1) - 3 * ks;

  if (maxEdgesS + maxEdgesQ < m)
    return params.stacks + params.queues + 1;

  return 2;
}

int mixedPagesLowerBound(InputGraph& inputGraph, const Params& params) {
  int n = inputGraph.nc;
  int m = (int)inputGraph.edges.size();
  int lb = params.queues + 1;

  for (int k = 0; k < params.mixedPages; k++) {
    if (n >= 2 * k) {
      int maxEdges = 2 * n * k + k - 2 * k * k - 2;
      if (maxEdges >= m) {
        lb = k;
        break;
      }
    }
  }
  return lb;
}

template<class T>
void applyAdditionalSymmetry(SATModel&, const Params&, T&) {
}

template<class T>
Result runInternal(SATModel& model, InputGraph& inputGraph, Params& params, T& solver) {
  solver.verbosity = params.verbose;
  model.initVars(solver);

  if (params.applySatsuma) {
    LOG_IF(params.verbose, "applying Satsuma for %'d variables and %'d constraints", model.varCount(), model.clauseCount());
    model.applySatsuma(params.verbose, solver);
  }

  model.initClauses(solver);

  applyAdditionalSymmetry(model, params, solver);

  if (params.modelFile != "") {
    LOG_IF(params.verbose, "encoded %'d variables and %'d constraints", model.varCount(), model.clauseCount());
    model.toDimacs(params.modelFile);
    LOG("SAT model in dimacs format saved to '%s'", params.modelFile.c_str());
    exit(0);
  }

  Simp21::lbool ret;

  if (params.resultFile != "") {
    LOG("parsing SAT model with %'d variables and %'d clauses from '%s'", model.varCount(), model.clauseCount(), params.resultFile.c_str());
    auto externalResult = model.fromDimacs(params.resultFile);

    if (externalResult == "SATISFIABLE") {
      ret = l_True;
    } else if (externalResult == "UNSATISFIABLE") {
      ret = l_False;
    } else {
      ret = l_Undef;
    }
  } else {
    LOG_IF(params.verbose, "solving SAT model with %'d variables and %'d clauses using Simp21...", solver.nVars(), solver.nClauses());

    if (!solver.okay()) {
      ret = l_False;
    } else {
      Simp21::vec<Simp21::Lit> dummy;
      ret = solver.solveLimited(dummy);
    }
  }

  // output
  Result result(ret == l_True ? ResultCode::SAT
                             : ret == l_False ? ResultCode::UNSAT
                                              : ResultCode::ERROR);
  LOG_IF(params.verbose, "SAT model solved with return code: %d (%s)",
         static_cast<int>(result.code), resultCodeName(result.code));

  if (result.isSat()) {
    fillResult(model, inputGraph, params, solver, result);
  }

  return result;
}

Result runInternal(InputGraph& inputGraph, Params& params) {
  CHECK(!params.skipSAT);
  CHECK(params.stacks >= 0 && params.queues >= 0 && params.twists >= 0 &&
        params.tracks >= 0 && params.mixedPages >= 0 && params.riques >= 0,
        "layout counts must be non-negative");
  if (params.isRique()) {
    CHECK(params.riques > 0 && params.stacks == 0 && params.queues == 0 &&
          params.twists == 0 && params.tracks == 0 && params.mixedPages == 0,
          "invalid RIQUE layout parameters");
  } else if (params.isTrack()) {
    CHECK(params.tracks > 0 && params.stacks == 1 && params.queues == 0 &&
          params.twists == 0 && params.mixedPages == 0 && params.riques == 0,
          "invalid track layout parameters");
  } else if (params.isTwist()) {
    CHECK(params.twists > 0 && params.stacks == 0 && params.queues == 0 &&
          params.tracks == 0 && params.mixedPages == 0 && params.riques == 0,
          "invalid twist layout parameters");
  } else if (params.isMixedPages()) {
    CHECK(params.mixedPages > 0 && params.stacks == 0 && params.queues == 0 &&
          params.twists == 0 && params.tracks == 0 && params.riques == 0,
          "invalid mixed-page layout parameters");
  } else if (params.isMixed()) {
    CHECK(params.stacks > 0 && params.queues > 0 && params.twists == 0 &&
          params.tracks == 0 && params.mixedPages == 0 && params.riques == 0,
          "invalid mixed layout parameters");
  } else if (params.isStack()) {
    CHECK(params.stacks > 0 && params.queues == 0 && params.twists == 0 &&
          params.tracks == 0 && params.mixedPages == 0 && params.riques == 0,
          "invalid stack layout parameters");
  } else if (params.isQueue()) {
    CHECK(params.queues > 0 && params.stacks == 0 && params.twists == 0 &&
          params.tracks == 0 && params.mixedPages == 0 && params.riques == 0,
          "invalid queue layout parameters");
  }
  CHECK(params.local >= 0, "local page bound must be non-negative");
  CHECK(params.span >= 0, "track span must be non-negative");
  CHECK(!params.strict || params.isQueue(), "strict layouts require queues");
  CHECK(params.span == 0 || params.isTrack(), "span is only valid for track layouts");
  CHECK(!params.fixedOrder || !params.isTrack(),
        "fixed-order track layouts are not implemented");
  CHECK(!contains(params.constraints, "trees") || params.stacks + params.queues > 0,
        "tree constraints require stack or queue pages");
  CHECK(!contains(params.constraints, "local") ||
        (params.local > 0 && params.stacks + params.queues > 0),
        "local constraint requires a positive bound and stack or queue pages");
  CHECK(params.local == 0 || contains(params.constraints, "local"),
        "a local page bound requires the local constraint");
  CHECK(!contains(params.constraints, "dispersable") || params.page_var_num() > 0,
        "dispersable constraint requires page variables");
  CHECK(!contains(params.constraints, "directed") ||
        inputGraph.direction.size() == inputGraph.edges.size(),
        "directed constraint requires one direction per edge");
  int lbPages = -1;
  int ubPages = params.isMixedPages() ? params.mixedPages
              : params.isRique() ? params.riques
              : params.stacks + params.queues + params.twists;

  if (params.isRique()) {
    lbPages = riqueLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for rique thickness: %d", lbPages);
  } else if (params.isStack()) {
    lbPages = stackLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for stack thickness: %d", lbPages);
  } else if (params.isQueue()) {
    lbPages = queueLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for queue thickness: %d", lbPages);
  } else if (params.isTwist()) {
    lbPages = twistLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for twist thickness: %d", lbPages);
  } else if (params.isTrack()) {
    lbPages = trackLowerBound(inputGraph, params);
    ubPages = params.tracks;
    LOG_IF(params.verbose, "lower bound for track thickness: %d", lbPages);
  } else if (params.isMixed()) {
    lbPages = mixedLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for mixed thickness: %d", lbPages);
  } else if (params.isMixedPages()) {
    lbPages = mixedPagesLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for mixed-pages thickness: %d", lbPages);
  } else {
    ERROR("wrong type of layout");
  }

  if (lbPages > ubPages && params.modelFile.empty()) {
    LOG_IF(params.verbose, "lower bound (%d) exceeds upper bound (%d)", lbPages, ubPages);
    return Result(ResultCode::UNSAT);
  }
  if (lbPages > ubPages) {
    LOG_IF(params.verbose,
           "lower bound (%d) exceeds upper bound (%d), but continuing to "
           "export the full SAT model",
           lbPages, ubPages);
  }

  std::unordered_map<std::string, FuncPreTy> preConstraints;
  std::unordered_map<std::string, FuncPostTy> postConstraints;
  std::vector<std::string> constraints;

  if (!params.constraints.empty()) {
    prepareConstraints(preConstraints, postConstraints);
    constraints = params.constraints;

    std::vector<std::string> remainingConstraints;
    for (std::string c : constraints) {
      CHECK(preConstraints.count(c) || postConstraints.count(c),  "constraint '%s' not implemented", c.c_str());

      if (preConstraints.count(c)) {
        LOG_IF(params.verbose, "encoding pre-constraints for '%s'...", c.c_str());
        auto func = preConstraints[c];
        func(inputGraph, params);
      } else {
        remainingConstraints.push_back(c);
      }
    }
    constraints = remainingConstraints;
  }

  if (params.fixedOrder) {
    CHECK(!inputGraph.vertexOrder.empty(), "vertex order is not initialized with fixedOrder");
  }

  if (!inputGraph.vertexOrder.empty() && !params.fixedOrder) {
    LOG_IF(params.verbose, "converting computed vertex order to constraints");
    for (int i = 0; i + 1 < inputGraph.nc; i++) {
      inputGraph.addNodeRel(inputGraph.vertexOrder[i], inputGraph.vertexOrder[i + 1]);
    }
  }

  SATModel model;

  LOG_IF(params.verbose && params.fixedOrder, "using fixed vertex order");

  // encoding
  if (!params.skipSolve) {
    if (params.isRique()) {
      LOG_IF(params.verbose, "encoding model for rique embedding...");
      encodeRiqueLayout(model, inputGraph, params);
    } else if (params.isStack()) {
      LOG_IF(params.verbose, "encoding model for stack embedding...");
      encodeStackLayout(model, inputGraph, params);
    } else if (params.isQueue()) {
      LOG_IF(params.verbose, "encoding model for queue embedding...");
      encodeQueueLayout(model, inputGraph, params);
    } else if (params.isTwist()) {
      LOG_IF(params.verbose, "encoding model for twist embedding...");
      encodeTwistLayout(model, inputGraph, params);
    } else if (params.isTrack()) {
      LOG_IF(params.verbose, "encoding model for track embedding...");
      encodeTrackLayout(model, inputGraph, params);
    } else if (params.isMixed()) {
      LOG_IF(params.verbose, "encoding model for mixed embedding...");
      encodeMixedLayout(model, inputGraph, params);
    } else if (params.isMixedPages()) {
      LOG_IF(params.verbose, "encoding model for mixed-page embedding...");
      encodeMixedPageLayout(model, inputGraph, params);
    } else {
      ERROR("wrong type of layout");
    }
  }

  if (params.adjacent) {
    LOG_IF(params.verbose, "encoding adjacent vertices...");
    encodeAdjacent(model, inputGraph, params.page_var_num());
  }


  if (!constraints.empty()) {
    for (std::string c : constraints) {
      CHECK(postConstraints.count(c));

      LOG_IF(params.verbose, "encoding post-constraints for '%s'...", c.c_str());
      auto func = postConstraints[c];
      func(model, inputGraph, params);
    }
  }

  if (params.skipSolve)
    return Result(ResultCode::SAT);

  // Symmetry-breaking and pre/post constraints
  encodeCustomConstraints(model, inputGraph, params);

  Simp21::Solver solver;
  return runInternal(model, inputGraph, params, solver);
}

Result run(InputGraph& inputGraph, Params& params) {
  try {
    return runInternal(inputGraph, params);
  } catch (...) {
    return Result(ResultCode::ERROR);
  }
}
