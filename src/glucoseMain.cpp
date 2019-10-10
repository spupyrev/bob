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
  CHECK(inputGraph.multiPage.size() == inputGraph.edges.size() || inputGraph.multiPage.empty());
  for (int i = 0; i < m; i++) {
    if (inputGraph.multiPage.size() == inputGraph.edges.size() && inputGraph.multiPage[i]) continue;
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
      bool multiI = inputGraph.multiPage.size() == inputGraph.edges.size() && inputGraph.multiPage[i];
      bool multiJ = inputGraph.multiPage.size() == inputGraph.edges.size() && inputGraph.multiPage[j];

      // set on same page var
      for (int p1 = 0; p1 < pageCount; p1++) {
        for (int p2 = 0; p2 < pageCount; p2++) {
          if (p1 != p2 && (multiI || multiJ)) continue;
          model.addClause( MClause(model.getPageVar(i, p1, false), model.getPageVar(j, p2, false), model.getSamePageVar(i, j, (p1 == p2))) );
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
      clause.addVar( model.getTrackVar(i, j, true) );
    }

    model.addClause( clause );
  }

  // at most one track per vertex
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

  // track i before track j for all i < j
  for (int i = 0; i < trackCount; i++) {
    for (int j = i + 1; j < trackCount; j++) {
      for (int v = 0; v < n; v++) {
        for (int u = 0; u < n; u++) {
          if (v == u) continue;
          // u on track_i && v on track_j => u < v
          model.addClause( MClause(model.getTrackVar(u, i, false), model.getTrackVar(v, j, false), model.getRelVar(u, v, true)) );
        }
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

  // one page => fix
  if (params.stacks + params.queues == 1) {
    model.addClause( MClause(model.getPageVar(index, 0, true)) );
  }

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
    if (e1n1 == e2n1 || e1n1 == e2n2 || e1n2 == e2n1 || e1n2 == e2n2) {
      continue;
    }

    // forbid crossings between i-th and index-th edges on pages [0, params.stacks)
    for (int page = 0; page < params.stacks; page++) {
      model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n1, e1n2, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n2, e1n2, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n1, e1n1, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n2, e1n1, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );

      model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n1, e2n2, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n2, e2n2, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n1, e2n1, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n2, e2n1, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
    }

    // forbid nestings between i-th and index-th edges on pages [params.stacks, params.stacks + params.queues)
    for (int page = params.stacks; page < params.stacks + params.queues; page++) {
      model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n1, e2n2, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e1n1, e2n2, e2n1, e1n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n1, e2n2, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e1n2, e2n2, e2n1, e1n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );

      model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n1, e1n2, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e2n1, e1n2, e1n1, e2n2), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n1, e1n2, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
      model.addClause( MClause(crossingClause(model, i, index, e2n2, e1n2, e1n1, e2n1), model.getPageVar(i, page, false), model.getPageVar(index, page, false)) );
    }
  }
}

void encodeStack(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isStack());
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.stacks);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeStackEdge(model, inputGraph, i, params);
  }
}

void encodeQueue(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isQueue());
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.queues);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeQueueEdge(model, inputGraph, i, params);
  }
}

void encodeTrack(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isTrack());
  encodeRelative(model, inputGraph);
  CHECK(params.stacks == 1);
  encodePageVariables(model, inputGraph, params.stacks);
  encodeTrackVariables(model, inputGraph, params.tracks);

  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeTrackEdge(model, inputGraph, i, params);
  }
}

void encodeMixed(SATModel& model, InputGraph& inputGraph, Params params) {
  CHECK(params.isMixed());
  CHECK(params.stacks >= 1 && params.queues >= 1, "incorrect page number for mixed layout");
  encodeRelative(model, inputGraph);
  encodePageVariables(model, inputGraph, params.stacks + params.queues);

  // page assignment:
  //   [0, params.stacks) are for stacks
  //   [params.stacks, params.stacks + params.queues) are for queues
  for (size_t i = 0; i < inputGraph.edges.size(); i++) {
    encodeMixedEdge(model, inputGraph, i, params);
  }
}

void encodeAutomorphismConstraints(SATModel& model, InputGraph& inputGraph, Params params) {
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
        model.addClause( MClause(model.getRelVar(group[i], group[j], true)) );
      }
    }
  }
  LOG_IF(params.verbose && cnt > 0, "identified %d similarity groups...", cnt);
}

void encodeStackSymmetry(SATModel& model, InputGraph& inputGraph, Params params) {
  int n = inputGraph.nc;

  // set node 1 as the first one on the spine
  for (int i = 0; i < n; i++) {
    if (i == inputGraph.firstNode) continue;
    inputGraph.addNodeRel(inputGraph.firstNode, i);
  }

  // set the direction of the spine: 1 < 2
  if (n >= 3) {
    inputGraph.addNodeRel(1, 2);
  }

  if (!params.dispersible) {
    // edge 0 on the first page
    inputGraph.edgePages[0] = {0};
    // edge 1 on the first page or second page
    if (params.stacks >= 2 && inputGraph.edges.size() >= 2) {
      inputGraph.edgePages[1] = {0, 1};
    }
  }
}

void encodeQueueSymmetry(SATModel& model, InputGraph& inputGraph, Params params) {
  int n = inputGraph.nc;

  // set the direction of the spine: 1 < 2
  if (n >= 3) {
    inputGraph.addNodeRel(1, 2);
  }

  if (!params.dispersible) {
    // edge 0 on the first page
    inputGraph.edgePages[0] = {0};
    // edge 1 on the first page or second page
    if (params.queues >= 2 && inputGraph.edges.size() >= 2) {
      inputGraph.edgePages[1] = {0, 1};
    }
  }

  // TODO: does this help?
  // edges incident to first node => same page
  // egdes incident to last node => same page
  /*vector<int> rightmostVar;
  vector<int> leftmostVar;
  MClause rightClause, leftClause;
  for (int i = 0; i < n; i++) {
    rightmostVar.push_back(model.addVar());
    leftmostVar.push_back(model.addVar());
    rightClause.addVar(MVar(rightmostVar[i], true));
    leftClause.addVar(MVar(leftmostVar[i], true));
  }
  model.addClause(rightClause);
  model.addClause(leftClause);

  for (int i = 0; i < n; i++) {
    MClause rightClause(MVar(rightmostVar[i], true));
    MClause leftClause(MVar(leftmostVar[i], true));
    for (int j = 0; j < n; j++) {
      if (i == j) continue;
      rightClause.addVar(model.getRelVar(i, j, true));
      leftClause.addVar(model.getRelVar(j, i, true));
    }
    model.addClause(rightClause);
    model.addClause(leftClause);
  }

  for (int i = 0; i < n; i++) {
    vector<int> adjEdges;
    for (size_t j = 0; j < inputGraph.edges.size(); j++) {
      auto& edge = inputGraph.edges[j];
      if (edge.first == i || edge.second == i) {
        adjEdges.push_back(j);
      }
    }

    CHECK(adjEdges.size() > 0, "isolated vertex " + to_string(i));

    for (size_t j1 = 0; j1 < adjEdges.size(); j1++) {
      for (size_t j2 = j1 + 1; j2 < adjEdges.size(); j2++) {
        model.addClause( MClause(MVar(rightmostVar[i], false), model.getSamePageVar(adjEdges[j1], adjEdges[j2], true)) );
        model.addClause( MClause(MVar(leftmostVar[i], false), model.getSamePageVar(adjEdges[j1], adjEdges[j2], true)) );
      }
    }
  }*/
}

void encodeTrackSymmetry(SATModel& model, InputGraph& inputGraph, Params params) {
  // set node 1 on the first track, adjacent node x on the second and assume 1 < x
  for (int i = 0; i < min(inputGraph.nc, params.tracks); i++) {
    for (int t = 0; t <= i; t++) {
      inputGraph.nodeTracks[i].push_back(t);
    }
  }
  // set the direction of the spine: 1 < 2
  inputGraph.addNodeRel(1, 2);
}

void encodeMixedSymmetry(SATModel& model, InputGraph& inputGraph, Params params) {
  // set the direction of the spine: 1 < 2
  if (inputGraph.nc >= 3) {
    auto rel = make_pair(1, 2);
    inputGraph.nodeRel.push_back(rel);
  }
}

void encodeCustomConstraints(SATModel& model, InputGraph& inputGraph, Params params) {
  // Basic symmetryc-breaking constraints
  if (inputGraph.nodeRel.empty() && inputGraph.edgePages.empty() && inputGraph.nodeTracks.empty() && inputGraph.samePage.empty()) {
    LOG_IF(params.verbose, "adding symmetry-breaking constraints");

    if (params.isStack()) {
      // STACK
      encodeStackSymmetry(model, inputGraph, params);
    } else if (params.isQueue()) {
      // QUEUE
      encodeQueueSymmetry(model, inputGraph, params);
    } else if (params.isTrack()) {
      // TRACK
      encodeTrackSymmetry(model, inputGraph, params);
    } else if (params.isMixed()) {
      // MIXED
      encodeMixedSymmetry(model, inputGraph, params);
    }

    // breaking symmetry: relative order for isomorphic vertices
    encodeAutomorphismConstraints(model, inputGraph, params);
  } else {
    size_t numCons = inputGraph.nodeRel.size() + inputGraph.edgePages.size() + inputGraph.nodeTracks.size() + inputGraph.samePage.size();
    LOG_IF(params.verbose, "encoding %zu custom constraints...", numCons);
  }

  // Custom Constraints
  for (size_t i = 0; i < inputGraph.nodeRel.size(); i++) {
    auto rel = inputGraph.nodeRel[i];
    int l = rel.first;
    int r = rel.second;
    CHECK(0 <= l && l < inputGraph.nc, "incorrect nodeRel (" + to_string(l) + ", " + to_string(r) + ")");
    CHECK(0 <= r && r < inputGraph.nc, "incorrect nodeRel (" + to_string(l) + ", " + to_string(r) + ")");
    CHECK(l != r, "incorrect nodeRel (" + to_string(l) + ", " + to_string(r) + ")");

    if (!params.isTrack()) {
      model.addClause( MClause(model.getRelVar(l, r, true)) );
    } else {
      model.addClause( MClause(model.getRelVar(l, r, true), model.getSameTrackVar(l, r, false)) );
    }
  }

  for (auto pr : inputGraph.edgePages) {
    int index = pr.first;
    auto& pages = pr.second;
    MClause clause;
    for (int page : pages) {
      CHECK(0 <= pr.first && pr.first < (int)inputGraph.edges.size(), "incorrect edgePages");
      CHECK(0 <= page && page < params.stacks + params.queues);

      clause.addVar( model.getPageVar(index, page, true));
    }
    model.addClause( clause );
  }

  for (auto pr : inputGraph.samePage) {
    int e1 = pr.first;
    int e2 = pr.second;

    model.addClause( MClause(model.getSamePageVar(e1, e2, true)) );
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

void encodeTrees(SATModel& model, InputGraph& inputGraph, Params& params);
void encodeDispersible(SATModel& model, InputGraph& inputGraph, Params& params);

int dispersibleLowerBound(InputGraph& inputGraph, Params& params) {
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
  int lb = (m - n + n - 4) / max(n - 3, 1);
  lb = max(lb, 1);

  if (params.dispersible) {
    lb = max(lb, dispersibleLowerBound(inputGraph, params));
  }

  return lb;
}

int queueLowerBound(InputGraph& inputGraph, Params& params) {
  int n = inputGraph.nc;
  int m = inputGraph.edges.size();
  int lb = params.queues + 1;
  for (int k = 0; k <= params.queues; k++) {
    int maxEdges = 2*k*n - k*(2*k+1);
    if (maxEdges >= m) {
      lb = k;
      break;
    }
  }

  if (params.dispersible) {
    lb = max(lb, dispersibleLowerBound(inputGraph, params));
  }

  return lb;
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
	return 2;
}

bool runInternal(InputGraph& inputGraph, Params params) {
  int lbPages = -1;
  int ubPages = params.stacks + params.queues;
  if (params.isStack()) {
  	lbPages = stackLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for stack thickness: %d", lbPages);
  } else if (params.isQueue()) {
    lbPages = queueLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for queue thickness: %d", lbPages);
  } else if (params.isTrack()) {
    lbPages = trackLowerBound(inputGraph, params);
    ubPages = params.tracks;
    LOG_IF(params.verbose, "lower bound for track thickness: %d", lbPages);
  } else if (params.isMixed()) {
    lbPages = mixedLowerBound(inputGraph, params);
    LOG_IF(params.verbose, "lower bound for mixed thickness: %d", lbPages);
  } else {
    ERROR("wrong type of layout");
  }

	if (lbPages > ubPages) {
      LOG_IF(params.verbose, "lower bound exceeds input parameter");
  	  return false;
	}

  SATModel model;

  // encoding
  if (params.isStack()) {
    LOG_IF(params.verbose, "encoding model for stack embedding...");
    encodeStack(model, inputGraph, params);
  } else if (params.isQueue()) {
    LOG_IF(params.verbose, "encoding model for queue embedding...");
    encodeQueue(model, inputGraph, params);
  } else if (params.isTrack()) {
    LOG_IF(params.verbose, "encoding model for track embedding...");
    encodeTrack(model, inputGraph, params);
  } else if (params.isMixed()) {
    LOG_IF(params.verbose, "encoding model for mixed embedding...");
    encodeMixed(model, inputGraph, params);
  }

  if (params.trees) {
    LOG_IF(params.verbose, "encoding trees...");
    encodeTrees(model, inputGraph, params);
  }

  if (params.dispersible) {
    LOG_IF(params.verbose, "encoding dispersible constraints...");
    encodeDispersible(model, inputGraph, params);
  }

  encodeCustomConstraints(model, inputGraph, params);
  
  LOG_IF(params.verbose, "encoded %d variables and %d constraints", model.varCount(), model.clauseCount());
  model.toDimacs(params.modelFile);
  LOG_IF(params.verbose, "SAT model in dimacs format saved to '%s'", params.modelFile.c_str());
  return true;
}

bool run(InputGraph& inputGraph, Params params) {
	bool res;
  try {
    res = runInternal(inputGraph, params);
  } catch (...) {
  	res = false;
  	ERROR("exception during SAT model construction");
  }
  return res;
}
