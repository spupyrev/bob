#include "sat_utils.h"

#include <chrono>
#include <future>
#include <thread>

#include "logging.h"
#include "queues.h"
#include "stacks.h"

#include <algorithm>
#include <iostream>
#include <fstream>
#include <vector>
#include <charconv>
#include <set>
#include <sstream>

using namespace std;

int parsePageNumber(const string& token, const string& entry) {
  int page = 0;
  const char* begin = token.data();
  const char* end = begin + token.size();
  const auto parsed = std::from_chars(begin, end, page);
  CHECK(parsed.ec == std::errc() && parsed.ptr == end,
        "invalid page '%s' in -edge-pages entry '%s'",
        token.c_str(), entry.c_str());
  return page;
}

void applyNodeRelOption(InputGraph& inputGraph, const string& specification) {
  for (const string& group : SplitNotNull(specification, ";"))
    createNodeRel(inputGraph, group);
}

void applyEdgePagesOption(InputGraph& inputGraph, const string& specification) {
  for (const string& entry : SplitNotNull(specification, ";")) {
    const auto tokens = SplitNotNull(entry, "(),: \t\r\n");
    CHECK(tokens.size() >= 3,
          "expected '(u,v):pages' in -edge-pages entry '%s'", entry.c_str());
    CHECK(inputGraph.label2id.count(tokens[0]), "vertex '%s' not found", tokens[0].c_str());
    CHECK(inputGraph.label2id.count(tokens[1]), "vertex '%s' not found", tokens[1].c_str());

    vector<int> pages;
    for (size_t i = 2; i < tokens.size(); i++)
      pages.push_back(parsePageNumber(tokens[i], entry));
    sort_unique(pages);
    inputGraph.setEdgePages(inputGraph.label2id.at(tokens[0]),
                            inputGraph.label2id.at(tokens[1]), pages);
  }
}

void createNodeRel(InputGraph& inputGraph, const string& order) {
  auto& label2id = inputGraph.label2id;
  auto ord = SplitNotNull(order, " \t\r\n");

  for (size_t i = 0; i < ord.size(); i++) {
    for (size_t j = i + 1; j < ord.size(); j++) {
      string a = ord[i];
      string b = ord[j];
      CHECK(label2id.count(a), "createNodeRel failed: vertex %s not found", a.c_str());
      CHECK(label2id.count(b), "createNodeRel failed: vertex %s not found", b.c_str());
      inputGraph.addNodeRel(label2id[a], label2id[b]);
    }
  }
}

void createNodeRel(InputGraph& inputGraph, const string& pred, const string& succ) {
  auto& label2id = inputGraph.label2id;
  auto p = SplitNotNull(pred, " ");
  auto s = SplitNotNull(succ, " ");

  for (size_t i = 0; i < p.size(); i++) {
    for (size_t j = 0; j < s.size(); j++) {
      string a = p[i];
      string b = s[j];
      CHECK(label2id.count(a), "createNodeRel failed: vertex %s not found", a.c_str());
      CHECK(label2id.count(b), "createNodeRel failed: vertex %s not found", b.c_str());
      inputGraph.addNodeRel(label2id[a], label2id[b]);
    }
  }
}

void createEdgePages(InputGraph& inputGraph, const string& edges, int page) {
  auto& label2id = inputGraph.label2id;
  auto ed = SplitNotNull(edges, " ");

  for (size_t i = 1; i < ed.size(); i++) {
    string a = ed[i - 1];
    string b = ed[i];
    CHECK(label2id.count(a));
    CHECK(label2id.count(b));
    int idx = -1;

    for (int i = 0; i < (int)inputGraph.edges.size(); i++) {
      auto& e = inputGraph.edges[i];

      if ((e.first == label2id[a] && e.second == label2id[b]) || (e.first == label2id[b] && e.second == label2id[a])) {
        idx = i;
        break;
      }
    }

    CHECK(idx != -1, "edge (%s, %s) not found", a.c_str(), b.c_str());
    inputGraph.edgePages[idx].push_back(page);
  }
}

void createSamePages(InputGraph& inputGraph, const string& edges) {
  auto& label2id = inputGraph.label2id;
  auto ed = SplitNotNull(edges, "(), ");
  CHECK(ed.size() > 1);
  CHECK(ed.size() % 2 == 0);

  for (auto v : ed) {
    CHECK(label2id.count(v), "vertex %s not found in the graph", v.c_str());
  }

  for (size_t i = 0; i + 3 < ed.size(); i += 2) {
    string u1 = ed[i];
    string v1 = ed[i + 1];
    CHECK(label2id.count(u1));
    CHECK(label2id.count(v1));
    string u2 = ed[i + 2];
    string v2 = ed[i + 3];
    CHECK(label2id.count(u2));
    CHECK(label2id.count(v2));
    int idxU1 = label2id[u1];
    int idxV1 = label2id[v1];
    int idxU2 = label2id[u2];
    int idxV2 = label2id[v2];
    int e1 = inputGraph.findEdgeIndex(idxU1, idxV1);
    int e2 = inputGraph.findEdgeIndex(idxU2, idxV2);
    inputGraph.samePage.push_back(make_pair(e1, e2));
  }
}

void createNodeTracks(InputGraph& inputGraph, const string& nodes, int track) {
  auto& label2id = inputGraph.label2id;
  auto nd = SplitNotNull(nodes, " ");

  for (size_t i = 0; i < nd.size(); i++) {
    CHECK(label2id.count(nd[i]));
    int id = label2id[nd[i]];
    CHECK(0 <= id && id < inputGraph.nc);
    inputGraph.nodeTracks[id].push_back(track);
  }
}

bool dfs(const vector<vector<int>>& adj, vector<bool>& used, int now, int parent) {
  used[now] = true;
  bool res = true;

  for (int i = 0; i < (int) adj[now].size(); i++) {
    int next = adj[now][i];

    if (next == parent) {
      continue;
    }

    if (used[next]) {
      return false;
    }

    res = res && dfs(adj, used, next, now);
  }

  return res;
}

bool isOnSamePage(const vector<int>& pages1, const vector<int>& pages2) {
  for (int p1 : pages1) {
    for (int p2 : pages2) {
      if (p1 == p2) return true;
    }
  }
  return false;
}

bool checkTrees(const vector<pair<int, int>>& edges, const vector<vector<int>>& pages) {
  int n = 0;

  for (size_t i = 0; i < edges.size(); i++) {
    pair<int, int> e = edges[i];
    n = max(n, e.first + 1);
    n = max(n, e.second + 1);
  }

  CHECK(n > 0);
  int numPages = 0;
  for (auto pv : pages) {
    for (int page : pv) {
      numPages = max(numPages, page + 1);
    }
  }

  for (int page = 0; page < numPages; page++) {
    vector<vector<int>> adj = vector<vector<int>>(n);

    for (int i = 0; i < (int) edges.size(); i++) {
      pair<int, int> e = edges[i];
      CHECK(0 <= e.first && e.first < n, "incorrect edge");

      if (!isOnSamePage(pages[i], {page}))
        continue;

      adj[e.first].push_back(e.second);
      adj[e.second].push_back(e.first);
    }

    vector<bool> used = vector<bool>(n, false);

    for (int i = 0; i < n; i++)
      if (!used[i]) {
        if (!dfs(adj, used, i, -1)) {
          cerr << "page " << page << " is not a tree" << endl;
          return false;
        }
      }
  }

  return true;
}

bool checkCrossings(int n, const vector<pair<int, int>>& edges, const vector<int>& order, const vector<vector<int>>& pages, int k) {
  CHECK(n > 0);
  CHECK((int) order.size() == n, 10);
  CHECK(pages.size() == edges.size(), "incorrect number of pages", 10);
  vector<int> index(n, -1);

  for (size_t i = 0; i < order.size(); i++) {
    CHECK(0 <= order[i] && order[i] < n, 10);
    index[order[i]] = i;
  }

  for (size_t i = 0; i < pages.size(); i++) {
    CHECK(!pages[i].empty(), 10);
    for (int page : pages[i])
      CHECK(0 <= page && page < k, 10);
  }

  for (size_t i = 0; i < edges.size(); i++) {
    for (size_t j = i + 1; j < edges.size(); j++) {
      if (!isOnSamePage(pages[i], pages[j]))
        continue;

      int l1 = min(index[edges[i].first], index[edges[i].second]);
      int r1 = max(index[edges[i].first], index[edges[i].second]);
      int l2 = min(index[edges[j].first], index[edges[j].second]);
      int r2 = max(index[edges[j].first], index[edges[j].second]);

      if (l1 < l2 && l2 < r1 && r1 < r2)
        return false;

      if (l2 < l1 && l1 < r2 && r2 < r1) {
        return false;
      }
    }
  }

  return true;
}

bool checkNestings(int n, const vector<EdgeTy>& edges, const vector<int>& order, const vector<vector<int>>& pages, int k) {
  CHECK(n > 0, 10);
  CHECK((int) order.size() == n, 10);
  vector<int> index(n, -1);

  for (size_t i = 0; i < order.size(); i++) {
    CHECK(0 <= order[i] && order[i] < n, 10);
    index[order[i]] = i;
  }

  for (size_t i = 0; i < pages.size(); i++) {
    CHECK(!pages[i].empty(), 10);
    for (int page : pages[i]) {
      CHECK(0 <= page && page < k, 10);
    }
  }

  for (size_t i = 0; i < edges.size(); i++)
    for (size_t j = i + 1; j < edges.size(); j++) {
      if (!isOnSamePage(pages[i], pages[j]))
        continue;

      int l1 = min(index[edges[i].first], index[edges[i].second]);
      int r1 = max(index[edges[i].first], index[edges[i].second]);
      int l2 = min(index[edges[j].first], index[edges[j].second]);
      int r2 = max(index[edges[j].first], index[edges[j].second]);

      if (l1 < l2 && l2 < r2 && r2 < r1) {
        LOG("  checkNestings failed for edges (%d, %d) and (%d, %d) on page %d",
            edges[i].first, edges[i].second, edges[j].first, edges[j].second, pages[i][0]);
        return false;
      }

      if (l2 < l1 && l1 < r1 && r1 < r2) {
        LOG("  checkNestings failed for edges (%d, %d) and (%d, %d) on page %d",
            edges[i].first, edges[i].second, edges[j].first, edges[j].second, pages[i][0]);
        return false;
      }
    }

  return true;
}

bool checkRique(int n, const vector<EdgeTy>& edges, const vector<int>& order,
                const vector<vector<int>>& pages, int k) {
  CHECK(n > 0, 10);
  CHECK((int) order.size() == n, 10);
  CHECK(pages.size() == edges.size(), "incorrect number of pages", 10);
  vector<int> index(n, -1);

  for (size_t i = 0; i < order.size(); i++) {
    CHECK(0 <= order[i] && order[i] < n, 10);
    index[order[i]] = i;
  }

  vector<vector<pair<int, int>>> pageEdges(k);
  for (size_t i = 0; i < edges.size(); i++) {
    CHECK(!pages[i].empty(), 10);
    const int left = min(index[edges[i].first], index[edges[i].second]);
    const int right = max(index[edges[i].first], index[edges[i].second]);
    for (int page : pages[i]) {
      CHECK(0 <= page && page < k, 10);
      pageEdges[page].push_back({left, right});
    }
  }

  for (int page = 0; page < k; page++) {
    const auto& pageIntervals = pageEdges[page];
    for (size_t middle = 0; middle < pageIntervals.size(); middle++) {
      const int b = pageIntervals[middle].first;
      const int bp = pageIntervals[middle].second;
      bool hasNester = false;
      bool hasRightCrosser = false;

      for (size_t other = 0; other < pageIntervals.size(); other++) {
        if (other == middle)
          continue;
        const int left = pageIntervals[other].first;
        const int right = pageIntervals[other].second;
        if (left < b && bp < right)
          hasNester = true;
        if (b < left && left < bp && bp < right)
          hasRightCrosser = true;
      }

      if (hasNester && hasRightCrosser) {
        LOG("  checkRique failed for middle interval (%d, %d) on page %d",
            b, bp, page);
        return false;
      }
    }
  }

  return true;
}

bool checkTwist(int n, const vector<EdgeTy>& edges, const vector<int>& order, int k, int verbose) {
  CHECK((int) order.size() == n, 10);

  return checkTwist(edges, order, "the order", k, verbose) <= k;
}

bool checkMixed(int n, const vector<EdgeTy>& edges, const vector<int>& order, const vector<vector<int>>& pages, int stacks, int queues) {
  CHECK(n > 0, 10);
  CHECK((int) order.size() == n, 10);
  CHECK(pages.size() == edges.size(), "incorrect number of pages", 10);
  vector<int> index(n, -1);

  for (size_t i = 0; i < order.size(); i++) {
    CHECK(0 <= order[i] && order[i] < n, 10);
    index[order[i]] = i;
  }

  for (size_t i = 0; i < pages.size(); i++) {
    for (int page : pages[i]) {
      CHECK(0 <= page && page < stacks + queues, 10);
    }
  }

  for (size_t i = 0; i < edges.size(); i++) {
    for (size_t j = i + 1; j < edges.size(); j++) {
      int l1 = min(index[edges[i].first], index[edges[i].second]);
      int r1 = max(index[edges[i].first], index[edges[i].second]);
      int l2 = min(index[edges[j].first], index[edges[j].second]);
      int r2 = max(index[edges[j].first], index[edges[j].second]);

      for (int page : pages[i]) {
        if (find(pages[j].begin(), pages[j].end(), page) == pages[j].end())
          continue;

      if (page < stacks) {
          if ((l1 < l2 && l2 < r1 && r1 < r2) ||
              (l2 < l1 && l1 < r2 && r2 < r1))
            return false;
        } else {
          CHECK(page < stacks + queues, "unknown page");
          if ((l1 < l2 && l2 < r2 && r2 < r1) ||
              (l2 < l1 && l1 < r1 && r1 < r2))
          return false;
        }
      }
    }
  }

  return true;
}

bool checkMixedPages(int n, const vector<EdgeTy>& edges, const vector<int>& order, const vector<vector<int>>& pages, const vector<bool>& pageTypes, int numPages) {
  CHECK(n > 0, 10);
  CHECK((int) order.size() == n, 10);
  CHECK(pages.size() == edges.size(), "incorrect number of pages", 10);
  CHECK((int)pageTypes.size() == numPages, "incorrect number of page types", 10);
  vector<int> index(n, -1);

  for (size_t i = 0; i < order.size(); i++) {
    CHECK(0 <= order[i] && order[i] < n, 10);
    index[order[i]] = i;
  }

  for (size_t i = 0; i < pages.size(); i++) {
    for (int page : pages[i]) {
      CHECK(0 <= page && page < numPages, 10);
    }
  }

  for (size_t i = 0; i < edges.size(); i++) {
    for (size_t j = i + 1; j < edges.size(); j++) {
      int l1 = min(index[edges[i].first], index[edges[i].second]);
      int r1 = max(index[edges[i].first], index[edges[i].second]);
      int l2 = min(index[edges[j].first], index[edges[j].second]);
      int r2 = max(index[edges[j].first], index[edges[j].second]);

      for (int page : pages[i]) {
        if (find(pages[j].begin(), pages[j].end(), page) == pages[j].end())
          continue;

      if (pageTypes[page]) {
          if ((l1 < l2 && l2 < r1 && r1 < r2) ||
              (l2 < l1 && l1 < r2 && r2 < r1))
          return false;
      } else {
          if ((l1 < l2 && l2 < r2 && r2 < r1) ||
              (l2 < l1 && l1 < r1 && r1 < r2))
          return false;
        }
      }
    }
  }

  return true;
}

bool checkTracks(int n, const vector<EdgeTy>& edges, const vector<int>& order, const vector<vector<int>>& pages, const vector<int>& tracks, int kPages, int kTracks) {
  CHECK(n > 0);
  CHECK((int) order.size() == n);
  CHECK((int) tracks.size() == n);
  vector<int> index(n, -1);

  for (int i = 0; i < (int) order.size(); i++) {
    CHECK(0 <= order[i] && order[i] < n);
    index[order[i]] = i;
  }

  for (size_t i = 0; i < pages.size(); i++) {
    for (int page : pages[i]) {
      CHECK(0 <= page && page < kPages, 10);
    }
  }

  for (size_t i = 0; i < tracks.size(); i++) {
    int track = tracks[i];
    CHECK(0 <= track && track < kTracks, 10);
  }

  for (int i = 0; i < (int) edges.size(); i++) {
    for (int j = i + 1; j < (int) edges.size(); j++) {
      if (!isOnSamePage(pages[i], pages[j])) {
        continue;
      }

      int x = edges[i].first;
      int y = edges[i].second;
      int u = edges[j].first;
      int v = edges[j].second;

      if (tracks[x] == tracks[y]) {
        return false;
      }

      if (tracks[u] == tracks[v]) {
        return false;
      }

      if (tracks[x] == tracks[v] && tracks[y] == tracks[u] && index[x] < index[v] && index[u] < index[y]) {
        return false;
      }

      if (tracks[x] == tracks[v] && tracks[y] == tracks[u] && index[x] > index[v] && index[u] > index[y]) {
        return false;
      }

      if (tracks[x] == tracks[u] && tracks[y] == tracks[v] && index[x] < index[u] && index[v] < index[y]) {
        return false;
      }

      if (tracks[x] == tracks[u] && tracks[y] == tracks[v] && index[x] > index[u] && index[v] > index[y]) {
        return false;
      }
    }
  }

  return true;
}

bool checkDispersable(const vector<EdgeTy>& edges, const vector<vector<int>>& pages) {
  for (size_t i = 0; i < edges.size(); i++) {
    for (size_t j = i + 1; j < edges.size(); j++) {
      pair<int, int> ei = edges[i];
      pair<int, int> ej = edges[j];

      if (ei.first == ej.first || ei.first == ej.second || ei.second == ej.first || ei.second == ej.second) {
        if (isOnSamePage(pages[i], pages[j])) {
          return false;
        }
      }
    }
  }

  return true;
}

bool checkLocal(int n, const vector<EdgeTy>& edges, const vector<vector<int>>& pages, int local) {
  auto v2pages = vector<set<int>>(n);

  for (size_t i = 0; i < edges.size(); i++) {
    for (int page : pages[i]) {
      v2pages[edges[i].first].insert(page);
      v2pages[edges[i].second].insert(page);
    }
  }

  for (int i = 0; i < n; i++) {
    if ((int)v2pages[i].size() > local) {
      return false;
    }
  }

  return true;
}

bool checkSAT(const InputGraph& inputGraph, const Params& params, const Result& result) {
  LOG_IF(params.verbose, "verifying SAT solution...");

  // check general
  CHECK(inputGraph.nc > 0);
  CHECK((int) result.order.size() == inputGraph.nc, "incorrect vertex order", 10);
  CHECK(params.isTwist() || result.pages.size() == inputGraph.edges.size(), "incorrect number of pages", 10);
  for (size_t i = 0; i < result.order.size(); i++) {
    CHECK(0 <= result.order[i] && result.order[i] < inputGraph.nc, 10);
  }
  for (size_t i = 0; i < result.pages.size(); i++) {
    CHECK(!result.pages[i].empty(), 10);
  }

  if (params.isStack()) {
    if (!checkCrossings(inputGraph.nc, inputGraph.edges, result.order, result.pages, params.stacks)) {
      LOG("checkCrossings failed");
      return false;
    }
  } else if (params.isQueue()) {
    if (!checkNestings(inputGraph.nc, inputGraph.edges, result.order, result.pages, params.queues)) {
      LOG("checkNestings failed");
      return false;
    }
  } else if (params.isRique()) {
    if (!checkRique(inputGraph.nc, inputGraph.edges, result.order, result.pages,
                    params.riques)) {
      LOG("checkRique failed");
      return false;
    }
  } else if (params.isTwist()) {
    if (!checkTwist(inputGraph.nc, inputGraph.edges, result.order, params.twists, params.verbose)) {
      LOG("checkTwist failed");
      return false;
    }
  } else if (params.isTrack()) {
    if (!checkTracks(inputGraph.nc, inputGraph.edges, result.order, result.pages, result.tracks, params.stacks, params.tracks)) {
      LOG("checkTracks failed");
      return false;
    }
  } else if (params.isMixed()) {
    if (!checkMixed(inputGraph.nc, inputGraph.edges, result.order, result.pages, params.stacks, params.queues)) {
      LOG("checkMixed failed");
      return false;
    }
  } else if (params.isMixedPages()) {
    if (!checkMixedPages(inputGraph.nc, inputGraph.edges, result.order, result.pages, result.pageTypes, params.mixedPages)) {
      LOG("checkMixedPages failed");
      return false;
    }
  } else {
    ERROR("unknown embedding type");
  }

  if (contains(params.constraints, "trees") && !checkTrees(inputGraph.edges, result.pages))
    return false;

  if (contains(params.constraints, "dispersable") && !checkDispersable(inputGraph.edges, result.pages))
    return false;

  if (params.local > 0 && !checkLocal(inputGraph.nc, inputGraph.edges, result.pages, params.local))
    return false;

  return true;
}

void printLayoutStatistics(ostream& out, const InputGraph& inputGraph,
                           const Params& params, const Result& result) {
  bool hasStack = params.isStack() || params.isTwist() || params.isMixed();
  bool hasQueue = params.isQueue() || params.isMixed();

  if (params.isMixedPages()) {
    hasStack = find(result.pageTypes.begin(), result.pageTypes.end(), true) !=
               result.pageTypes.end();
    hasQueue = find(result.pageTypes.begin(), result.pageTypes.end(), false) !=
               result.pageTypes.end();
  }

  if (hasStack)
    out << "max-twist: " << countTwist(inputGraph.edges, result.order) << "\n";
  if (hasQueue)
    out << "max-rainbow: " << countRainbow(inputGraph.edges, result.order) << "\n";
}

Result runWithTimeout(const InputGraph& inputGraph, const Params& params,
                      int timeoutSeconds) {
  CHECK(timeoutSeconds >= 0, "timeout must be non-negative");
  if (timeoutSeconds == 0) {
    InputGraph graph = inputGraph;
    Params runParams = params;
    return run(graph, runParams);
  }

  std::promise<Result> completion;
  std::future<Result> result = completion.get_future();
  std::thread worker(
      [graph = InputGraph(inputGraph), runParams = Params(params),
       completion = std::move(completion)]() mutable {
        completion.set_value_at_thread_exit(run(graph, runParams));
      });
  worker.detach();

  if (result.wait_for(std::chrono::seconds(timeoutSeconds)) ==
      std::future_status::ready) {
    return result.get();
  }

  return Result(ResultCode::TIMEOUT);
}
