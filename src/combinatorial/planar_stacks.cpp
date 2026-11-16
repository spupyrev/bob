#include "layout_cli.h"
#include "stack_orders.h"
#include "augmentation.h"

#include <algorithm>

// Triangulate each component and restrict the layout to original edges.
// Result::pages follows the input graph's extractEdgesId() order.
static Result buildFourPageLayout(const PlanarGraph& graph, int verbose) {
  CHECK(!graph.directed, "four-page layouts require an undirected simple plane graph");
  CHECK(graph.checkConsistency(false), "invalid input rotation system");
  const int n = graph.numberOfVertices();
  const auto edges = graph.extractEdgesId();
  std::map<std::pair<int, int>, size_t> original;
  for (size_t i = 0; i < edges.size(); ++i) {
    const auto [u, v] = edges[i];
    CHECK(u != v && original.emplace(std::make_pair(std::min(u, v), std::max(u, v)), i).second,
          "four-page layouts require a simple graph");
  }
  // Connected components in input-ID order; do not renumber a connected input.
  std::vector<int> component(n, -1);
  std::vector<std::vector<int>> parts;
  for (int start = 0; start < n; ++start) {
    if (component[start] >= 0) continue;
    const int id = parts.size();
    parts.push_back({start});
    component[start] = id;
    for (size_t i = 0; i < parts.back().size(); ++i) {
      for (Vertex* v : graph.vertices[parts.back()[i]]->neighbors()) {
        if (component[v->index] >= 0) continue;
        component[v->index] = id;
        parts.back().push_back(v->index);
      }
    }
    std::sort(parts.back().begin(), parts.back().end());
  }
  Result result(ResultCode::SAT);
  result.pages.resize(edges.size());
  result.pageTypes.assign(4, true);
  result.pageNames.assign(4, "stack");
  size_t assignedEdges = 0;
  std::vector<int> local(n, -1);
  for (const auto& vertices : parts) {
    for (int i = 0; i < (int)vertices.size(); ++i) local[vertices[i]] = i;
    std::vector<std::vector<int>> rotations(vertices.size());
    for (int i = 0; i < (int)vertices.size(); ++i)
      for (Vertex* v : graph.vertices[vertices[i]]->neighbors())
        rotations[i].push_back(local[v->index]);
    if (vertices.size() <= 2) {
      result.order.insert(result.order.end(), vertices.begin(), vertices.end());
      if (!rotations[0].empty()) {
        result.pages[original.at({vertices[0], vertices[1]})] = {0};
        ++assignedEdges;
      }
      continue;
    }
    {
      PlanarGraph part;
      part.readEdges(rotations);
      // Preserve the designated face where it belongs to this component.
      if (!graph.outerFace.empty() &&
          component[graph.outerFace.vertices[0]->index] == component[vertices[0]]) {
        Vertex* v = graph.outerFace.vertices[0];
        Vertex* w = graph.outerFace.edges[0]->other(v);
        Vertex* pv = part.vertices[local[v->index]];
        part.outerFace = part.extractRightFace(pv, pv->adjacentEdge(part.vertices[local[w->index]]));
      }
      triangulateInput(part);
      const Result emb = fourPageEmbedding(part, verbose);
      for (int v : emb.order) result.order.push_back(vertices.at(v));
      const auto partEdges = part.extractEdgesId();
      CHECK(emb.pages.size() == partEdges.size(), "component pages do not cover its edges");
      for (size_t i = 0; i < partEdges.size(); ++i) {
        const auto [u, v] = partEdges[i];
        const auto it = original.find({vertices.at(u), vertices.at(v)});
        if (it == original.end()) continue;  // Added by triangulation.
        CHECK(result.pages[it->second].empty(), "original edge assigned twice");
        result.pages[it->second] = {emb.getPage(i)};
        ++assignedEdges;
      }
    }
  }
  CHECK((int)result.order.size() == n && assignedEdges == original.size(),
        "four-page output does not cover the input");
  std::vector<int> position(n, -1);
  for (int i = 0; i < n; ++i) {
    const int v = result.order[i];
    CHECK(v >= 0 && v < n && position[v] == -1, "invalid output permutation");
    position[v] = i;
  }
  // Crossings were checked on each triangulation. Restriction preserves validity,
  // and concatenated components occupy disjoint intervals.
  return result;
}

int main(int argc, char* argv[]) {
  LayoutCLI cli;
  cli.name = "planar_stacks";
  cli.options = [](CMDOptions&) {};
  cli.pageBound = [](const CMDOptions&) { return 4; };
  cli.format = [](const CMDOptions&) { return std::string("yannakakis4"); };
  cli.build = [](PlanarGraph& g, CMDOptions& o, std::vector<int>& order, std::map<EdgeTy, int>& pages) {
    auto result = buildFourPageLayout(g, o.getInt("-verbose"));
    order = std::move(result.order);
    const auto edges = g.extractEdgesId();
    for (size_t i = 0; i < edges.size(); ++i)
      pages.emplace(edges[i], result.getPage(i));
  };
  cli.statistics = [](const std::vector<EdgeTy>&, const std::vector<int>&) {};
  return runLayoutCLI(argc, argv, cli);
}
