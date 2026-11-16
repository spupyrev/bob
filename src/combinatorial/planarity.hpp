#pragma once

// LR-planarity (de Fraysseix-Rosenstiehl).
// Edge keys are int64 packings of (u<<32|v) to avoid string overhead.

#include <cstdint>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

namespace planarvibe::planarity {

using EdgeKey = int64_t;
inline EdgeKey make_key(int u, int v) {
    return (int64_t(uint32_t(u)) << 32) | int64_t(uint32_t(v));
}

// Combinatorial embedding in terms of node indices. Caller is responsible for
// mapping back to string ids (compute_planar_embedding does it).
struct Embedding {
    bool ok = false;
    std::string reason;
    // 0..n-1 node indices. The string-id mapping is captured by caller.
    std::vector<std::vector<int>> rotation;    // rotation[v] = cyclic neighbor order
    std::vector<std::vector<int>> faces;       // faces traversed from rotation
    std::vector<int> outer_face;               // chosen outer face (may be empty)
};

// Run LR-planarity on int-indexed edges. `edges` should be unique and u<v.
Embedding lr_test(int n, const std::vector<std::pair<int,int>>& edges);

// Normalize a string-keyed graph into int-indexed edges; the id mapping is
// returned so the caller can map rotation/faces back to strings.
struct Normalized {
    std::vector<std::string> id_by_index;
    std::unordered_map<std::string, int> index_by_id;
    std::vector<std::pair<int,int>> edges;  // u < v, unique
};
Normalized normalize_edges(const std::vector<std::string>& node_ids,
                           const std::vector<std::pair<std::string,std::string>>& edge_pairs);

// High-level API: string-keyed combinatorial embedding including outer-face
// selection. Mirrors planarity.compute_planar_embedding in Python.
struct StringEmbedding {
    bool ok = false;
    std::string reason;
    std::vector<std::string> id_by_index;
    std::unordered_map<std::string, int> index_by_id;
    std::vector<std::pair<std::string,std::string>> edges;  // string form
    std::vector<std::vector<std::string>> rotation;
    std::vector<std::vector<std::string>> faces;
    std::vector<std::string> outer_face;   // empty if none chosen
};

StringEmbedding compute_planar_embedding(
    const std::vector<std::string>& node_ids,
    const std::vector<std::pair<std::string,std::string>>& edge_pairs);

// Planar 3-tree analysis. Returns ok=false if the graph is not a planar 3-tree.
// `elimination` gives the reverse-construction order: each record is (vertex, [p0,p1,p2])
// where `vertex` was added on top of triangle (p0,p1,p2). Matches Python analyze_planar_3_tree.
struct Planar3TreeRecord {
    std::string vertex;
    std::string parents[3];
};
struct Planar3TreeInfo {
    bool ok = false;
    std::string reason;
    StringEmbedding embedding;
    std::vector<std::string> outer_face;  // size 3
    std::vector<Planar3TreeRecord> elimination;
    std::vector<std::string> node_ids;
    std::vector<std::pair<std::string,std::string>> edges;
};
Planar3TreeInfo analyze_planar_3_tree(
    const std::vector<std::string>& node_ids,
    const std::vector<std::pair<std::string,std::string>>& edge_pairs);

} // namespace planarvibe::planarity
