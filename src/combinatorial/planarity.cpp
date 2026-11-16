#include "planarity.hpp"

#include <algorithm>
#include <array>
#include <optional>
#include <stdexcept>

namespace planarvibe::planarity {

namespace {

// Interval and conflict-pair state, keyed by EdgeKey.
struct Interval {
    // EdgeKey or kNoKey if "empty".
    static constexpr EdgeKey kNoKey = INT64_MIN;
    EdgeKey low = kNoKey;
    EdgeKey high = kNoKey;
    bool empty() const { return low == kNoKey && high == kNoKey; }
};
struct ConflictPair { Interval left, right; };

constexpr EdgeKey kNoKey = Interval::kNoKey;

std::pair<int,int> parse_key(EdgeKey k) {
    return { int(uint32_t(k >> 32)), int(uint32_t(k & 0xFFFFFFFFLL)) };
}

// Main LR state.
struct LRState {
    int n = 0;
    std::vector<std::pair<int,int>> edges;

    std::vector<std::vector<int>> adjs;
    std::vector<std::vector<int>> directed_adjs;
    std::unordered_set<EdgeKey> directed_edge_set;
    std::vector<std::vector<int>> ordered_adjs;

    std::vector<int> roots;
    std::vector<int> height;
    // parent_edge[v] = EdgeKey or kNoKey
    std::vector<EdgeKey> parent_edge;
    std::vector<int> next_index;

    std::unordered_map<EdgeKey, int> lowpt;
    std::unordered_map<EdgeKey, int> lowpt2;
    std::unordered_map<EdgeKey, int> nesting_depth;
    std::unordered_map<EdgeKey, EdgeKey> ref;  // maps EdgeKey -> EdgeKey or kNoKey
    std::unordered_map<EdgeKey, int> side;
    // stack_bottom[ei] = optional index into S (-1 for null). We store the
    // S-element "identity" by index; if stack is modified the invariants are
    // maintained by the algorithm's semantics.
    // Because the algorithm only ever pops until we see the same stack-bottom,
    // storing a pointer to the element value works if we snapshot it. We store
    // an int id: the value is an index assigned at push time.
    std::unordered_map<EdgeKey, int> stack_bottom;  // int id or -1
    std::unordered_map<EdgeKey, EdgeKey> lowpt_edge;
    std::unordered_map<EdgeKey, bool> skip_init;

    // S is a stack of conflict pairs with identity ids.
    struct StackEntry { int id; ConflictPair p; };
    std::vector<StackEntry> S;
    int next_id = 0;

    std::vector<std::vector<int>> rotation;
    std::vector<std::vector<int>> faces;

    bool has_directed_edge(int u, int v) const {
        return directed_edge_set.count(make_key(u, v)) != 0;
    }

    int get_side(EdgeKey e) {
        if (e == kNoKey) return 1;
        auto it = side.find(e);
        if (it == side.end()) { side[e] = 1; return 1; }
        return it->second;
    }

    void sort_by_signed_nesting(int v) {
        auto& adj = ordered_adjs[v];
        // Stable ordering ensures deterministic face traversal when
        // nesting_depth values tie.
        std::stable_sort(adj.begin(), adj.end(), [&](int a, int b){
            return nesting_depth[make_key(v, a)] < nesting_depth[make_key(v, b)];
        });
    }

    void orient_edge(int u, int v) {
        directed_adjs[u].push_back(v);
        directed_edge_set.insert(make_key(u, v));
    }

    void init_adjacency() {
        adjs.assign(n, {});
        directed_adjs.assign(n, {});
        ordered_adjs.assign(n, {});
        for (auto [u, v] : edges) {
            adjs[u].push_back(v);
            adjs[v].push_back(u);
        }
    }

    void dfs_orientation(int root) {
        std::vector<int> dfs_stack{root};
        next_index.assign(n, 0);
        skip_init.clear();

        while (!dfs_stack.empty()) {
            int v = dfs_stack.back(); dfs_stack.pop_back();
            EdgeKey parent = parent_edge[v];
            int i = next_index[v];
            while (i < (int)adjs[v].size()) {
                int w = adjs[v][i];
                EdgeKey vw = make_key(v, w);

                if (!skip_init[vw]) {
                    if (has_directed_edge(v, w) || has_directed_edge(w, v)) {
                        next_index[v]++;
                        i = next_index[v];
                        continue;
                    }
                    orient_edge(v, w);
                    lowpt[vw] = height[v];
                    lowpt2[vw] = height[v];

                    if (height[w] == -1) {
                        parent_edge[w] = vw;
                        height[w] = height[v] + 1;
                        dfs_stack.push_back(v);
                        dfs_stack.push_back(w);
                        skip_init[vw] = true;
                        break;
                    } else {
                        lowpt[vw] = height[w];
                    }
                }

                nesting_depth[vw] = 2 * lowpt[vw];
                if (lowpt2[vw] < height[v]) nesting_depth[vw] += 1;

                if (parent != kNoKey) {
                    if (lowpt[vw] < lowpt[parent]) {
                        lowpt2[parent] = std::min(lowpt[parent], lowpt2[vw]);
                        lowpt[parent] = lowpt[vw];
                    } else if (lowpt[vw] > lowpt[parent]) {
                        lowpt2[parent] = std::min(lowpt2[parent], lowpt[vw]);
                    } else {
                        lowpt2[parent] = std::min(lowpt2[parent], lowpt2[vw]);
                    }
                }
                next_index[v]++;
                i = next_index[v];
            }
        }
    }

    bool interval_conflicting(const Interval& iv, EdgeKey edge) {
        return !iv.empty() && lowpt[iv.high] > lowpt[edge];
    }

    int conflict_pair_lowest(const ConflictPair& pair) {
        if (pair.left.empty()) return lowpt[pair.right.low];
        if (pair.right.empty()) return lowpt[pair.left.low];
        return std::min(lowpt[pair.left.low], lowpt[pair.right.low]);
    }

    int top_id() const { return S.empty() ? -1 : S.back().id; }

    bool add_constraints(EdgeKey ei, EdgeKey e) {
        ConflictPair P;

        // first while-loop
        while (true) {
            StackEntry Q = S.back(); S.pop_back();
            if (!Q.p.left.empty()) std::swap(Q.p.left, Q.p.right);
            if (!Q.p.left.empty()) return false;
            if (lowpt[Q.p.right.low] > lowpt[e]) {
                if (P.right.empty()) P.right = Q.p.right;
                else ref[P.right.low] = Q.p.right.high;
                P.right.low = Q.p.right.low;
            } else {
                ref[Q.p.right.low] = lowpt_edge[e];
            }
            if (top_id() == stack_bottom[ei]) break;
        }

        // second while-loop: merge conflicting stack entries
        while (!S.empty()) {
            auto& top = S.back().p;
            if (!interval_conflicting(top.left, ei) && !interval_conflicting(top.right, ei)) break;
            StackEntry Q = S.back(); S.pop_back();
            if (interval_conflicting(Q.p.right, ei)) std::swap(Q.p.left, Q.p.right);
            if (interval_conflicting(Q.p.right, ei)) return false;
            ref[P.right.low] = Q.p.right.high;
            if (Q.p.right.low != kNoKey) P.right.low = Q.p.right.low;
            if (P.left.empty()) P.left = Q.p.left;
            else ref[P.left.low] = Q.p.left.high;
            P.left.low = Q.p.left.low;
        }

        if (!P.left.empty() || !P.right.empty()) {
            S.push_back({next_id++, P});
        }
        return true;
    }

    void remove_back_edges(EdgeKey e) {
        auto [u_parent, _v] = parse_key(e);
        int u = u_parent;

        while (!S.empty() && conflict_pair_lowest(S.back().p) == height[u]) {
            StackEntry popped = S.back(); S.pop_back();
            if (popped.p.left.low != kNoKey) side[popped.p.left.low] = -1;
        }

        if (!S.empty()) {
            StackEntry P = S.back(); S.pop_back();
            while (P.p.left.high != kNoKey && parse_key(P.p.left.high).second == u) {
                auto it = ref.find(P.p.left.high);
                P.p.left.high = (it != ref.end()) ? it->second : kNoKey;
            }
            if (P.p.left.high == kNoKey && P.p.left.low != kNoKey) {
                ref[P.p.left.low] = P.p.right.low;
                side[P.p.left.low] = -1;
                P.p.left.low = kNoKey;
            }
            while (P.p.right.high != kNoKey && parse_key(P.p.right.high).second == u) {
                auto it = ref.find(P.p.right.high);
                P.p.right.high = (it != ref.end()) ? it->second : kNoKey;
            }
            if (P.p.right.high == kNoKey && P.p.right.low != kNoKey) {
                ref[P.p.right.low] = P.p.left.low;
                side[P.p.right.low] = -1;
                P.p.right.low = kNoKey;
            }
            S.push_back(P);
        }

        if (lowpt[e] < height[u]) {
            EdgeKey hl = S.empty() ? kNoKey : S.back().p.left.high;
            EdgeKey hr = S.empty() ? kNoKey : S.back().p.right.high;
            if (hl != kNoKey && (hr == kNoKey || lowpt[hl] > lowpt[hr])) {
                ref[e] = hl;
            } else {
                ref[e] = hr;
            }
        }
    }

    bool dfs_testing(int root) {
        std::vector<int> dfs_stack{root};
        next_index.assign(n, 0);
        skip_init.clear();

        while (!dfs_stack.empty()) {
            int v = dfs_stack.back(); dfs_stack.pop_back();
            EdgeKey e = parent_edge[v];
            bool skip_final = false;
            int i = next_index[v];
            while (i < (int)ordered_adjs[v].size()) {
                int w = ordered_adjs[v][i];
                EdgeKey ei = make_key(v, w);

                if (!skip_init[ei]) {
                    stack_bottom[ei] = top_id();
                    if (ei == parent_edge[w]) {
                        dfs_stack.push_back(v);
                        dfs_stack.push_back(w);
                        skip_init[ei] = true;
                        skip_final = true;
                        break;
                    } else {
                        lowpt_edge[ei] = ei;
                        ConflictPair cp;
                        cp.right.low = ei;
                        cp.right.high = ei;
                        S.push_back({next_id++, cp});
                    }
                }

                if (lowpt[ei] < height[v]) {
                    if (w == ordered_adjs[v][0]) {
                        lowpt_edge[e] = lowpt_edge[ei];
                    } else {
                        if (!add_constraints(ei, e)) return false;
                    }
                }

                next_index[v]++;
                i = next_index[v];
            }
            if (!skip_final && e != kNoKey) remove_back_edges(e);
        }
        return true;
    }

    int sign_edge(EdgeKey start) {
        std::vector<EdgeKey> dfs_stack{start};
        std::unordered_map<EdgeKey, EdgeKey> old_ref;
        while (!dfs_stack.empty()) {
            EdgeKey e = dfs_stack.back(); dfs_stack.pop_back();
            auto it = ref.find(e);
            if (it != ref.end() && it->second != kNoKey) {
                dfs_stack.push_back(e);
                dfs_stack.push_back(it->second);
                old_ref[e] = it->second;
                ref[e] = kNoKey;
            } else {
                EdgeKey prev = kNoKey;
                auto o = old_ref.find(e);
                if (o != old_ref.end()) prev = o->second;
                side[e] = get_side(e) * get_side(prev);
            }
        }
        return side[start];
    }

    // Rotation list half-edge helpers.
    static void add_half_edge_first(std::vector<std::vector<int>>& rot, int v, int w) {
        auto& row = rot[v];
        if (std::find(row.begin(), row.end(), w) == row.end()) row.push_back(w);
    }
    // opts mode: 0=append, 1=ccw (insert after ref), 2=cw (insert before ref).
    static void add_half_edge(std::vector<std::vector<int>>& rot, int v, int w,
                              int mode, int ref_w) {
        auto& row = rot[v];
        if (std::find(row.begin(), row.end(), w) != row.end()) return;
        if (row.empty() || mode == 0 || ref_w < 0) {
            row.push_back(w);
            return;
        }
        auto it = std::find(row.begin(), row.end(), ref_w);
        if (it == row.end()) { row.push_back(w); return; }
        size_t idx = it - row.begin();
        if (mode == 1) row.insert(row.begin() + idx + 1, w);
        else row.insert(row.begin() + idx, w);
    }

    void dfs_embedding(int root) {
        std::vector<int> dfs_stack{root};
        std::vector<int> ind(n, 0);
        std::vector<int> left_ref(n, -1), right_ref(n, -1);
        while (!dfs_stack.empty()) {
            int v = dfs_stack.back(); dfs_stack.pop_back();
            int i = ind[v];
            while (i < (int)ordered_adjs[v].size()) {
                int w = ordered_adjs[v][i];
                ind[v]++;
                i = ind[v];
                EdgeKey ei = make_key(v, w);
                if (ei == parent_edge[w]) {
                    add_half_edge_first(rotation, w, v);
                    left_ref[v] = w;
                    right_ref[v] = w;
                    dfs_stack.push_back(v);
                    dfs_stack.push_back(w);
                    break;
                }
                if (get_side(ei) == 1) {
                    add_half_edge(rotation, w, v, 1, right_ref[w]);
                } else {
                    add_half_edge(rotation, w, v, 2, left_ref[w]);
                    left_ref[w] = v;
                }
            }
        }
    }

    void build_embedding() {
        for (int v = 0; v < n; ++v) {
            for (int w : ordered_adjs[v]) {
                EdgeKey e = make_key(v, w);
                nesting_depth[e] = sign_edge(e) * nesting_depth[e];
            }
        }
        for (int v = 0; v < n; ++v) sort_by_signed_nesting(v);

        rotation.assign(n, {});
        for (int v = 0; v < n; ++v) {
            int prev = -1;
            for (int w : ordered_adjs[v]) {
                add_half_edge(rotation, v, w, 1, prev);
                prev = w;
            }
        }

        for (int r : roots) dfs_embedding(r);

        // Face extraction via rotation traversal.
        std::unordered_set<EdgeKey> seen;
        faces.clear();
        for (int u = 0; u < n; ++u) {
            for (int v : rotation[u]) {
                EdgeKey start_key = make_key(u, v);
                if (seen.count(start_key)) continue;
                int start_u = u, start_v = v;
                int cur_u = start_u, cur_v = start_v;
                std::vector<int> face;
                while (true) {
                    EdgeKey ck = make_key(cur_u, cur_v);
                    if (seen.count(ck)) break;
                    seen.insert(ck);
                    face.push_back(cur_u);
                    const auto& adj = rotation[cur_v];
                    if (adj.empty()) { face.clear(); break; }
                    auto it = std::find(adj.begin(), adj.end(), cur_u);
                    if (it == adj.end()) { face.clear(); break; }
                    int idx = it - adj.begin();
                    int prev_idx = (idx - 1 + (int)adj.size()) % (int)adj.size();
                    int next_v = adj[prev_idx];
                    cur_u = cur_v;
                    cur_v = next_v;
                    if (cur_u == start_u && cur_v == start_v) break;
                }
                if (!face.empty()) faces.push_back(std::move(face));
            }
        }
    }

    bool run() {
        if (n > 2 && (int)edges.size() > 3 * n - 6) return false;

        init_adjacency();
        height.assign(n, -1);
        parent_edge.assign(n, kNoKey);

        for (int v = 0; v < n; ++v) {
            if (height[v] != -1) continue;
            height[v] = 0;
            roots.push_back(v);
            dfs_orientation(v);
        }
        for (int v = 0; v < n; ++v) {
            ordered_adjs[v] = directed_adjs[v];
            sort_by_signed_nesting(v);
        }
        for (int r : roots) {
            if (!dfs_testing(r)) return false;
        }
        build_embedding();
        return true;
    }
};

// Outer-face chooser (largest chord-free face), mirroring Python.
std::vector<std::string> choose_outer_face_from_faces(
        const std::vector<std::vector<std::string>>& faces,
        const std::vector<std::pair<std::string,std::string>>& edges) {
    auto ekey = [](const std::string& a, const std::string& b) {
        return (a < b) ? (a + "::" + b) : (b + "::" + a);
    };
    std::unordered_set<std::string> edge_set;
    for (const auto& [u, v] : edges) edge_set.insert(ekey(u, v));

    auto face_has_chord = [&](const std::vector<std::string>& f) {
        if (f.size() < 4) return false;
        int n = (int)f.size();
        for (int i = 0; i < n; ++i) {
            for (int j = i + 1; j < n; ++j) {
                bool is_boundary = (j == i + 1) || (i == 0 && j == n - 1);
                if (is_boundary) continue;
                if (edge_set.count(ekey(f[i], f[j]))) return true;
            }
        }
        return false;
    };

    std::vector<std::string> best;
    for (const auto& f : faces) {
        if (f.size() < 3) continue;
        if (face_has_chord(f)) continue;
        if (best.empty() || f.size() > best.size()) best = f;
    }
    return best;
}

} // namespace

Embedding lr_test(int n, const std::vector<std::pair<int,int>>& edges) {
    Embedding out;
    LRState st;
    st.n = n;
    st.edges = edges;
    if (!st.run()) {
        out.ok = false;
        out.reason = (n > 2 && (int)edges.size() > 3 * n - 6) ? "Euler bound violated"
                                                              : "LR constraints conflict";
        return out;
    }
    out.ok = true;
    out.rotation = std::move(st.rotation);
    out.faces = std::move(st.faces);
    return out;
}

Normalized normalize_edges(const std::vector<std::string>& node_ids,
                           const std::vector<std::pair<std::string,std::string>>& edge_pairs) {
    Normalized out;
    for (const auto& raw : node_ids) {
        if (out.index_by_id.count(raw)) continue;
        out.index_by_id[raw] = (int)out.id_by_index.size();
        out.id_by_index.push_back(raw);
    }
    std::unordered_set<EdgeKey> seen;
    for (const auto& pair : edge_pairs) {
        const auto& u = pair.first;
        const auto& v = pair.second;
        if (u == v) continue;
        if (!out.index_by_id.count(u)) {
            out.index_by_id[u] = (int)out.id_by_index.size();
            out.id_by_index.push_back(u);
        }
        if (!out.index_by_id.count(v)) {
            out.index_by_id[v] = (int)out.id_by_index.size();
            out.id_by_index.push_back(v);
        }
        int ui = out.index_by_id[u];
        int vi = out.index_by_id[v];
        int a = std::min(ui, vi), b = std::max(ui, vi);
        EdgeKey key = make_key(a, b);
        if (seen.count(key)) continue;
        seen.insert(key);
        out.edges.emplace_back(a, b);
    }
    return out;
}

StringEmbedding compute_planar_embedding(
        const std::vector<std::string>& node_ids,
        const std::vector<std::pair<std::string,std::string>>& edge_pairs) {
    StringEmbedding out;
    Normalized n = normalize_edges(node_ids, edge_pairs);
    Embedding emb = lr_test((int)n.id_by_index.size(), n.edges);
    out.id_by_index = n.id_by_index;
    out.index_by_id = n.index_by_id;
    if (!emb.ok) {
        out.ok = false;
        out.reason = emb.reason;
        return out;
    }
    // Map back to strings.
    for (const auto& [u, v] : n.edges) {
        out.edges.emplace_back(n.id_by_index[u], n.id_by_index[v]);
    }
    out.rotation.resize(emb.rotation.size());
    for (size_t i = 0; i < emb.rotation.size(); ++i) {
        out.rotation[i].reserve(emb.rotation[i].size());
        for (int w : emb.rotation[i]) out.rotation[i].push_back(n.id_by_index[w]);
    }
    out.faces.resize(emb.faces.size());
    for (size_t i = 0; i < emb.faces.size(); ++i) {
        out.faces[i].reserve(emb.faces[i].size());
        for (int w : emb.faces[i]) out.faces[i].push_back(n.id_by_index[w]);
    }
    out.outer_face = choose_outer_face_from_faces(out.faces, out.edges);
    out.ok = true;
    return out;
}

Planar3TreeInfo analyze_planar_3_tree(
    const std::vector<std::string>& node_ids,
    const std::vector<std::pair<std::string,std::string>>& edge_pairs) {
    Planar3TreeInfo r;
    auto emb = compute_planar_embedding(node_ids, edge_pairs);
    if (!emb.ok) { r.reason = "Graph is not planar"; return r; }
    int n = (int)emb.id_by_index.size();
    if (n < 3) { r.reason = "Need at least 3 vertices"; return r; }
    const auto& outer = emb.outer_face;
    if (outer.size() != 3) { r.reason = "Outer face is not a triangle"; return r; }
    int m = (int)emb.edges.size();
    if (m != 3 * n - 6) { r.reason = "Edge count does not match maximal planar graph"; return r; }

    // Build adjacency_sets.
    std::unordered_map<std::string, std::unordered_set<std::string>> adjacency;
    for (const auto& nid : emb.id_by_index) adjacency[nid] = {};
    for (const auto& [u, v] : emb.edges) {
        adjacency[u].insert(v);
        adjacency[v].insert(u);
    }
    std::unordered_set<std::string> outer_set(outer.begin(), outer.end());

    int unique_outer_apex = 0;
    for (const auto& v : emb.id_by_index) {
        if (outer_set.count(v)) continue;
        if (adjacency[v].count(outer[0]) && adjacency[v].count(outer[1]) && adjacency[v].count(outer[2])) {
            ++unique_outer_apex;
        }
    }
    if (unique_outer_apex != 1) {
        r.reason = "Outer face does not have a unique adjacent internal vertex";
        return r;
    }

    auto triangle_neighbors = [&](const std::array<std::string, 3>& ids) {
        return adjacency[ids[0]].count(ids[1]) && adjacency[ids[0]].count(ids[2])
            && adjacency[ids[1]].count(ids[2]);
    };

    std::unordered_set<std::string> remaining(emb.id_by_index.begin(), emb.id_by_index.end());
    bool changed = true;
    std::vector<Planar3TreeRecord> elimination;
    while (changed && (int)remaining.size() > 3) {
        changed = false;
        std::vector<std::string> ids(remaining.begin(), remaining.end());
        for (const auto& v : ids) {
            if (outer_set.count(v)) continue;
            std::vector<std::string> rem_neighbors;
            for (const auto& u : adjacency[v]) if (remaining.count(u)) rem_neighbors.push_back(u);
            if (rem_neighbors.size() != 3) continue;
            std::array<std::string, 3> tri{rem_neighbors[0], rem_neighbors[1], rem_neighbors[2]};
            if (!triangle_neighbors(tri)) continue;
            Planar3TreeRecord rec;
            rec.vertex = v;
            rec.parents[0] = rem_neighbors[0];
            rec.parents[1] = rem_neighbors[1];
            rec.parents[2] = rem_neighbors[2];
            elimination.push_back(rec);
            for (const auto& u : rem_neighbors) adjacency[u].erase(v);
            remaining.erase(v);
            changed = true;
            break;
        }
    }
    if ((int)remaining.size() != 3) { r.reason = "Could not eliminate to outer triangle"; return r; }
    std::vector<std::string> final_three(remaining.begin(), remaining.end());
    for (const auto& v : final_three) if (!outer_set.count(v)) {
        r.reason = "Remaining triangle does not match outer face";
        return r;
    }
    std::array<std::string, 3> tri{final_three[0], final_three[1], final_three[2]};
    if (!triangle_neighbors(tri)) {
        r.reason = "Final three vertices do not form a triangle";
        return r;
    }

    r.ok = true;
    r.embedding = emb;
    r.outer_face = outer;
    r.elimination = std::move(elimination);
    r.node_ids = emb.id_by_index;
    r.edges = emb.edges;
    return r;
}

} // namespace planarvibe::planarity
