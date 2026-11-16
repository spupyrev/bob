#include "stack_orders.h"

#include "bob/common.h"
#include "bob/graph_algorithms.h"
#include "bob/logging.h"

#include <algorithm>
#include <array>
#include <climits>
#include <cstdlib>
#include <functional>
#include <list>
#include <map>
#include <set>
#include <vector>

using namespace std;

// The recursion is EXPAND(C) over cycles with no external chords. A cycle context
// carries the P1-P6 state; §3's Step 1a dispatches on Cases 1, 2 and 3, Step 1b
// recurses into the cycles bounding nontrivial blocks, and Step 2 into the cycles
// K_j cut off by short edges of K.
// =========================================================================

// Anonymous: these type names are not unique across translation units.
namespace {

static bool edgesCross(int a, int b, int c, int d) {
  if (a > b) swap(a, b);
  if (c > d) swap(c, d);
  return (a < c && c < b && b < d) || (c < a && a < d && d < b);
}

// ---------------------------------------------------------------------------
// Peeling into levels (Y1989 §2).
// level 0 = vertices on the outer face; level i = vertices on the outer face
// after deleting all vertices of level < i. Equivalent to BFS distance from
// the set of outer-face vertices. Binding edges connect consecutive levels.
// ---------------------------------------------------------------------------
static vector<int> computeLevels(const PlanarGraph& g) {
  int n = g.numberOfVertices();
  vector<int> start;
  for (auto v : g.outerFace.vertices) start.push_back(v->index);
  CHECK(!start.empty(), "outer face is empty");
  vector<int> level = g.bfs(start);
  for (int i = 0; i < n; i++) {
    CHECK(level[i] >= 0, "vertex %d unreachable during peeling", i);
  }
  return level;
}

// ===========================================================================
// Two-level block analysis (Y1989 §2).

// Given a chordless outer cycle K (vertices in clockwise layout order) and the
// inner graph I induced by the level-1 vertices in K's interior, compute:
//   - the biconnected components (blocks) of I;
//   - the block tree rooted at the block of the first inner node;
//   - for each inner vertex, the block it is assigned to (highest block);
//   - each block's leader and dominator (first outer node adjacent to it).

// Definitions (Y1989 Section 2):
//   * "w sees edge (x,y)" if w~x, w~y and triangle (x,y,w) is a face.
//   * first inner node = third vertex of the inner face on the long edge
//     (v1, vk) of K.
//   * leader(B) = first vertex of B on any path from the first inner node to B.
//   * dominator(B) = first (lowest-index in K order) outer vertex adjacent to a
//     vertex assigned to B.
// ===========================================================================

// A block of the inner graph.
struct Block {
  vector<int> vertices;        // vertices of the block (original indices)
  vector<pair<int, int>> edges;
  int leader{-1};              // leader vertex (original index)
  int parent{-1};              // parent block index in the block tree (-1 = root)
  vector<int> children;        // child block indices
  int dominator{-1};           // dominator outer-vertex index (original)
};

struct TwoLevelAnalysis {
  map<int, int> outerPos;            // original index -> position along K
  vector<int> inner;                 // level-1 inner vertices
  vector<Block> blocks;              // biconnected components of the inner graph
  map<int, int> blockOfVertex;       // inner vertex -> assigned block index
  // Root of the block TREE: the block containing the first inner node. The inner
  // graph of a chordless K is connected (Y1989 p.39), so there is exactly one.
  int rootBlock{-1};
  int firstInnerNode{-1};
  // True for the analysis of Case 3's C', which p.55 reads RIGHT-TO-LEFT ("now we proceed
  // right-to-left since the leader is the last node v_l"). That reverses the index frame of
  // Lemma 1 and Lemma 4, which are stated over "a clockwise traversal": p.62 restates Lemma 4's
  // u_q for this frame as "the node of R with LEAST index q which is adjacent to u_l", where
  // p.44 says HIGHEST. Same node, two frames -- so any rule quoting an index extremum has to
  // know which frame it is in. Never infer this from `ctx.descending`: that is true of ordinary
  // descending block cycles and of p.59's leader-last K_s as well, so it conflates
  // "read right-to-left" with "is C''s".
  bool isCPrime{false};
};

// Lemma 4's u_q for one block, in the index frame of the analysis it belongs to.

// p.44: "u_q the node of B with HIGHEST index q that is adjacent to v_f", over "u_1,..., u_t
// the rest of the nodes of B in CLOCKWISE order".

// What is frame-dependent is the CLOCKWISE SEQUENCE, not the extremum. `blk.vertices` is p.43's
// counterclockwise order [u, u_t,..., u_1] as read in the frame of the analysis that built the
// block, so reversing its tail recovers u_1..u_t in THAT frame. Case 3's C' reads the same
// boundary right-to-left (p.55), which mirrors the sequence: there the tail is ALREADY
// u_1..u_t and reversing it would produce u_t..u_1.

// p.62's "the node of R with LEAST index q which is adjacent to u_l" is the same rule stated
// against the unmirrored sequence -- taking the least index of the reversed sequence is taking
// the highest index of the correct one. So the frame belongs to the sequence, and once the
// sequence is right, p.44's HIGHEST applies verbatim in both frames. Flipping the extremum
// instead leaves the sequence wrong, which is what made Lemma 4's FIRST part (the nodes BEFORE
// u_q -- a set that is frame-dependent even though u_q itself is not) fail on C''s blocks.

// `dominator` is the dominator IN FORCE, which is not always `blk.dominator`: p.54 makes the
// whole of Case 2's T_R "dominated by v_s", and the analysis that laid a block out may have
// given it a different p.42 dominator from the one that reaches it here.

// Returns the clockwise index, or -1 if no node is adjacent to the dominator. One function for
// every consumer, so no site can pick the wrong sequence: getting that wrong is the
// compounding-reversal trap, since with a leader-first counterclockwise store "mirror the
// order" and "flip the extremum" are the same operation on u_q -- they differ only on the
// nodes before it, and that is exactly what Lemma 4's first part constrains.
// ONE INTERPRETATION, p.44's HIGHEST index, in every frame including block R's.


static int lemma4UqIndex(const PlanarGraph& g, const Block& blk, int dominator,
                         bool cPrimeFrame, vector<int>* clockwiseOut = nullptr) {
  vector<int> cw(blk.vertices.begin() + 1, blk.vertices.end());
  if (!cPrimeFrame) reverse(cw.begin(), cw.end());   // u_1..u_t clockwise, in this frame
  int q = -1;
  for (int i = 0; i < (int)cw.size(); i++)
    if (g.vertices[cw[i]]->adjacent(g.vertices[dominator])) q = i;   // p.44's HIGHEST index
  if (clockwiseOut != nullptr) *clockwiseOut = cw;
  return q;
}

// Lemma 4's FIRST part, which the rest of §2 leans on and nothing here asserted.

// p.44: "Gamma(u_1) =... = Gamma(u_{q-1}) = {v_f}", derived from Lemma 1 -- every node before
// u_q in the clockwise order sees the dominator and NOTHING else. p.45 draws the consequence
// the layout depends on: "From Lemma 4, no forward binding edge is incident to a node u_i,
// i < q, from the last part of B", which is precisely what makes Lemma 5's same-block case go
// through. So if some u_i with i < q sees a second outer node, the boundary order is wrong for
// this frame and a forward binding edge will be emitted where p.45 forbids one.

// `outer` is the cycle whose nodes count as outer for this analysis. Checked wherever u_q is
// consumed, so a violation names the block and the offending node instead of surfacing later as
// a Lemma 5 crossing several rules downstream.
static void checkLemma4FirstPart(const PlanarGraph& g, const vector<int>& cw, int q,
                                 int dominator, const vector<int>& outer, int blockIdx) {
  for (int i = 0; i < q; i++) {
    vector<int> seen;
    for (int o : outer)
      if (g.vertices[cw[i]]->adjacent(g.vertices[o])) seen.push_back(o);
    CHECK(seen.size() == 1 && seen[0] == dominator,
          "Lemma 4 violated: node %d of block %d is u_%d, before u_q (q=%d), so p.44 makes "
          "Gamma of it {v_f} = {%d}, but it is {%s}. p.45 then puts a forward binding edge on a "
          "node it forbids one on, and Lemma 5's same-block case fails. The boundary order "
          "u_1..u_t = %s is wrong for this frame",
          cw[i], blockIdx, i + 1, q, dominator, to_string(seen).c_str(),
          to_string(cw).c_str());
  }
}

// Y1989 p.55's analysis of C' = (v_s,..., v_l), the cycle Case 3 expands to lay out region
// II. Every part of it is stated outright there, so it is RESTRICTED from the parent's
// analysis rather than recomputed:

//   "The cycle R is (v_s, v_{s+1},..., v_l) and its interior is region II. The first inner
//    node for K' is u which belongs to exactly one block (of region II), namely R... The
//    tree of blocks for the interior of K' is the subtree T_R of T rooted at R."

// Recomputing it geometrically is not an option: C' is closed by the long edge (v_s, v_l),
// which p.55 only imagines ("this edge does not exist"), so an interior walk would leak
// through the gap into region I.

// The outer positions come from C''s own node order, which is what makes the mirrored
// dominator of p.55 ("the LAST node v_i of K that sees B") the ORDINARY first-node dominator
// of this analysis: C' is read right-to-left, so its own first node is the parent's last.
static TwoLevelAnalysis restrictToRegionII(const TwoLevelAnalysis& parent,
                                           const vector<int>& cPrime, int R) {
  TwoLevelAnalysis a;
  for (int i = 0; i < (int)cPrime.size(); i++) a.outerPos[cPrime[i]] = i;
  // T_R: R and its descendants, REINDEXED DENSELY with R as block 0. Every rule that walks
  // the tree -- the preorder that orders a dominator group top-down, Rule 2's colour
  // propagation -- requires a gap-free tree rooted at index `rootBlock`.
  vector<char> keep(parent.blocks.size(), 0);
  {
    vector<int> st = {R};
    while (!st.empty()) {
      const int b = st.back(); st.pop_back();
      keep[b] = 1;
      for (int ch : parent.blocks[b].children) st.push_back(ch);
    }
  }
  vector<int> remap(parent.blocks.size(), -1);
  remap[R] = 0;
  a.blocks.push_back(parent.blocks[R]);
  a.blocks[0].parent = -1;          // R is the root of T_R (p.55)
  for (int b = 0; b < (int)parent.blocks.size(); b++) {
    if (!keep[b] || b == R) continue;
    remap[b] = (int)a.blocks.size();
    a.blocks.push_back(parent.blocks[b]);
  }
  for (auto& blk : a.blocks) {
    if (blk.parent >= 0) blk.parent = remap[blk.parent];
    vector<int> kids;
    for (int c : blk.children)
      if (c >= 0 && remap[c] >= 0) kids.push_back(remap[c]);
    blk.children = kids;
  }
  a.rootBlock = 0;
  a.isCPrime = true;
  // `blk.vertices` is NOT mirrored here, deliberately. p.43 defines the boundary order from the
  // plane ("starting at the leader of B traverse its boundary in counterclockwise order"), which
  // C''s right-to-left reading does not change. What the reading DOES mirror is the clockwise
  // sequence u_1..u_t that Lemma 1 and Lemma 4 are stated over, and `lemma4UqIndex` derives that
  // per frame from `isCPrime`. Mirroring the store as well double-counts the reversal, because the
  // store also feeds the LAYOUT order, which C''s frame does not mirror -- one role would be fixed
  // and the other broken.

  // Lemma 1(1) is asserted below in C''s own frame, as well as in the parent's analysis.
  // "The first inner node for K' is u" -- R's leader, which the parent laid out already.
  a.firstInnerNode = parent.blocks[R].leader;
  for (auto& kv : parent.blockOfVertex)
    if (keep[kv.second]) {
      a.blockOfVertex[kv.first] = remap[kv.second];
      a.inner.push_back(kv.first);
    }
  // R's leader is assigned to R's parent block in T, which is outside T_R, so it is not in
  // `blockOfVertex` above -- but p.55 makes it this analysis's first inner node, and it is a
  // vertex of R. Assign it to R, as §2 does for a root block's leader ("the root block of T
  // is assigned all the nodes that it contains").
  if (!a.blockOfVertex.count(a.firstInnerNode)) {
    a.blockOfVertex[a.firstInnerNode] = 0;   // R, after reindexing
    a.inner.push_back(a.firstInnerNode);
  }
  sort(a.inner.begin(), a.inner.end());
  return a;
}

// Lemma 1(1) (p.41) for one analysis, in ITS OWN index frame: along the clockwise order
// u_1..u_t of a block's non-leader nodes, Gamma is nondecreasing, where "S <= U" is p.41's
// "each member of S precedes or is equal to each member of U", i.e. max(S) <= min(U).

// The analysis builder asserts this for the frame it derives the boundary in (via §5's alpha).
// C''s analysis inherits those boundaries and reads them in the MIRRORED frame (p.55), so the
// property has to be re-asserted there -- it is the arbiter of whether the inherited sequence is
// admissible, and Lemma 5's same-block case is proved from it ("the claim follows from part (1)
// of Lemma 1", p.46). The leader is excluded throughout: it may see the whole span.
static void checkLemma1Part1(const PlanarGraph& g, const TwoLevelAnalysis& a, const char* frame) {
  for (int b = 0; b < (int)a.blocks.size(); b++) {
    const Block& blk = a.blocks[b];
    if ((int)blk.vertices.size() < 3) continue;      // no two non-leader nodes to compare
    vector<int> cw(blk.vertices.begin() + 1, blk.vertices.end());
    if (!a.isCPrime) reverse(cw.begin(), cw.end());  // u_1..u_t in this analysis's frame
    auto gammaPositions = [&](int v) {
      set<int> gs;
      for (Vertex* nbv : g.vertices[v]->neighbors()) {
        auto it = a.outerPos.find(nbv->index);
        if (it != a.outerPos.end()) gs.insert(it->second);
      }
      return gs;
    };
    for (size_t i = 0; i + 1 < cw.size(); i++) {
      const set<int> S = gammaPositions(cw[i]), U = gammaPositions(cw[i + 1]);
      if (S.empty() || U.empty()) continue;          // A3 guarantees nonempty; not this check's job
      CHECK(*S.rbegin() <= *U.begin(),
            "Lemma 1(1) violated in the %s frame for block %d: Gamma(%d) reaches position %d but "
            "the next node Gamma(%d) starts at position %d, so the clockwise order %s is not "
            "admissible in this frame",
            frame, b, cw[i], *S.rbegin(), cw[i + 1], *U.begin(), to_string(cw).c_str());
    }
  }
}

// Does `w` see edge (x,y) (Y1989 §2): w~x, w~y and triangle (w,x,y) is a face.
// Both faces incident to (w,x) are checked. The graph's OUTER face is excluded:
// at the top level it is itself a triangle, so it would otherwise satisfy "sees"
// even though the triangle is not interior. This matches how the other face
// selections in this file identify interior faces.
static bool sees(const PlanarGraph& g, int w, int x, int y) {
  Vertex* vw = g.vertices[w];
  if (!vw->adjacent(g.vertices[x]) || !vw->adjacent(g.vertices[y])) return false;
  Edge* e = vw->adjacentEdge(g.vertices[x]);
  for (bool right : {true, false}) {
    Face f = right ? g.extractRightFace(vw, e) : g.extractLeftFace(vw, e);
    if (f.length() == 3 && f.contains(g.vertices[x]) &&
        f.contains(g.vertices[y]) && f.contains(g.vertices[w]) &&
        !(f == g.outerFace))
      return true;
  }
  return false;
}

// Block tree for the interior of a chordless cycle `outerCycle`
// (given in clockwise layout order). `level` is the peeling level of every
// vertex; the inner vertices are those at level = outerLevel + 1 lying in the
// interior. Returns the analysis; used by both Section 2 and EXPAND.

// This routine assumes the standard setup of Y1989 Section 2: K chordless,
// interior faces triangulated. The first inner node is the third vertex of the
// inner face on the long edge (outer[0], outer.back()).

// STAGE 1 of the analysis: the interior, the first inner node, and the RAW
// biconnected components -- everything needed to decide whether the graph must be
// augmented with a fictitious first inner node, and nothing that depends on that
// decision. Y1989 p.39 makes the augmentation a precondition of all of §2, so the
// block tree must not be rooted, leaders assigned or lemmas checked until it has
// been applied; `analyzeTwoLevel` below runs stage 2 on an already-clean graph.
static TwoLevelAnalysis analyzeTwoLevelRaw(const PlanarGraph& g,
                                           const vector<int>& outerCycle,
                                           const vector<int>& level) {
  TwoLevelAnalysis a;
  for (int i = 0; i < (int)outerCycle.size(); i++) a.outerPos[outerCycle[i]] = i;

  int outerLevel = level[outerCycle[0]];
  for (int c : outerCycle) CHECK(level[c] == outerLevel, "outer cycle spans multiple levels");

  // Inner vertices = the level-(outerLevel+1) vertices lying strictly INSIDE this
  // cycle. The interior must be determined GEOMETRICALLY, not by level alone:
  // sibling cycles are all at the same level, so walking from level-(l+1) vertex to
  // level-(l+1) vertex escapes this cycle's interior into a sibling's and pulls in
  // foreign vertices.
  set<int> onCycle(outerCycle.begin(), outerCycle.end());
  set<int> innerSet;
  {
    // Removing the cycle's vertices splits the rest of the graph into components,
    // each lying entirely inside or entirely outside the cycle. A component is
    // OUTSIDE iff it contains a vertex of the graph's outer face. (For the top-level
    // cycle -- the outer face itself -- there is no outside component, so every other
    // vertex is inside, as required.)
    set<int> outerFaceIds;
    for (auto v : g.outerFace.vertices) outerFaceIds.insert(v->index);

    set<int> visited;
    for (auto vptr : g.vertices) {
      int s = vptr->index;
      if (onCycle.count(s) || visited.count(s)) continue;
      vector<int> comp, stack = {s};
      visited.insert(s);
      bool outside = false;
      while (!stack.empty()) {
        int u = stack.back(); stack.pop_back();
        comp.push_back(u);
        if (outerFaceIds.count(u)) outside = true;
        for (Vertex* nb : g.vertices[u]->neighbors()) {
          int x = nb->index;
          if (onCycle.count(x) || visited.count(x)) continue;
          visited.insert(x);
          stack.push_back(x);
        }
      }
      if (outside) continue;  // exterior component
      for (int x : comp)
        if (level[x] == outerLevel + 1) innerSet.insert(x);
    }
  }
  a.inner.assign(innerSet.begin(), innerSet.end());

  // Edges of the inner graph I (both endpoints inner).
  vector<pair<int, int>> innerEdges;
  {
    set<pair<int, int>> seen;
    for (int u : a.inner) {
      for (Vertex* nb : g.vertices[u]->neighbors()) {
        int w = nb->index;
        if (innerSet.count(w)) {
          auto e = make_pair(min(u, w), max(u, w));
          if (seen.insert(e).second) innerEdges.push_back(e);
        }
      }
    }
  }

  // FIRST INNER NODE (Y1989 §2): the third vertex of the interior face on the
  // long edge (v1,vk) -- i.e. the INNER vertex adjacent to BOTH v1 and vk.
  // This choice is not cosmetic: it roots the block tree, and rooting at the
  // wrong vertex reorders whole blocks.
  int v1 = outerCycle.front(), vk = outerCycle.back();
  if (!innerSet.empty()) {
    Edge* e = g.vertices[v1]->adjacentEdge(g.vertices[vk]);
    CHECK(e != nullptr, "long edge (%d,%d) missing", v1, vk);
    // Y1989 defines a as the third vertex of the interior FACE on the long edge,
    // so identify it from the embedding rather than by adjacency alone: several
    // inner vertices may be adjacent to both ends, and only the face apex is the
    // first inner node. Getting this wrong also breaks addFictitiousInner, which
    // needs the triangle (v1, a, vk) to be a face in order to insert a' inside it.
    for (bool right : {true, false}) {
      Face f = right ? g.extractRightFace(g.vertices[v1], e)
                     : g.extractLeftFace(g.vertices[v1], e);
      if (f.length() != 3) continue;
      for (Vertex* fv : f.vertices) {
        int x = fv->index;
        if (x != v1 && x != vk && innerSet.count(x)) {
          a.firstInnerNode = x;
          break;
        }
      }
      if (a.firstInnerNode >= 0) break;
    }
    // The apex is guaranteed to exist: Y1989 §3 Step 1 calls EXPAND on K, the
    // boundary of the inner face of G_C on the long edge, which is chordless by
    // construction. Its absence therefore means the caller passed a cycle that is not
    // such a K. There is no substitute -- any other inner vertex would re-root the
    // whole block tree and silently change the layout.
    CHECK(a.firstInnerNode >= 0,
          "the long edge (%d,%d) has no inner apex: no inner vertex is adjacent "
          "to both ends, although the cycle has %d inner vertices. The cycle "
          "passed in is not a chordless K (Y1989 §3 Step 1).",
          v1, vk, (int)innerSet.size());
  }

  // Blocks of the inner graph. Compact inner vertices to a dense index space
  // for biconnectedComponents, then map back.
  if (!a.inner.empty()) {
    map<int, int> toLocal;
    vector<int> toGlobal;
    for (int u : a.inner) { toLocal[u] = (int)toGlobal.size(); toGlobal.push_back(u); }
    vector<pair<int, int>> localEdges;
    for (auto& e : innerEdges) localEdges.push_back({toLocal[e.first], toLocal[e.second]});

    if (a.inner.size() == 1) {
      // single inner vertex: a degenerate block
      Block b;
      b.vertices = {a.inner[0]};
      a.blocks.push_back(b);
    } else {
      auto comps = biconnectedComponents((int)a.inner.size(), localEdges);
      set<int> covered;
      for (auto& comp : comps) {
        Block b;
        set<int> vs;
        for (auto& e : comp) {
          int gu = toGlobal[e.first], gv = toGlobal[e.second];
          b.edges.push_back({gu, gv});
          vs.insert(gu); vs.insert(gv);
        }
        b.vertices.assign(vs.begin(), vs.end());
        covered.insert(vs.begin(), vs.end());
        a.blocks.push_back(b);
      }
      // Inner vertices with no inner edge are isolated: each is a DEGENERATE block on
      // its own, so that every inner vertex has a block assignment.
      for (int u : a.inner)
        if (!covered.count(u)) {
          Block b;
          b.vertices = {u};
          a.blocks.push_back(b);
        }
    }
  }

  return a;
}

// Y1989 §5's traversal of the inner graph's boundary (pp. 64-65), which is the paper's
// own construction of the block boundaries, their DIRECTION, and their leaders.

// The paper builds it in two steps. First beta, the binding edges "in the order they are
// scanned; first the edges of v_1, then of v_2, etc." -- at each node of K, the edges to
// not-yet-laid-out (i.e. inner) nodes, taken in rotation order. Then alpha: "if the inner
// node, say x_j, of b_j is different than the inner node, say x_{j+1}, of b_{j+1} then
// append the edge (x_j, x_{j+1})". Because G is triangulated, consecutive binding edges
// share a face, so each such (x_j, x_{j+1}) is an edge of the inner graph's boundary, and
// "alpha actually traces the boundary of the inner graph in CLOCKWISE order".

// THE ROTATIONAL SENSE IS ANCHORED TO THE LONG EDGE'S INTERIOR FACE, per frame.

// §5's scan is stated in the paper's own drawing convention -- "keep taking the next edge (in
// counterclockwise order around the leader)" (p.63), with p.62 defining "next" as the
// counterclockwise neighbour. That fixes the sense relative to the PAPER'S plane, not relative
// to a stored adjacency list: `CycleContext::nodes` is in logical order with the leader first,
// and p.49 licenses either spine direction ("otherwise, reverse the layout"), so a cycle handed
// to this walk may be stored in either traversal sense. So no single fixed physical direction is
// correct, and the sense has to be derived per frame from the embedding.

// The anchor is the long edge's INTERIOR FACE, which §2 already names. p.39 defines the first
// inner node `a` as the third vertex of the interior face on the long edge (v1, vk) -- so
// (v1, a, vk) IS a face of G. In a plane embedding, two edges of a common face at a shared
// vertex are ROTATIONALLY ADJACENT there. Hence at v1 the edge to `a` is the immediate
// rotational neighbour of the long edge, on exactly one side, and that side is the interior.

// The sweep at K[0] starts from the long edge and steps inward, so the sense whose immediate
// successor of the long edge at v1 is `a` is the sense that sweeps the interior wedge. It is a
// fact about this frame's embedding, needs no count, and has no tie: `a` lies on one side only.

// Returns true if the interior sense is the stored list's `after` direction.
static bool interiorSenseFromLongEdge(const PlanarGraph& g, const vector<int>& K,
                                      int firstInnerNode) {
  const int v1 = K.front(), vk = K.back();
  Edge* longEdge = g.vertices[v1]->adjacentEdge(g.vertices[vk]);
  CHECK(longEdge != nullptr,
        "Y1989 §5: the long edge (%d,%d) of K=%s is missing, so the interior sense has no "
        "anchor", v1, vk, to_string(K).c_str());
  Vertex* vv = g.vertices[v1];
  const int afterNb = vv->findEdgeAfter(longEdge)->other(vv)->index;
  const int beforeNb = vv->findEdgeBefore(longEdge)->other(vv)->index;
  // p.39's apex is rotationally adjacent to the long edge at v1, on the interior side only.
  // Both sides agreeing would mean v1 has degree 2, which a triangulated interior excludes.
  const string where = "long edge (" + to_string(v1) + "," + to_string(vk) + ") of K=" +
                       to_string(K) + "; rotational neighbours at " + to_string(v1) + " are " +
                       to_string(afterNb) + " (after) and " + to_string(beforeNb) + " (before)";
  CHECK(afterNb == firstInnerNode || beforeNb == firstInnerNode,
        "Y1989 §5: neither rotational neighbour of the %s is the first inner node %d, but p.39 "
        "makes (v1, a, vk) a FACE, so the apex must be rotationally adjacent to the long edge "
        "there. The rotation system and the computed apex disagree", where.c_str(),
        firstInnerNode);
  CHECK(!(afterNb == firstInnerNode && beforeNb == firstInnerNode),
        "Y1989 §5: both rotational neighbours of the long edge at %d are the first inner node "
        "%d, so %d has degree 2 and there is no interior wedge to sweep", v1, firstInnerNode,
        v1);
  return afterNb == firstInnerNode;
}

// Returns the node sequence of alpha (with consecutive duplicates collapsed), starting at
// the first inner node. Empty if the walk cannot be formed.

// `useAfter` is the interior sense, determined by the caller from the long edge's interior face
// (`interiorSenseFromLongEdge`). The walk uses that same sense at every node of K.
static vector<int> innerBoundaryWalk(const PlanarGraph& g, const vector<int>& K,
                                     const set<int>& innerSet, bool useAfter) {
  // beta, exactly as §5 scans it (p.64): at the leader, start from the long edge and "keep
  // taking the next edge... until an edge is found to a node which has been already laid
  // out", which is v_2; the edges passed over on the way are the leader's binding edges.
  // At each later node v_j, start from the edge back to v_{j-1} and scan the same way to
  // v_{j+1}. The scan therefore sweeps only the wedge interior to K at each node, which is
  // what makes consecutive entries of beta share a face.

  const int klen = (int)K.size();
  // The sweep at K[j]: start from the edge back to v_{j-1} and step in the interior sense
  // until v_{j+1} is reached, collecting the inner nodes passed on the way. Those are p.64's
  // binding edges of v_j, "in the order they are scanned".
  auto sweep = [&](int j, vector<int>* into) {
    Vertex* vv = g.vertices[K[j]];
    const int from = (j == 0) ? K[klen - 1] : K[j - 1];
    Edge* start = vv->adjacentEdge(g.vertices[from]);
    if (start == nullptr) return false;
    const int stopAt = (j + 1 < klen) ? K[j + 1] : K[0];
    Edge* e = start;
    for (int step = 0; step < vv->degree(); step++) {
      e = useAfter ? vv->findEdgeAfter(e) : vv->findEdgeBefore(e);
      const int w = e->other(vv)->index;
      if (w == stopAt) return true;
      if (innerSet.count(w) && into != nullptr) into->push_back(w);
    }
    return false;
  };
  // ONE SENSE AT EVERY NODE, checked per node against an EXACT SET.

  // K bounds a single face of G_C, so the interior lies on the same rotational side at every one
  // of its nodes. The testable form of that: at each K[j], the inner vertices the selected wedge
  // sweeps must be ALL of K[j]'s inner neighbours -- no more and no fewer. Since every inner
  // neighbour of K[j] lies in one wedge or the other, equality here implies the OPPOSITE wedge
  // contains none, which is the property that makes the selected sense the interior one.

  // Each node must sweep exactly its inner neighbors in the selected wedge; the opposite wedge
  // must contain none.

  // Both senses always reach v_{j+1} (the scan is bounded by degree, so going the wrong way round
  // simply arrives from the other side), so ARRIVAL is not the discriminator. Which side the
  // inner nodes are on is.
  for (int j = 0; j < klen; j++) {
    vector<int> swept;
    if (!sweep(j, &swept)) return {};   // reported by the caller's own CHECK below
    const set<int> sweptSet(swept.begin(), swept.end());
    set<int> allInnerNbrs;
    for (Vertex* nb : g.vertices[K[j]]->neighbors())
      if (innerSet.count(nb->index)) allInnerNbrs.insert(nb->index);
    CHECK(sweptSet == allInnerNbrs,
          "Y1989 §5: at node %d of K=%s the interior wedge (the '%s' rotational sense, anchored "
          "at the long edge) sweeps the inner vertices {%s}, but %d's inner neighbours are {%s}. "
          "Every inner neighbour lies in one wedge or the other, so a mismatch means the "
          "opposite wedge holds some of them -- i.e. the interior is not on the same rotational "
          "side at every node of K, and K does not bound a single region",
          K[j], to_string(K).c_str(), useAfter ? "after" : "before",
          to_string(vector<int>(sweptSet.begin(), sweptSet.end())).c_str(), K[j],
          to_string(vector<int>(allInnerNbrs.begin(), allInnerNbrs.end())).c_str());
  }
  vector<int> beta;  // the inner endpoint of each binding edge, in scan order
  for (int j = 0; j < klen; j++)
    if (!sweep(j, &beta)) return {};
  if (beta.empty()) return {};
  // alpha: consecutive distinct inner endpoints, which are boundary edges of the inner
  // graph. The sequence closes, so the walk is cyclic; keep it as a node list.
  vector<int> alpha;
  for (size_t j = 0; j < beta.size(); j++) {
    const int x = beta[j], y = beta[(j + 1) % beta.size()];
    if (x == y) continue;
    if (alpha.empty()) alpha.push_back(x);
    CHECK(g.vertices[x]->adjacent(g.vertices[y]),
          "Y1989 p.64: consecutive binding edges of beta reach %d and %d, which are not "
          "adjacent, so alpha is not a walk on the inner boundary", x, y);
    alpha.push_back(y);
  }
  return alpha;
}

// §5's extraction of the blocks from alpha (p.65): "Take the edges of alpha in sequence. If
// the next edge... enters a new node x_{j+1} that has not been previously visited, then
// push the edge onto the stack; otherwise, pop the stack up to the previous occurrence of
// x_{j+1}. The popped edges trace the boundary of a block B of the inner graph. The leader
// of B is node x_{j+1}, the first node of B that was reached in the traversal."

// Since alpha is clockwise, each popped boundary comes out in clockwise order starting at
// the leader -- so this yields both the block's boundary CYCLE and its DIRECTION, with no
// appeal to Lemma 1(1). Returns one entry per block found: the boundary in clockwise order
// with the leader first.
static vector<vector<int>> blocksFromAlpha(const vector<int>& alpha) {
  vector<vector<int>> out;
  if (alpha.size() < 2) return out;
  vector<int> stack;            // node sequence of the current walk
  map<int, int> depth;          // node -> its index in `stack`, if present
  stack.push_back(alpha[0]);
  depth[alpha[0]] = 0;
  for (size_t j = 1; j < alpha.size(); j++) {
    const int y = alpha[j];
    auto seen = depth.find(y);
    if (seen == depth.end()) {
      depth[y] = (int)stack.size();
      stack.push_back(y);
      continue;
    }
    // Closing a cycle: everything above y's occurrence, plus y itself, is a block boundary
    // in clockwise order with y (the earliest-reached node) as its leader.
    const int at = seen->second;
    vector<int> cyc(stack.begin() + at, stack.end());
    if (cyc.size() >= 2) out.push_back(cyc);
    for (int i = at + 1; i < (int)stack.size(); i++) depth.erase(stack[i]);
    stack.resize(at + 1);
  }
  return out;
}

// dom(B), Y1989 p.42: the FIRST outer node adjacent to a vertex assigned to B, where
// "first" is by position along the cycle this analysis was built for.

// Case 3 needs no separate notion. p.55's mirrored dominator -- "we take now the dominator of
// a block B in region II to be the LAST node u_i of K (highest i) that sees B" -- is this same
// first-node rule applied to C', whose node order is the reverse of C's, so it falls out of
// building C''s own analysis rather than needing a direction flag.

// p.55 says "sees" where p.42 says "adjacent", and the two agree here: BBKR §2.1, restating
// this, defines u_f(B)/u_l(B) as "the smallest- and largest-indexed vertices of level L0 that
// see edges (v0,vk) and (v0,v1)" and then states "Equivalently, u_f(B) and u_l(B) are defined
// as the smallest- and largest-indexed vertices of N(B)" -- so plain adjacency is exact.

static vector<int> dominatorsToward(const PlanarGraph& g,
                                    const TwoLevelAnalysis& a) {
  const int nb = (int)a.blocks.size();
  vector<int> dom(nb, -1);
  for (int b = 0; b < nb; b++) {
    int best = -1, bestPos = INT_MAX;
    for (int v : a.blocks[b].vertices) {
      if (a.blockOfVertex.at(v) != b) continue;  // only vertices assigned to B
      for (Vertex* nbv : g.vertices[v]->neighbors()) {
        auto it = a.outerPos.find(nbv->index);
        if (it == a.outerPos.end()) continue;
        const bool better = (it->second < bestPos);
        if (better) {
          bestPos = it->second;
          best = nbv->index;
        }
      }
    }
    dom[b] = best;
  }
  return dom;
}

// Y1989 p.39: the first inner node `a` must belong to exactly one block, and that
// block must be seen by the first outer node v1. When either fails, a fictitious
// node a' is added inside the triangle (v1, a, vk) and becomes the new first inner
// node -- it then lies in the single trivial block (a,a'), which v1 sees.

// Takes a RAW analysis (stage 1): the predicate is about the blocks alone, and it
// must be decidable before anything is rooted.
static bool firstInnerNodeIsClean(const PlanarGraph& g,
                                  const TwoLevelAnalysis& an,
                                  const vector<int>& K);

// STAGE 2: root the block tree, assign vertices to blocks, order block
// boundaries, compute dominators, and check the structural lemmas. Every one of
// these presumes the first inner node is clean, so this runs only after any
// augmentation has been applied to `g`.
static TwoLevelAnalysis analyzeTwoLevel(const PlanarGraph& g,
                                        const vector<int>& outerCycle,
                                        const vector<int>& level) {
  TwoLevelAnalysis a = analyzeTwoLevelRaw(g, outerCycle, level);

  // The augmentation is a PRECONDITION of everything below (Y1989 p.39), not a
  // repair applied afterwards: with the first inner node a cutpoint, the root
  // block can have several children whose Gammas interleave, which breaks Lemma
  // 2(3) and hence Lemma 3, and every rule keyed on a dominator group is then
  // unsound. The caller is responsible for having augmented, so state the
  // precondition here rather than discovering it as a lemma failure.
  CHECK(firstInnerNodeIsClean(g, a, outerCycle),
        "analyzeTwoLevel called with an unclean first inner node (%d): it is a "
        "cutpoint of the inner graph, or its block is not seen by v1=%d. Y1989 "
        "p.39 requires the fictitious node a' to be added BEFORE the block tree "
        "is rooted.", a.firstInnerNode, outerCycle.front());

  // -- Root the block tree at the block containing the first inner node. ----
  if (!a.blocks.empty()) {
    int nb = (int)a.blocks.size();
    // vertex -> set of blocks containing it
    map<int, vector<int>> blocksOf;
    for (int b = 0; b < nb; b++)
      for (int v : a.blocks[b].vertices) blocksOf[v].push_back(b);

    // The root of the block forest is the component containing the FIRST INNER
    // NODE (Y1989 §2: the inner graph is "rooted" at the first inner node).
    // That node is the third vertex of the interior face on the long edge, so it
    // is always an inner vertex of this cycle and always lies in some block --
    // there is no principled "default" root, so a missing one is a bug in the
    // interior/first-inner-node computation and must fail loudly rather than be
    // papered over by picking block 0.
    CHECK(a.firstInnerNode >= 0,
          "first inner node not found although the cycle has %d inner vertices",
          (int)a.inner.size());
    CHECK(blocksOf.count(a.firstInnerNode),
          "first inner node %d belongs to no block", a.firstInnerNode);
    {
      // The first inner node is clean (asserted above), so it lies in EXACTLY one
      // block and there is no choice to make here -- ruling out an arbitrary root is
      // what the augmentation exists for.
      auto& bs = blocksOf[a.firstInnerNode];
      CHECK(bs.size() == 1,
            "first inner node %d lies in %d blocks; it is clean, so it must lie "
            "in exactly one", a.firstInnerNode, (int)bs.size());
      a.rootBlock = bs.front();
    }

    // Build block adjacency via shared cut vertices, then BFS from the root block
    // to orient parent/child and assign leaders. K is chordless here, so the inner
    // graph is connected (Y1989 p.39) and its blocks form a single TREE rooted at
    // the block of the first inner node -- the traversal below reaches every block,
    // which is asserted rather than assumed.
    vector<char> visited(nb, 0);
    vector<int> queueB;
    auto rootComponent = [&](int rb, int rootLeader) {
      visited[rb] = 1;
      a.blocks[rb].parent = -1;
      a.blocks[rb].leader = rootLeader;
      int qstart = (int)queueB.size();
      queueB.push_back(rb);
      for (int qi = qstart; qi < (int)queueB.size(); qi++) {
        int b = queueB[qi];
        for (int v : a.blocks[b].vertices) {
          for (int b2 : blocksOf[v]) {
            if (!visited[b2]) {
              visited[b2] = 1;
              a.blocks[b2].parent = b;
              a.blocks[b2].leader = v;  // shared cut vertex with parent
              a.blocks[b].children.push_back(b2);
              queueB.push_back(b2);
            }
          }
        }
      }
    };
    // The root block's leader IS the first inner node (Y1989 §2: the block tree is
    // rooted at the block containing it, and "the first inner node a appears first
    // among all inner nodes in the layout", p.43). Since that node lies in exactly
    // one block and rootBlock is that block, it is a vertex of the block by
    // construction -- there is nothing to select.
    {
      const vector<int>& rv = a.blocks[a.rootBlock].vertices;
      CHECK(find(rv.begin(), rv.end(), a.firstInnerNode) != rv.end(),
            "first inner node %d is not a vertex of its own root block %d (%s)",
            a.firstInnerNode, a.rootBlock, to_string(rv).c_str());
      rootComponent(a.rootBlock, a.firstInnerNode);
    }
    // The inner graph of a chordless K is CONNECTED (Y1989 p.39, third
    // observation / Heath's Lemma 4.1), so its blocks form a single TREE and the
    // traversal from the root block reaches all of them. There is no second
    // component to root, and therefore no root leader to invent: inventing one
    // meant picking the block vertex with the smallest outer-neighbour position,
    // which disagrees with the paper's notion of a leader.
    for (int b = 0; b < nb; b++)
      CHECK(visited[b],
            "block tree traversal from the root block %d missed block %d (%s), so "
            "the inner graph is disconnected -- Y1989 p.39 proves it is connected "
            "when K is chordless, so either the interior computation or the "
            "chordlessness of K is wrong",
            a.rootBlock, b, to_string(a.blocks[b].vertices).c_str());

    // -- Assign each inner vertex to its highest block (closest to root). ----
    // BFS order in queueB is by increasing depth, so the first block (in that
    // order) that contains a vertex is its highest block.
    for (int b : queueB) {
      for (int v : a.blocks[b].vertices) {
        if (!a.blockOfVertex.count(v)) a.blockOfVertex[v] = b;
      }
    }

    // §5's traversal alpha of the inner boundary, in CLOCKWISE order (p.65). It fixes the
    // direction of every block's boundary below, so it is computed once here.
    const set<int> innerSetForAlpha(a.inner.begin(), a.inner.end());
    // The interior rotational sense, anchored to the long edge's interior face via p.39's apex
    // -- which `a.firstInnerNode` already holds, computed from the embedding above. One
    // determined sense is passed in; the walk does not search.
    // One determined sense, anchored to the long edge's interior face (p.39), not
    // a choice between the two and not a retry.
    const bool alphaUsesAfter =
        interiorSenseFromLongEdge(g, outerCycle, a.firstInnerNode);
    const vector<int> alphaWalk =
        innerBoundaryWalk(g, outerCycle, innerSetForAlpha, alphaUsesAfter);
    const vector<vector<int>> alphaBlocks = blocksFromAlpha(alphaWalk);

    // -- Order each block's vertices along its boundary cycle, starting at ----
    // the leader (Y1989: "in the order they appear in a counterclockwise
    // traversal of the boundary of B starting from the leader").
    // The block is a cycle possibly with chords (inner graph is outerplanar).
    // The boundary is the block's unique cycle through all its vertices; we
    // recover it from G's rotation among block edges.
    for (int b = 0; b < nb; b++) {
      Block& blk = a.blocks[b];
      if ((int)blk.vertices.size() <= 2) {
        // Trivial/degenerate block: a single edge, or one isolated vertex. The
        // leader comes first; there is no boundary traversal to derive, and no
        // freedom to exploit -- the leader is fixed by the block tree (the
        // cutvertex shared with the parent, or the first inner node at a root).
        // Should a root trivial block's leader ever be genuinely ambiguous, it
        // must be resolved from the embedding, never by a scalar penalty.
        vector<int> ord;
        ord.push_back(blk.leader);
        for (int v : blk.vertices)
          if (v != blk.leader) ord.push_back(v);
        CHECK(ord.size() == blk.vertices.size(),
              "trivial block %d reorder dropped vertices (%d -> %d); leader %d "
              "may not belong to the block", b,
              (int)blk.vertices.size(), (int)ord.size(), blk.leader);
        blk.vertices = ord;
        continue;
      }
      // ---- Boundary order, from the rotation system ------------------------
      // Y1989 p.43: "starting at the leader of B traverse its boundary in
      // counterclockwise order, and list the nodes assigned to B as they are
      // encountered".

      // A block is a cycle possibly with chords, and is outerplanar, so every vertex
      // lies on its outer face: the boundary is the unique face walk of the block
      // subgraph visiting all its vertices (chord-bounded faces are shorter). Walk
      // faces of the block subgraph -- at each vertex leave by the next block edge in
      // rotation order after the arrival edge -- and take the walk of full length.
      const int t = (int)blk.vertices.size();
      set<pair<int, int>> blockEdge;
      for (auto& e : blk.edges)
        blockEdge.insert({min(e.first, e.second), max(e.first, e.second)});
      auto isBlockEdge = [&](int x, int y) {
        return blockEdge.count({min(x, y), max(x, y)}) != 0;
      };
      // One face walk of the block subgraph, starting along (start -> second).
      // `ccw` selects the rotation sense used to leave each vertex.
      auto traceFace = [&](int start, int second, bool ccw) {
        vector<int> path = {start};
        int prev = start, cur = second;
        const int maxSteps = 2 * (int)blk.edges.size() + 4;
        for (int guard = 0; cur != start && guard < maxSteps; guard++) {
          path.push_back(cur);
          Vertex* vc = g.vertices[cur];
          Edge* arrived = vc->adjacentEdge(g.vertices[prev]);
          if (arrived == nullptr) return vector<int>();
          Edge* e = arrived;
          int nxt = -1;
          for (int i = 0; i < vc->degree(); i++) {
            e = ccw ? vc->findEdgeBefore(e) : vc->findEdgeAfter(e);
            int cand = e->other(vc)->index;
            if (isBlockEdge(cur, cand)) { nxt = cand; break; }
          }
          if (nxt == -1) return vector<int>();
          prev = cur; cur = nxt;
        }
        if (cur != start) return vector<int>();
        return path;
      };
      // The outer face walk through the leader, in a FIXED rotation sense. Walking
      // faces of a plane subgraph with one consistent rule (at each vertex leave by
      // the next block edge after the arrival edge in rotation order) traverses
      // every internal face in one rotational direction and the outer face in the
      // other -- so the sense is not a free choice, it is inherited from G. Fixing
      // it means every block's boundary comes out in the same rotational direction,
      // and which of Y1989's two directions that is becomes a single global fact,
      // asserted below rather than decided per block.
      const bool kRotationSense = false;  // findEdgeAfter at every step
      vector<int> boundaryCycle;
      for (Edge* e0 : g.vertices[blk.leader]->edges) {
        int w = e0->other(g.vertices[blk.leader])->index;
        if (!isBlockEdge(blk.leader, w)) continue;
        vector<int> f = traceFace(blk.leader, w, kRotationSense);
        if ((int)f.size() != t) continue;
        if (set<int>(f.begin(), f.end()).size() != (size_t)t) continue;
        boundaryCycle = f;
        break;
      }
      // Every full-length walk is the same cycle up to direction and rotation -- a block is
      // outerplanar, so its outer face is the unique face through all its vertices -- and taking the
      // first is therefore not a choice among candidates. ASSERTED rather than assumed, immediately
      // below: if a block ever yields two genuinely different boundary cycles, the "outerplanar
      // block" premise has failed and the first walk would be an arbitrary pick.
      for (Edge* eChk : g.vertices[blk.leader]->edges) {
        const int wChk = eChk->other(g.vertices[blk.leader])->index;
        if (!isBlockEdge(blk.leader, wChk)) continue;
        for (bool senseChk : {false, true}) {
          vector<int> f2 = traceFace(blk.leader, wChk, senseChk);
          if ((int)f2.size() != t) continue;
          if (set<int>(f2.begin(), f2.end()).size() != (size_t)t) continue;
          vector<int> rev(f2.rbegin(), f2.rend());
          rotate(rev.begin(), find(rev.begin(), rev.end(), blk.leader), rev.end());
          CHECK(f2 == boundaryCycle || rev == boundaryCycle,
                "block %d has two different full-length boundary walks, %s and %s, so its "
                "boundary cycle is not determined by the embedding",
                b, to_string(boundaryCycle).c_str(), to_string(f2).c_str());
        }
      }
      CHECK(!boundaryCycle.empty(),
            "block %d (%d vertices, %d edges) has no face walk through its leader "
            "%d covering all its vertices -- it is not an outerplanar block",
            b, t, (int)blk.edges.size(), blk.leader);

      // Gamma(v) = the set of cycle positions adjacent to v (Y1989 p.41: "if u is an
      // inner node, we denote by Gamma(u) the set of outer nodes adjacent to u").
      auto gammaSet = [&](int v) {
        set<int> gs;
        for (Vertex* nbv : g.vertices[v]->neighbors()) {
          auto it = a.outerPos.find(nbv->index);
          if (it != a.outerPos.end()) gs.insert(it->second);
        }
        return gs;
      };
      // "S <= U", exactly as Y1989 p.41 defines it: "if S, U are two subsets of outer
      // nodes where each member of S precedes or is equal to each member of U", i.e.
      // max(S) <= min(U).

      // A spanning Gamma is not a counterexample to Lemma 1's chain
      // Gamma(u_1) <=... <= Gamma(u_t), because a vertex seeing the whole cycle is the
      // LEADER, and Lemma 1 states the chain over u_1..u_t only -- `lemma1Violations`
      // below therefore starts at index 1 and never takes the leader's Gamma as an
      // argument.
      auto gammaLeq = [&](const set<int>& S, const set<int>& U) {
        CHECK(!S.empty() && !U.empty(),
              "Gamma of a non-leader block vertex is empty, but every such vertex is "
              "adjacent to some cycle vertex (A3)");
        return *S.rbegin() <= *U.begin();
      };
      // Lemma 1 holds along u_1..u_t (the leader u is excluded: it may see the
      // whole span). Returns the number of consecutive pairs that violate it.
      auto lemma1Violations = [&](const vector<int>& ord) {
        int viol = 0;
        for (size_t i = 1; i + 1 < ord.size(); i++)
          if (!gammaLeq(gammaSet(ord[i]), gammaSet(ord[i + 1]))) viol++;
        return viol;
      };

      CHECK(boundaryCycle.front() == blk.leader,
            "boundary walk of block %d does not start at its leader %d", b,
            blk.leader);

      // ---- Which way round? --------------------------------------------------
      // The boundary is a cyclic sequence in a fixed rotational sense; which of Y1989's
      // two directions that is comes from §5's traversal alpha, which "traces the boundary
      // of the inner graph in CLOCKWISE order" (p.65). alpha visits every inner node, so a
      // block's own nodes appear along it in clockwise order; comparing two of them fixes
      // the sense of `boundaryCycle` without appealing to Gamma.

      // Deriving direction from the rotation system lets Lemma 1(1) serve as an
      // independent check below.
      vector<int> forward(boundaryCycle), reversed(boundaryCycle.rbegin(),
                                                   boundaryCycle.rend());
      rotate(reversed.begin(), find(reversed.begin(), reversed.end(), blk.leader),
             reversed.end());
      {
        // Find this block among alpha's popped boundaries by vertex set: §5's stack yields
        // one boundary per block, already in clockwise order.
        const set<int> mine(blk.vertices.begin(), blk.vertices.end());
        const vector<int>* cwFromAlpha = nullptr;
        for (const auto& cand : alphaBlocks) {
          if (set<int>(cand.begin(), cand.end()) == mine) { cwFromAlpha = &cand; break; }
        }
        CHECK(cwFromAlpha != nullptr,
              "block %d (%s) does not appear among alpha's popped boundaries, so §5's "
              "traversal and the biconnected decomposition disagree", b,
              to_string(blk.vertices).c_str());
        // Does `forward` run the same way round as alpha's clockwise boundary? Compare one
        // step: take the successor of `forward[0]` in each and see whether they agree.
        map<int, int> cwPos;
        for (int i = 0; i < (int)cwFromAlpha->size(); i++) cwPos[(*cwFromAlpha)[i]] = i;
        const int t2 = (int)cwFromAlpha->size();
        const int d0 = cwPos.at(forward[0]), d1 = cwPos.at(forward[1]);
        const bool forwardIsClockwise = ((d1 - d0 + t2) % t2 == 1);
        // p.43's layout order is the COUNTERCLOCKWISE traversal from the leader, so when
        // `forward` is the clockwise one we lay out `reversed`.
        blk.vertices = forwardIsClockwise ? reversed : forward;

      }
      // Lemma 1(1) (p.41) is an independent check rather than the definition: along the
      // clockwise traversal u_1..u_t, Gamma is nondecreasing. `blk.vertices` is the
      // counterclockwise order u, u_t,..., u_1, so its tail reversed is u_1..u_t.
      {
        vector<int> cw(blk.vertices.begin() + 1, blk.vertices.end());
        reverse(cw.begin(), cw.end());
        vector<int> withLeader = {blk.leader};
        withLeader.insert(withLeader.end(), cw.begin(), cw.end());
        CHECK(lemma1Violations(withLeader) == 0,
              "Lemma 1(1) violated for block %d: along its clockwise order %s, Gamma is not "
              "nondecreasing -- the boundary walk, the leader or alpha's direction is wrong",
              b, to_string(cw).c_str());
      }
    }

    // -- Dominator(B) (p.42): the FIRST outer node adjacent to a vertex assigned
    // to B, by position along this analysis's own cycle.
    {
      const vector<int> dom = dominatorsToward(g, a);
      for (int b = 0; b < nb; b++) a.blocks[b].dominator = dom[b];
    }

    // -- Lemma 4's checks on u_q. u_q ITSELF IS NOT CACHED: it depends on the dominator, and
    // a block reachable from two cycles gets a different dominator in each analysis, so a
    // stored value is wrong for at least one of them. Every consumer recomputes it against the
    // dominator in force. `blk.vertices` is the counterclockwise layout order u, u_t,..., u_1,
    // so u_1..u_t clockwise is its tail reversed.
    for (int b = 0; b < nb; b++) {
      Block& blk = a.blocks[b];
      // A trivial block bounds no cycle, so it has no P2 to satisfy -- but u_q is also the
      // anchor Lemma 4 uses for a same-dominator CHILD ("Node u_q, the leader of the child of
      // B that is dominated by v_r"), and p.44 gives it explicitly here: "It is possible that
      // q = t or that q = 1 (or both in case t = 1 and B is a trivial block)." With t = 1 the
      // single assigned vertex is u_1 = u_q, so there is nothing to check for it.
      if ((int)blk.vertices.size() == 2) continue;   // t == 1: u_1 = u_q, nothing to check
      if ((int)blk.vertices.size() < 3) continue;  // isolated vertex: no edges at all
      vector<int> cw(blk.vertices.begin() + 1, blk.vertices.end());
      reverse(cw.begin(), cw.end());
      int q = -1;
      for (int i = 0; i < (int)cw.size(); i++)
        if (g.vertices[cw[i]]->adjacent(g.vertices[blk.dominator])) q = i;
      // Some non-leader node is always adjacent to the dominator, so u_q exists and P2's
      // "a node m of C, other than its leader" is satisfiable. For a NON-ROOT block the
      // leader is assigned to the parent, so by definition the dominator is adjacent to
      // some node assigned to this block, i.e. some u_i. For the ROOT block the leader
      // is the first inner node a, which is the apex of the long edge and so adjacent to
      // v_1, making v_1 the dominator; the augmentation of p.39 guarantees v_1 SEES the
      // root block, i.e. is adjacent to both endpoints of one of its edges, and at most
      // one endpoint can be the leader.
      CHECK(q >= 0,
            "Lemma 4: no non-leader node of block %d (%s, leader %d) is adjacent to its "
            "dominator %d, so the turning point u_q does not exist and P2 has no legal "
            "m. Either the dominator or the p.39 augmentation is wrong.",
            b, to_string(blk.vertices).c_str(), blk.leader, blk.dominator);
      // Lemma 4: "If q > 1, then the nodes u_1,...,u_{q-1} are adjacent to v_f BUT TO NO
      // OTHER OUTER NODE." p.60's clause-(a) argument depends on it -- those nodes are the
      // ones that carry only back edges -- so state it here, where u_q is chosen.
      for (int i = 0; i < q; i++) {
        for (Vertex* nbv : g.vertices[cw[i]]->neighbors()) {
          auto op = a.outerPos.find(nbv->index);
          if (op == a.outerPos.end()) continue;
          CHECK(nbv->index == blk.dominator,
                "Lemma 4 violated: node %d of block %d (index %d < q=%d) is adjacent to "
                "outer node %d, but Lemma 4 allows only the dominator %d",
                cw[i], b, i, q, nbv->index, blk.dominator);
        }
      }
    }

    // Lemma 3 (p.42): "The blocks dominated by the same outer node v_i form a
    // directed path in the tree T." Its proof rules out two UNRELATED blocks
    // sharing a dominator, so within one dominator group every pair must be
    // ancestor/descendant. A branching group means the dominators or the block
    // forest parenting is wrong, and every ordering rule keyed on the group (the
    // nested method, Rule 2's colour propagation) is then built on sand.
    {
      map<int, vector<int>> group;
      for (int b = 0; b < nb; b++)
        if (a.blocks[b].dominator >= 0) group[a.blocks[b].dominator].push_back(b);
      auto isAncestor = [&](int anc, int x) {
        for (int y = x; y >= 0; y = a.blocks[y].parent)
          if (y == anc) return true;
        return false;
      };
      // Lemma 2(1) (p.42): "the dominator is monotonically nondecreasing along any
      // path down the tree T". This is one half of Lemma 3's proof, so asserting it
      // separately localizes a violation to the dominators rather than the
      // parenting.
      for (int b = 0; b < nb; b++) {
        int par = a.blocks[b].parent;
        if (par < 0) continue;  // the root has no parent to compare against
        // Every block has a dominator (A3's corollary, asserted below) and every
        // dominator is a node of the cycle, so these lookups cannot fail.
        CHECK(a.blocks[b].dominator >= 0 && a.blocks[par].dominator >= 0,
              "Lemma 2(1): block %d or its parent %d has no dominator", b, par);
        auto pp = a.outerPos.find(a.blocks[par].dominator);
        auto pc = a.outerPos.find(a.blocks[b].dominator);
        CHECK(pp != a.outerPos.end() && pc != a.outerPos.end(),
              "Lemma 2(1): the dominator of block %d or of its parent %d is not a "
              "node of the cycle", b, par);
        CHECK(pp->second <= pc->second,
              "Lemma 2(1) violated: block %d has dominator %d at cycle position "
              "%d, but its parent %d has dominator %d at position %d -- the "
              "dominator must not decrease down the block tree",
              b, a.blocks[b].dominator, pc->second, par,
              a.blocks[par].dominator, pp->second);
      }

      // Lemma 2(3) (p.42): for two blocks UNRELATED in T, their outer
      // neighbourhoods satisfy Gamma(B) < Gamma(B') or Gamma(B') < Gamma(B) -- they
      // are never interleaved. This is the other half of Lemma 3's proof, and it is
      // the primitive that fails first when the block tree is mis-rooted.
      {
        auto countAssigned = [&](int b) {
          int c = 0;
          for (int v : a.blocks[b].vertices) {
            auto it = a.blockOfVertex.find(v);
            if (it != a.blockOfVertex.end() && it->second == b) c++;
          }
          return c;
        };
        auto gammaOf = [&](int b) {
          set<int> g_;
          for (int v : a.blocks[b].vertices) {
            auto it = a.blockOfVertex.find(v);
            if (it == a.blockOfVertex.end() || it->second != b) continue;
            for (Vertex* nb2 : g.vertices[v]->neighbors()) {
              auto op = a.outerPos.find(nb2->index);
              if (op != a.outerPos.end()) g_.insert(op->second);
            }
          }
          return g_;
        };
        for (int x = 0; x < nb; x++)
          for (int y = x + 1; y < nb; y++) {
            if (isAncestor(x, y) || isAncestor(y, x)) continue;
            set<int> gx = gammaOf(x), gy = gammaOf(y);
            // A3: every inner vertex has a cycle neighbour, so a block with any
            // assigned vertex has a non-empty Gamma. A block with NO assigned vertex
            // (all of them are leaders of descendants) is the one legitimate empty
            // case, and Lemma 2(3) says nothing about it.
            if (gx.empty() || gy.empty()) {
              CHECK(countAssigned(x) == 0 || countAssigned(y) == 0,
                    "Lemma 2(3): block %d or %d has assigned vertices but an empty "
                    "Gamma, contradicting A3", x, y);
              continue;
            }
            CHECK(*gx.rbegin() <= *gy.begin() || *gy.rbegin() <= *gx.begin(),
                  "Lemma 2(3) violated: unrelated blocks %d and %d have "
                  "interleaved outer neighbourhoods [%d,%d] and [%d,%d]",
                  x, y, *gx.begin(), *gx.rbegin(), *gy.begin(), *gy.rbegin());
          }
      }

      // B6: block-tree parenting is consistent with cutvertices. Y1989 p.40: "the
      // leader of B is the node of B that belongs also to its parent in the tree T",
      // and each node is assigned to "the highest block in T that contains it". So
      // for a vertex v lying in several blocks, exactly ONE of them is highest --
      // the one v is assigned to -- and v must be the LEADER of every other block
      // containing it.

      // Note this permits sibling blocks to share a cutvertex: several children of
      // one block can all have the same shared vertex as their leader. Two blocks
      // sharing a vertex are therefore not required to be in a parent/child
      // relation, only to agree on which one owns it.
      map<int, vector<int>> blocksContaining;
      for (int b = 0; b < nb; b++)
        for (int v : a.blocks[b].vertices) blocksContaining[v].push_back(b);
      for (auto& kv : blocksContaining) {
        const int v = kv.first;
        const vector<int>& bs = kv.second;
        if (bs.size() < 2) continue;
        auto owner = a.blockOfVertex.find(v);
        CHECK(owner != a.blockOfVertex.end(),
              "B6 violated: cutvertex %d lies in %d blocks but is assigned to none",
              v, (int)bs.size());
        for (int b : bs) {
          if (b == owner->second) continue;
          CHECK(a.blocks[b].leader == v,
                "B6 violated: vertex %d lies in block %d (assigned to block %d) but "
                "is not that block's leader (%d). Y1989 p.40 makes the shared vertex "
                "the leader of every block below the one owning it.",
                v, b, owner->second, a.blocks[b].leader);
        }
      }

      // B7 (Y1989 p.40): "the root block of T is assigned all the nodes that it
      // contains. Any other block is assigned all its nodes except its leader."
      // The assignment is computed independently (highest block in BFS order), so
      // this is a genuine cross-check on it rather than a restatement.
      for (int b = 0; b < nb; b++)
        for (int v : a.blocks[b].vertices) {
          const bool isLeaderOfNonRoot =
              (b != a.rootBlock && v == a.blocks[b].leader);
          auto it = a.blockOfVertex.find(v);
          CHECK(it != a.blockOfVertex.end(),
                "B7 violated: vertex %d of block %d has no assignment", v, b);
          if (isLeaderOfNonRoot) {
            CHECK(it->second != b,
                  "B7 violated: vertex %d is the leader of non-root block %d yet is "
                  "assigned to it; p.40 assigns it to the parent %d", v, b,
                  a.blocks[b].parent);
          } else {
            CHECK(it->second == b,
                  "B7 violated: vertex %d of block %d is not its leader, so p.40 "
                  "assigns it to %d, but it is assigned to %d", v, b, b, it->second);
          }
        }

      for (auto& kv : group) {
        const vector<int>& gs = kv.second;
        for (size_t i = 0; i < gs.size(); i++)
          for (size_t j = i + 1; j < gs.size(); j++)
            CHECK(isAncestor(gs[i], gs[j]) || isAncestor(gs[j], gs[i]),
                  "Lemma 3 violated (level %d, cycle length %d): blocks %d (%s) "
                  "and %d (%s) are unrelated in the block forest yet share "
                  "dominator %d. Y1989 p.42 proves this cannot happen, so the "
                  "dominators or the block-forest parenting are wrong.",
                  level[outerCycle.front()], (int)outerCycle.size(),
                  gs[i], to_string(a.blocks[gs[i]].vertices).c_str(), gs[j],
                  to_string(a.blocks[gs[j]].vertices).c_str(), kv.first);
      }
    }

  }

  // ---- §A input invariants for this cycle's two-level graph ----------------
  {
    // A3 (Y1989 p.39, second observation): "Every inner node is adjacent to some
    // outer node." This is what guarantees dominator >= 0 everywhere below.
    for (int u : a.inner) {
      bool hasOuter = false;
      for (Vertex* nb2 : g.vertices[u]->neighbors())
        if (a.outerPos.count(nb2->index)) { hasOuter = true; break; }
      CHECK(hasOuter,
            "A3 violated: inner vertex %d has no neighbour on the cycle, but "
            "Y1989 p.39 proves every inner node is adjacent to some outer node", u);
    }
    for (auto& blk : a.blocks)
      CHECK(blk.dominator >= 0,
            "A3 corollary violated: block with %d vertices has no dominator",
            (int)blk.vertices.size());

    // A4 (Y1989 p.39, first observation): "Every outer node is adjacent to some
    // inner node", which holds BECAUSE K has no chords -- so this doubles as a
    // chordlessness check on K.
    if (!a.inner.empty())
      for (int w : outerCycle) {
        bool hasInner = false;
        for (Vertex* nb2 : g.vertices[w]->neighbors())
          if (find(a.inner.begin(), a.inner.end(), nb2->index) != a.inner.end()) {
            hasInner = true; break;
          }
        CHECK(hasInner,
              "A4 violated: cycle node %d has no inner neighbour. Y1989 p.39 proves "
              "every outer node has one when K is chordless, so K has a chord",
              w);
      }

    // A2 (Y1989 p.~1071): "the subgraph induced by nodes at the same level is
    // outerplanar". Cheap necessary condition; this is the precondition for "a
    // block is a cycle plus chords, so its boundary is its unique Hamiltonian
    // cycle", which the whole boundary derivation rests on.
    {
      int vi = (int)a.inner.size(), ei = 0;
      set<int> innerSet(a.inner.begin(), a.inner.end());
      for (auto& e : g.extractEdgesId())
        if (innerSet.count(e.first) && innerSet.count(e.second)) ei++;
      if (vi >= 3)
        CHECK(ei <= 2 * vi - 3,
              "A2 violated: the inner graph has %d vertices and %d edges, exceeding "
              "the outerplanar bound 2n-3 = %d", vi, ei, 2 * vi - 3);
    }

    // A5 (Y1989 p.39, third observation / Heath Lemma 4.1): the inner graph I is
    // CONNECTED, so with K chordless its blocks form a single tree. That is now
    // structural rather than checked after the fact -- there is only one root by
    // construction -- and the residual statement is that every block is reachable
    // from it, asserted at the end of the tree traversal above.
    if (!a.inner.empty())
      CHECK(a.rootBlock >= 0 && a.rootBlock < (int)a.blocks.size(),
            "A5: the block tree has no valid root (rootBlock=%d, %d blocks)",
            a.rootBlock, (int)a.blocks.size());
  }

  return a;
}

// ===========================================================================
// Spine: a doubly-linked list of vertices supporting O(1) insertion right
// before / right after an already-placed vertex, as in Y1989 Section 5.

// NOTE on complexity: insertion is O(1), but `before()`/`rank()` read a rank cache
// that any insertion invalidates, so the realised cost is O(n) per query and O(n^2)
// overall -- not the linear-time bound §5 describes, which needs the order-maintenance
// structure §5 sketches. The whole-embedding check is likewise O(m^2). Both are accepted:
// the construction's correctness does not depend on either bound.
// ===========================================================================
struct Spine {
  list<int> seq;
  map<int, list<int>::iterator> loc;  // vertex -> its node in seq

  Spine() = default;
  Spine(const Spine& o) : seq(o.seq) {
    for (auto it = seq.begin(); it != seq.end(); ++it) loc[*it] = it;
  }
  Spine& operator=(const Spine& o) {
    if (this == &o) return *this;
    seq = o.seq;
    loc.clear();
    for (auto it = seq.begin(); it != seq.end(); ++it) loc[*it] = it;
    return *this;
  }

  bool placed(int v) const { return loc.count(v) != 0; }

  // is x before y on the spine? both must be placed
  bool before(int x, int y) const {
    // Distinguish the two failure modes rather than conflating them.
    CHECK(x >= 0 && y >= 0, "before(): negative vertex id (%d, %d)", x, y);
    const int rx = rank(x), ry = rank(y);
    return rx < ry;
  }
  // iterator to the element just after v; v must be placed
  std::list<int>::const_iterator iterAfter(int v) const {
    CHECK(placed(v), "iterAfter(): vertex %d is not on the spine", v);
    auto it = loc.at(v); ++it;
    return it;
  }
  // position of v along the spine; v must be placed
  // Position of `v` along the spine. Walks the list: the layout is built by insertion, so
  // there is no index to maintain.

  // Do NOT justify the linear scan by "every caller is already inside a quadratic per-cycle
  // check" -- that reasoning is what let SpineView::between call this once per element of
  // `seq`, making that O(n^2) per call and the verification pass cubic. Each caller has to pay
  // for its own scans: a loop over the spine must track its position itself, not ask here.
  int rank(int v) const {
    int r = 0;
    for (int x : seq) {
      if (x == v) return r;
      r++;
    }
    CHECK(false, "rank(): vertex %d is not on the spine", v);
    return -1;
  }

  void pushBack(int v) {
    CHECK(!placed(v), "vertex %d placed twice", v);
    seq.push_back(v);
    loc[v] = prev(seq.end());
  }
  // insert v immediately before the already-placed vertex `ref`
  void insertBefore(int v, int ref) {
    CHECK(!placed(v), "vertex %d placed twice", v);
    CHECK(placed(ref), "reference vertex %d not placed", ref);
    loc[v] = seq.insert(loc[ref], v);
  }
  // insert v immediately after the already-placed vertex `ref`
  void insertAfter(int v, int ref) {
    CHECK(!placed(v), "vertex %d placed twice", v);
    CHECK(placed(ref), "reference vertex %d not placed", ref);
    auto it = loc[ref]; ++it;
    loc[v] = seq.insert(it, v);
  }
};

// ===========================================================================

// Colors are 0..3. The four page indices are exactly these colors.

// Context for a cycle C being expanded: the P1-P6 state, all in original indices.

// EXPAND's contract is an INDUCTION (Y1989 §4): "if properties P1-P6 hold at the
// beginning, then upon termination of the call the layout is legal and satisfies the
// output constraints O1 and O2." So every field here is a precondition asserted on
// entry by `checkP1toP6`, and a caller that builds a child context wrongly is caught
// at the call that did it.
// One convention, stated once: `nodes` is ALWAYS in the paper's logical order, node 1
// (= index 0) being the leader, and `descending` says which way that order runs along the
// spine. p.49 licenses exactly this: "One of the extreme nodes of C, node 1 or node p, is
// specified as the leader... For concreteness, we assume without loss of generality that
// the leader is the first node 1; OTHERWISE, REVERSE THE LAYOUT."

// So every rule of §2/§3 -- P1-P6, the short-edge colours, the dominator, Step 1's
// numbering of K -- is written for logical indices and needs no direction test. Only the
// three operations that touch the SPINE do: "does x precede y", "insert before x", and the
// gap between consecutive nodes. Those go through the helpers below.
struct CycleContext {
  vector<int> nodes;   // C in LOGICAL order: nodes[0] is the leader, nodes[p-1] the far end
  // Which rule built this context (Step 1b block, Case 3 region II block, Step 2 K_j, or
  // the top-level call). Diagnostic only: a P1/P2 entry failure is always the fault of
  // whoever built the context, so the failure message can name it.
  const char* origin{"top"};
  // Set when this cycle bounds block R of a Case 3 C' call, i.e. p.62's doubly-exceptional
  // block: R alone keeps the increasing clockwise order and takes the LEAST-index u_q.
  // Diagnostic only -- no rule reads it; the construction tests `a.isCPrime && b == a.rootBlock`
  // at the site that needs it, so this cannot become a correctness input.
  bool isRofCPrime{false};
  // The cycle whose Step 1a built this one, in the same form `Builder::cycTag` records at
  // placement time. Diagnostic only: it lets a P2 entry failure say whether the vertices in
  // a gap came from this cycle's own parent or from an unrelated region.
  std::string parentTag{"(none)"};
  std::string cyclePath{"top"};
  int peelDepth{0};
  bool frameFictitiousClosure{false};
  // True when logical order runs right-to-left along the spine, i.e. nodes[0] is the
  // RIGHTMOST of C on the spine. Case 3's C' is the motivating case (p.55: "Regard u_l --
  // the last node of C' -- as the leader"), and p.59's K_s row is another.
  bool descending{false};
  int c0;              // P4: the leader's colour
  int c1;              // P5: the first colour
  int c2;              // P5: the second colour (may equal c0)
  // P2's turning point, as a LOGICAL index into `nodes`. m == p-1 means no border. Not an
  // index into K: p.52 brackets m between two nodes of K by position ("v_s <= m < m+1 <=
  // v_{s+1}"), and m itself may lie on a chord cycle and not be a node of K at all.
  int m;
  // P3: with a border (m < p-1), the border node adjacent to N2 is the attachment point and
  // the other the free point; vertex ids, or -1 when P3 is vacuous. p.49: "If N2 = 0 (or N2
  // is not adjacent to any node of C), the choice of attachment and free point is
  // arbitrary."
  int attachmentPoint{-1};
  int freePoint{-1};

  int size() const { return (int)nodes.size(); }
  int leader() const { return nodes.front(); }
  int farEnd() const { return nodes.back(); }
};

// The state every recursive call shares, passed by reference.

// The builder owns a MUTABLE working copy of the graph so it can insert
// fictitious first-inner nodes (Y1989 §2): when the first inner node of a
// cycle is a cutpoint of the inner graph, or its block is not seen by the
// leader, Yannakakis adds a node a' inside the triangle (v1, a, vk). Fictitious
// vertices get index >= nOrig; they carry no original edges, so the verifier
// (which sees only original edges) ignores them automatically.
struct Builder {
  PlanarGraph g;                   // mutable working copy of the input
  vector<int> level;               // peeling level of every (incl. fictitious) vertex
  int nOrig;                       // number of original vertices
  Spine spine;
  map<pair<int, int>, int> page;   // edge (min,max) -> color/page (original + fictitious)
  int verbose;
  Builder(const PlanarGraph& input, int verbose_) : verbose(verbose_) {
    g.copy(input);
    // Preserve the exact outer face of the input (copy() picks its own).
    vector<int> outerIds;
    for (auto v : input.outerFace.vertices) outerIds.push_back(v->index);
    CHECK(!outerIds.empty(), "input has no outer face");
    g.outerFace = g.extractFace(outerIds);
    nOrig = g.numberOfVertices();
  }

  bool isFictitious(int v) const { return v >= nOrig; }

  // `assignPage`  -- this site OWNS the edge: it must be unassigned.
  // `requirePage` -- already assigned elsewhere, and this site's rule says which page
  //                  that must have been. An edge on the boundary between two cycles is
  //                  claimed by both, and they must agree rather than the first
  //                  assignment silently standing.
  // Which rule assigned each edge, and in which cycle, so a colour disagreement names
  // the two rules responsible. Dumped at -verbose=5.
  map<pair<int, int>, string> provenance;
  string ruleTag, cycTag;
  // Which cycle's Step 1a placed each interior vertex (the cycTag at insertion time). p.51
  // partitions C's interior into K and the K_j "occupying disjoint intervals", so a vertex
  // found in a gap that P2 requires empty is a partition violation, and the only actionable
  // question is which cycle put it there.
  map<int, string> placedBy;

  void assignPage(int u, int v, int p) {
    auto key = make_pair(min(u, v), max(u, v));
    CHECK(p >= 0, "assignPage(%d,%d): negative page %d", u, v, p);
    // Ownership is checked BEFORE provenance is written: overwriting it first would
    // destroy the record of the rule that already owns the edge, which is the one fact
    // needed to diagnose the collision.
    auto ins = page.emplace(key, p);
    CHECK(ins.second,
          "assignPage(%d,%d,%d): edge is already on page %d, claimed by [%s] -- this site "
          "claims to own the edge, so a previous assignment means two rules both claim it",
          u, v, p, ins.first->second,
          provenance.count(key) ? provenance.at(key).c_str() : "(unrecorded)");
    provenance[key] = ruleTag + " pg=" + to_string(p) + " in[" + cycTag + "]";
    colouredHere.insert(key);
  }

  // The edges the Step 1a currently running has coloured. p.59's intermediate-node
  // property is about what "Step 1a [and] the expansion of any other new cycle" add, so
  // the check needs this set as data rather than inferring it from a log string.
  set<pair<int, int>> colouredHere;

  // The subset of `colouredHere` that Step 1a classified as FORWARD binding edges, for
  // Lemma 5. p.43 defines the classification by direction -- "a binding edge (v_i,u) is a
  // back edge if v_i comes before u in the layout; otherwise, it is forward" -- so each
  // site records its own verdict here. Every rule that colours a binding edge must write
  // to it: Lemma 5 is unconditional, and a set assembled from `ruleTag` spellings instead
  // would silently shrink whenever a log label is renamed.
  set<pair<int, int>> forwardBindingHere;
  void noteForwardBinding(int u, int v) {
    forwardBindingHere.insert(make_pair(min(u, v), max(u, v)));
  }
  // The logical direction of the instance that coloured each binding edge. Case 3's two
  // calls run in opposite directions over one Step 1a, so "before in the layout" is not a
  // per-Step-1a fact; recording it per edge lets `checkStep1aOutput` reproduce p.44's
  // forward/back test from the finished layout and compare with `forwardBindingHere`.
  map<pair<int, int>, bool> bindDir;
  // The edges p.55 has the CALLER colour before expanding C' -- "Give color c1 to these edges
  // (v_l, i)" -- so Step 1a's ownership check can recognise them as a legitimate class.
  set<pair<int, int>> cPrimeLeaderEdges;
  // The K_j leader-incident edges Step 2 colours (p.53), likewise a class of their own.
  set<pair<int, int>> kjLeaderEdges;
  // p.61's edges from C''s already-placed first inner node u. They connect an inner vertex to a
  // node of C, so they LOOK like binding edges, but p.61 treats them as level 1 edges of block R
  // ("All edges from u entering the interval [v_s,v_l] go to other nodes of R, and they all have
  // the color of the block R"). Recorded so the Lemma 5 check can exclude them by name rather
  // than by finding them absent from `bindDir`, which would also swallow a genuinely forgotten
  // classification.
  set<pair<int, int>> firstInnerLevel1Edges;
  // C''s node sequence for the Step 1a currently running, empty when this Step 1a has no C'.
  // Lets the ownership check test p.55's structure rather than trusting set membership.
  vector<int> cPrimeNodesHere;
  void noteBindingEdge(int u, int v, bool descending) {
    bindDir[make_pair(min(u, v), max(u, v))] = descending;
  }
  // The vertices that Step 1a put on the spine, for O1. Both are per-instance and are
  // cleared together at the top of Step 1a.
  vector<int> placedHere;

  void requirePage(int u, int v, int p) {
    auto key = make_pair(min(u, v), max(u, v));
    auto it = page.find(key);
    CHECK(it != page.end(),
          "requirePage(%d,%d,%d): edge has no page yet, but this site expects it "
          "to have been assigned already", u, v, p);
    CHECK(it->second == p,
          "requirePage(%d,%d,%d): edge is on page %d instead. The two rules that "
          "claim this edge disagree.", u, v, p, it->second);
  }

  // Add a fictitious node a' inside triangular face (v1, a, vk) and connect it
  // to all three, so a' becomes the new first inner node on the long edge
  // (v1, vk). Mirrors triangulateByStellation for a single face. Returns the
  // new vertex index. a' gets the level of the old first inner node a.
  int addFictitiousInner(int v1, int a, int vk) {
    // locate the triangular face (v1, a, vk)
    Edge* e = g.vertices[v1]->adjacentEdge(g.vertices[vk]);
    CHECK(e != nullptr, "long edge (%d,%d) missing for augmentation", v1, vk);
    // Select the face on the long edge that is INTERIOR to the current cycle.
    // Testing "the face that is not the graph's outer face" would only be valid
    // for the TOP-LEVEL cycle: for a recursion cycle neither incident face is the
    // graph's outer face, so such a test can pick the face OUTSIDE the cycle.
    // Identify it instead by the property actually needed: the face is a triangle
    // containing the first inner node `a`.
    Face f;
    {
      bool found = false;
      for (bool right : {true, false}) {
        Face cand = right ? g.extractRightFace(g.vertices[v1], e)
                          : g.extractLeftFace(g.vertices[v1], e);
        if (cand.length() == 3 && cand.contains(g.vertices[a])) {
          f = cand; found = true; break;
        }
      }
      CHECK(found,
            "neither face on the long edge (%d,%d) is a triangle containing the "
            "first inner node %d", v1, vk, a);
    }
    CHECK(f.contains(g.vertices[v1]) && f.contains(g.vertices[vk]),
          "long-edge face does not contain both %d and %d", v1, vk);

    Vertex* nv = g.newVertex();
    Edge* prevEdge = nullptr;
    for (size_t i = 0; i < f.vertices.size(); i++) {
      Vertex* u = f.vertices[i];
      Edge* edge = g.newEdge(nv, u);
      nv->addEdgeAfter(edge, prevEdge);
      u->addEdgeAfter(edge, f.edges[i]);
      prevEdge = edge;
    }
    if ((int)level.size() <= nv->index) level.resize(nv->index + 1, -1);
    level[nv->index] = level[a];  // same level as the old first inner node
    return nv->index;
  }
};

// Chords of cycle C: edges of G joining two non-consecutive nodes of C.
// EXPAND is only ever called on cycles with no EXTERNAL chords (invariant),
// so every such edge is an internal chord.
static vector<pair<int, int>> chordsOfCycle(const PlanarGraph& g,
                                            const vector<int>& C) {
  int p = (int)C.size();
  map<int, int> posInC;
  for (int i = 0; i < p; i++) posInC[C[i]] = i;
  vector<pair<int, int>> chords;
  for (int i = 0; i < p; i++) {
    for (Vertex* nb : g.vertices[C[i]]->neighbors()) {
      auto it = posInC.find(nb->index);
      if (it == posInC.end()) continue;
      int j = it->second;
      if (i < j) {
        int d = j - i;
        if (d != 1 && d != p - 1) chords.push_back({C[i], nb->index});
      }
    }
  }
  return chords;
}

// Y1989 §3 Step 1: G_C is C together with its internal chords; the chords cut
// C's interior into inner faces, and K is the one containing the long edge
// (v_1, v_p). Step 2 then recurses on each cycle K_j cut off by a short edge of
// K that is a chord of C.

// With C listed in layout order v_1..v_p, an internal chord is a pair of
// non-consecutive positions. K is obtained by walking from position 0 to p-1 and,
// at each step, following the chord that reaches FURTHEST forward (that is the
// edge of G_C bounding the long-edge face), or the cycle edge when no chord
// leaves the current position. Each such forward jump from i to j > i+1 cuts off
// the cycle K_j = (v_i, v_{i+1},..., v_j).
struct GcDecomposition {
  vector<int> K;                        // long-edge face of G_C, in layout order
  vector<pair<int, int>> chordCycles;   // (i, j) position pairs cutting off K_j
};

static GcDecomposition decomposeGc(const PlanarGraph& g, const vector<int>& C) {
  int p = (int)C.size();
  CHECK(p >= 3, "cycle passed to decomposeGc has only %d nodes", p);
  map<int, int> posInC;
  for (int i = 0; i < p; i++) posInC[C[i]] = i;

  // farthest forward position reachable from each position by a cycle edge or an
  // internal chord (never the long edge itself, which closes the cycle)
  vector<int> reach(p, -1);
  for (int i = 0; i < p; i++) {
    int best = (i + 1 < p) ? i + 1 : -1;   // the cycle edge
    for (Vertex* nb : g.vertices[C[i]]->neighbors()) {
      auto it = posInC.find(nb->index);
      if (it == posInC.end()) continue;
      int j = it->second;
      if (i == 0 && j == p - 1) continue;  // the long edge
      if (j > i) best = max(best, j);
    }
    reach[i] = best;
  }

  GcDecomposition d;
  d.K.push_back(C[0]);
  int cur = 0;
  int guard = 0;
  while (cur != p - 1) {
    CHECK(guard++ <= p, "K trace did not terminate on a %d-node cycle", p);
    int nxt = reach[cur];
    CHECK(nxt > cur, "cannot advance the K trace from position %d (reach=%d)",
          cur, nxt);
    d.K.push_back(C[nxt]);
    if (nxt > cur + 1) d.chordCycles.push_back({cur, nxt});
    cur = nxt;
  }
  CHECK(d.K.size() >= 3, "long-edge face of G_C has only %d nodes",
        (int)d.K.size());
  // K must be chordless: it is a face of G_C, so by construction no chord of C
  // joins two of its non-consecutive nodes.
  const vector<pair<int, int>> kChords = chordsOfCycle(g, d.K);
  CHECK(kChords.empty(),
        "the computed long-edge face K is not chordless (%d chords)",
        (int)kChords.size());

  // p.51 DEFINES K as "the cycle that bounds [the] inner face" of G_C containing the long
  // edge, and the trace above finds it by taking the farthest forward chord at each step.
  // That is a shortcut, so verify the result against the definition: K's own faces in G_C
  // must be a single face -- equivalently, walking C's nodes, every gap K skips is spanned
  // by a chord, and every node K keeps is reachable only by chords that do not skip it.

  // The economical form of that: each consecutive pair of K is an edge of G_C (a short edge
  // of C or a chord), and no chord of C strictly spans a pair of K's consecutive nodes --
  // if one did, the trace would have taken it and the face would be larger.
  {
    for (size_t i = 0; i + 1 < d.K.size(); i++)
      CHECK(g.vertices[d.K[i]]->adjacent(g.vertices[d.K[i + 1]]),
            "K's consecutive nodes %d and %d are not adjacent, so K is not a cycle of G_C",
            d.K[i], d.K[i + 1]);
    // The closing edge is C's long edge, which for Case 3's C' is FICTITIOUS -- p.55 imagines
    // it ("this edge does not exist") -- so its absence is legitimate exactly when C's own long
    // edge is absent. Tie the two together rather than requiring either outright.
    CHECK(g.vertices[d.K.front()]->adjacent(g.vertices[d.K.back()]) ==
              g.vertices[C.front()]->adjacent(g.vertices[C.back()]),
          "K's closing edge (%d,%d) and C's long edge (%d,%d) disagree on existence, so K is "
          "not the face on C's long edge", d.K.front(), d.K.back(), C.front(), C.back());
    // No chord of C reaches past a node K kept, from a node K kept.
    for (size_t i = 0; i + 1 < d.K.size(); i++) {
      const int lo = posInC.at(d.K[i]), hi = posInC.at(d.K[i + 1]);
      for (Vertex* nb : g.vertices[d.K[i]]->neighbors()) {
        auto it = posInC.find(nb->index);
        if (it == posInC.end()) continue;
        if (it->second > hi)
          CHECK(lo == 0 && it->second == p - 1,
                "chord (%d,%d) of C reaches past K's node %d, so the trace did not take the "
                "farthest chord and K is not the long-edge face", d.K[i], nb->index,
                d.K[i + 1]);
      }
    }
    // p.51 says "K and these cycles K_j partition the interior of C" -- a statement about the
    // INTERIOR, i.e. the plane regions, not about C's node set. At the node level it is not a
    // partition: p.51's "K_j is the cycle (v_j, v_{j+1},..., v_{j'})" shares both of its chord
    // endpoints WITH K, so those two nodes lie on two of the cycles.

    // What is checked below is the node-level corollary of the region partition, and it is
    // stated as such: every node of C is either on K or strictly inside exactly one K_j. It
    // follows because the trace advances `cur` monotonically, so the chord cycles' open spans
    // are pairwise disjoint, and every position is either landed on (hence on K) or skipped by
    // exactly one jump (hence strictly inside that one K_j). Checking it here catches a trace
    // that loses or double-counts a node, which would leave part of C's interior unexpanded.
    vector<int> cover(p, 0);
    for (const auto& cc : d.chordCycles)
      for (int x = cc.first + 1; x < cc.second; x++) cover[x]++;
    for (int i = 0; i < p; i++) {
      const bool onK = find(d.K.begin(), d.K.end(), C[i]) != d.K.end();
      CHECK(cover[i] + (onK ? 1 : 0) == 1,
            "node %d of C is on K or strictly inside a chord cycle %d times, not exactly once, "
            "so the K trace lost or double-counted it and part of C's interior would go "
            "unexpanded", C[i], cover[i] + (onK ? 1 : 0));
    }
  }
  return d;
}

// The two non-leader, non-c1, non-c2 colors, i.e. {0,1,2,3} \ {c1,c2}.
// These are Yannakakis' c3, c4 (used for level-1 and forward binding edges).
static pair<int, int> otherColors(int c1, int c2) {
  vector<int> rest;
  for (int c = 0; c < 4; c++) if (c != c1 && c != c2) rest.push_back(c);
  CHECK((int)rest.size() == 2, "c1==c2 not allowed");
  return {rest[0], rest[1]};  // deterministic: lower index first
}

// ---------------------------------------------------------------------------
// The two cycle constructions Step 1b and Step 2 recurse on. Both are pure §2/§3
// geometry: they read the cycle off the plane embedding, and carry no colouring state.
// ---------------------------------------------------------------------------

// Step 1b: the cycle bounding a nontrivial block, in layout order v1..vp.

// `blk.vertices` is the boundary cycle in leader-first order as read in the frame of the
// analysis that BUILT the block. p.53 fixes the leader ("the leader of a cycle bounding a
// nontrivial block is the leader of the block") and p.49 fixes the rest: "the nodes of C,
// listed in circular... order", node 1 the leader.

// p.49 fixes the sense: "the nodes of C, listed in circular (clockwise or counterclockwise)
// order", node 1 the leader, "otherwise, reverse the layout". So the cycle is returned in the
// sense that makes the leader logically first, and the caller says which way that sense runs
// along the spine.

// Two inputs decide which of the boundary's two senses that is, and they are independent:

//   `cPrimeFrame` -- whose frame the boundary was STORED in. p.55 has C' read the boundary
//     right-to-left, which mirrors the clockwise sequence exactly as it does for Lemma 1 and
//     Lemma 4 (p.50: "look at the plane from the back -- exchange clockwise and
//     counterclockwise in what follows"). So the stored tail is u_t..u_1 in an ordinary frame
//     and u_1..u_t in a C' frame.

//   `leaderActivelyLast` -- p.61/p.62's block R, whose leader the PARENT's T' pass laid out
//     "outside the interval [v_s,v_l]" rather than "right before v_l... as it would if C'
//     was expanded normally". Every other block's leader is actively first (p.43).

// The child's layout run is u, u_t,..., u_1 when the leader is actively first, and
// u_t,..., u_1, u for R. Read from the leader, those are [u, u_t,..., u_1] and
// [u, u_1,..., u_t] respectively -- the same cycle, opposite senses -- which is why R's
// cycle also runs the OPPOSITE way along the spine from its siblings'. That is p.62's
// exception in full, and it is the reason its leader is "laid out first" physically.

// The order matters twice over: CONSECUTIVE entries must be adjacent on the cycle so that
// the long edge is (v1,vp), and the leader must come first. Re-deriving either by scanning
// the current spine order would take the geometry from the layout rather than from the plane,
// so both are asserted here.
static vector<int> childCycleOfBlock(const Builder& B, const Block& blk, int b,
                                     bool cPrimeFrame, bool leaderActivelyLast) {
  vector<int> cyc = blk.vertices;
  CHECK((int)cyc.size() >= 3,
        "childCycleOfBlock called on trivial block %d (%d vertices); only "
        "nontrivial blocks bound a cycle", b, (int)cyc.size());
  // Mirror the TAIL so the leader stays node 1 (p.53). The store already reads the required
  // way when the frame's mirror and R's exception either both apply or neither does.
  if (cPrimeFrame != leaderActivelyLast) reverse(cyc.begin() + 1, cyc.end());
  // Every boundary vertex was laid out as an inner vertex of this level, so all of
  // them are on the spine. An assertion rather than a guard: skipping the recursion
  // would silently drop a whole subgraph.
  for (int v : cyc)
    CHECK(B.spine.placed(v), "child cycle vertex %d of block %d is not on the spine",
          v, b);
  // Which end of the spine run the leader occupies is NOT fixed. p.43's "the leader of B
  // precedes in the layout all other nodes of B" holds for a block laid out left-to-right,
  // but p.62 states the mirrored form for region II of Case 3: "each cycle bounding a
  // (nontrivial) block is laid out in clockwise order from right to left starting with the
  // leader. Or, in other words, an inner cycle is laid out in counterclockwise order from
  // left to right ENDING WITH THE LEADER. The only exception is block R whose leader u is
  // laid out first."

  // So both orientations are legal and the caller knows which it built. What must hold
  // either way is that the block occupies a contiguous logical run with the leader at one
  // END of it -- asserted here -- and the caller reads the direction off the spine.
  const bool leaderFirst = B.spine.before(cyc.front(), cyc[1]);
  for (size_t i = 1; i < cyc.size(); i++)
    CHECK(B.spine.before(cyc.front(), cyc[i]) == leaderFirst,
          "child cycle of block %d: the leader %d is not at one end of the block's spine "
          "run -- %d falls on the opposite side from %d", b, cyc.front(), cyc[i], cyc[1]);
  // A genuine cycle of G: consecutive entries adjacent, and the long edge present.
  for (size_t i = 0; i + 1 < cyc.size(); i++)
    CHECK(B.g.vertices[cyc[i]]->adjacent(B.g.vertices[cyc[i + 1]]),
          "child cycle of block %d is not a path: %d,%d not adjacent", b, cyc[i],
          cyc[i + 1]);
  CHECK(B.g.vertices[cyc.front()]->adjacent(B.g.vertices[cyc.back()]),
        "child cycle of block %d does not close: long edge (%d,%d) missing", b,
        cyc.front(), cyc.back());
  return cyc;
}

// The layout order of the nodes assigned to one dominator group: the blocks dominated
// by a common outer node v_f, given top-down (`group[0]` highest). Y1989 p.43 offers
// two methods and lets each dominator use either.

// CONSECUTIVE: "the blocks dominated by v_i are listed one after the other in top-down
// order of T... To order the nodes assigned to block B, starting at the leader of B
// traverse its boundary in counterclockwise order, and list the nodes assigned to B as
// they are encountered." `blocks[b].vertices` is already that traversal, so this is a
// concatenation.

// NESTED: "Starting from the leader of the highest block, traverse the boundary of the
// SUBGRAPH INDUCED BY THESE BLOCKS in counterclockwise order, and list the nodes
// assigned to them as they are first encountered." Lemma 4 gives the split point ("if B
// has a child B' which is also dominated by v_f, then the leader of B' is u_q"), so the
// order is the highest block's counterclockwise run with the rest of the group spliced
// in right after the next block's leader, recursively.

// The two agree on the nodes carrying forward binding edges (p.45), which is why Lemma 5
// holds for both.
static vector<int> blockGroupOrder(const TwoLevelAnalysis& a,
                                   const vector<int>& group, bool nested) {
  // Y1989 p.43 assigns each node to the highest block containing it, so a block's own
  // contribution is its counterclockwise boundary restricted to the nodes assigned to
  // it.
  // p.45/p.60 give the run explicitly: "u, u_t,..., u_q, u_{q-1},..., u_1" -- the leader, then
  // the non-leader nodes in DECREASING index order (with the nested method's splice after u_q).
  // `blk.vertices` stores that as [u, u_t,..., u_1] in the frame of the analysis that built the
  // block. C' reads the same boundary right-to-left (p.55), so in C''s frame the stored tail runs
  // u_1..u_t -- increasing -- and has to be mirrored to recover p.60's order.

  // This is the LAYOUT half of `blk.vertices`' two roles; the reading half (Lemma 1/Lemma 4's
  // u_1..u_t) is handled in `lemma4UqIndex` and `checkLemma1Part1`. Mirroring the STORE itself
  // would flip both at once, fixing one role and breaking the other.

  // Why this makes Lemma 5's same-block case hold, from p.46's proof: it argues from Lemma 1(1),
  // Gamma nondecreasing along u_1..u_t. If x precedes y in the layout and both lie in the
  // decreasing run, then index(x) > index(y), so Gamma(x) >= Gamma(y) and the two forward edges
  // cannot interleave. Get the run increasing instead and two forward edges on the same first
  // colour (p.60 puts u_q's and u_t..u_{q+1}'s alike there) cross.
  auto assignedOf = [&](int b) {
    const Block& blk = a.blocks[b];
    // The block's assigned nodes in STORE order. The store is p.43's counterclockwise
    // boundary from the leader, [u, x_1,..., x_k], in the frame of the analysis that BUILT
    // the block -- so its tail is u_t..u_1 in an ordinary frame and u_1..u_t in a C' frame,
    // which is the same split `lemma4UqIndex` makes for the reading role.
    vector<int> own;
    for (int v : blk.vertices)
      if (a.blockOfVertex.at(v) == b) own.push_back(v);
    if (!a.isCPrime || own.size() < 2) return own;

    // ---- C' frame: mirror the tail, and place the leader per p.61/p.62. -------------

    // The required ACTIVE run is p.43's counterclockwise traversal read in C''s own
    // direction, which p.55 imports unchanged ("the layout of the nodes... follow from our
    // description for Cases 1 and 2... remember only that now we proceed right-to-left").
    // Since C' reads the boundary from the back (p.50: "otherwise, look at the plane from the
    // back"), its clockwise sequence is the stored tail as it stands, so the counterclockwise
    // run u_t,..., u_1 is that tail MIRRORED -- for every block of C', not for R alone.

    // This is the direction Lemma 5's same-block case is proved from (p.46: "the claim
    // follows from part (1) of Lemma 1"), which needs x before y to give index(x) > index(y).
    // Leaving a C' block's tail unmirrored gives the opposite and lets two forward binding
    // edges of one block interleave on one page.

    // The leader's side is the one thing that differs between R and the rest:
    //   * an ordinary block: p.43's "the leader of B precedes in the layout all other nodes
    //     of B", so ACTIVELY FIRST -- which p.62 restates for this frame as "laid out in
    //     clockwise order from right to left STARTING WITH THE LEADER";
    //   * block R: p.61 puts its leader where the PARENT's T' pass left it, "outside the
    //     interval [v_s,v_l]" rather than "right before v_l... as it would if C' was
    //     expanded normally", and calls that "the only anomaly". Outside-to-the-left is C''s
    //     active LAST, and p.62's "block R whose leader u is laid out first" is the same fact
    //     read physically -- as is its printed "u, u_1,..., u_t", the physical left-to-right
    //     reading of the active run u_t,..., u_1, u.

    // R's leader is also `exc.alreadyPlaced`, so the caller skips it when emitting; its
    // position here matters only as the nested method's splice point.
    const bool ownsLeader = (own.front() == blk.leader);
    vector<int> tail(own.begin() + (ownsLeader ? 1 : 0), own.end());
    reverse(tail.begin(), tail.end());
    vector<int> out;
    const bool leaderLast = (b == a.rootBlock);   // p.61/p.62's block R
    if (ownsLeader && !leaderLast) out.push_back(blk.leader);
    for (int v : tail) out.push_back(v);
    if (ownsLeader && leaderLast) out.push_back(blk.leader);
    return out;
  };

  // Lemma 3: the group is a directed path in T. Lemma 2(1) makes the dominator
  // nondecreasing down T, so any block between two members of the group is itself in
  // the group -- consecutive members are therefore parent and child, which is what the
  // nested splice relies on.
  for (size_t i = 0; i + 1 < group.size(); i++)
    CHECK(a.blocks[group[i + 1]].parent == group[i],
          "dominator group is not a directed path: block %d does not follow its "
          "parent (block %d has parent %d)", group[i + 1], group[i + 1],
          a.blocks[group[i + 1]].parent);

  // p.62's two run shapes for a block inside C':
  //     ordinary block: u_t,..., u_1, u    -- the leader LAST
  //     block R:        u, u_t,..., u_1    -- the leader FIRST ("The only exception is block
  //                                            R whose leader u is laid out first")
  // In both, the NON-LEADER run is DECREASING in clockwise index, exactly as p.45 has it for
  // an ordinary frame: p.62's "clockwise order from right to left" changes the ACTIVE FRAME,
  // not the physical run, and does not authorise u_1,..., u_t in left-to-right order. Only
  // the leader's side moves between the frames.

  // Why the direction is load-bearing: Lemma 5's same-block inference is stronger than an
  // extrema comparison. With the decreasing run, x = u_r preceding y = u_s forces r > s, so
  // Lemma 1(1) gives Gamma(u_s) <= Gamma(u_r), which orders EVERY pair of endpoints and not
  // merely their extrema -- so v_j <= v_i and interleaving is excluded outright (equality
  // means the two edges share an outer endpoint, which is not a conflict). An increasing run
  // makes that inference unavailable, and p.44 puts all forward binding edges of one block on
  // ONE page, so two of them can then cross.

  // A non-root block's leader is assigned to its PARENT (p.40), so its position comes from
  // where the parent's run sits in this group, not from this block's own run. Reversing the
  // GROUP's block order to move it is wrong: the group's order and the insertion direction are not
  // independent -- the chain already lands in logical order, and reversing the emission reverses the
  // logical order too.

  if (!nested) {
    vector<int> out;
    for (int b : group)
      for (int v : assignedOf(b)) out.push_back(v);
    return out;
  }

  // Nested: splice the tail of the group in after the next block's leader.
  function<vector<int>(size_t)> nest = [&](size_t i) {
    vector<int> own = assignedOf(group[i]);
    if (i + 1 >= group.size()) return own;
    const int split = a.blocks[group[i + 1]].leader;
    const vector<int> tail = nest(i + 1);
    auto at = find(own.begin(), own.end(), split);
    // u_q is a node of this block assigned to it (the leader of a non-root block is
    // assigned to its parent), so it is always present.
    CHECK(at != own.end(),
          "nested method: the leader %d of block %d is not among the nodes assigned to "
          "its parent %d (%s), contradicting Lemma 4", split, group[i + 1], group[i],
          to_string(own).c_str());
    vector<int> out(own.begin(), at + 1);
    out.insert(out.end(), tail.begin(), tail.end());
    out.insert(out.end(), at + 1, own.end());
    return out;
  };
  return nest(0);
}

// Step 2: the cycle K_j cut off by a short edge of K that is a chord of C (p.51:
// "K_j is the cycle (v_j, v_j+1,..., v_{j+1})"), given as the position pair
// `cc` = (j, j+1) into `cyc`.
static vector<int> chordCycleNodes(const Builder& B, const vector<int>& cyc,
                                   const pair<int, int>& cc) {
  vector<int> kj;
  for (int t = cc.first; t <= cc.second; t++) kj.push_back(cyc[t]);
  CHECK((int)kj.size() >= 3, "chord cycle K_j has only %d nodes", (int)kj.size());
  // TERMINATION of the same-depth recursion: a K_j is expanded at its parent's
  // peeling depth, so no depth bound covers it and the decreasing measure is the
  // cycle length. It does decrease, because `decomposeGc` never follows the long edge
  // (0, p-1) when tracing K, so a chord cycle [cur,nxt] omits at least one node of C.
  // Asserted rather than left implicit: a bug making K_j == C would otherwise recurse
  // forever instead of failing.
  CHECK(kj.size() < cyc.size(),
        "K_j (%d nodes) is not shorter than its parent cycle (%d nodes), so the "
        "same-depth recursion has no decreasing measure and would not terminate",
        (int)kj.size(), (int)cyc.size());
  CHECK(B.g.vertices[kj.front()]->adjacent(B.g.vertices[kj.back()]),
        "chord cycle K_j does not close: chord (%d,%d) missing", kj.front(),
        kj.back());
  return kj;
}

// §D, the two-level self-check: Y1989 Theorem 1 (p.47) proves the subproblem just solved
// is legal in THREE pages, so restrict our own output to H = K + its interior and verify
// it independently.

// Two tests run. The first is per-page: no two edges of H on one page cross. The second
// is Theorem 1 itself, transferred by p.57's mapping -- "colors c3 and c4 are used in
// place of colors 2 and 3 there, and colors c1 and c2 are used in place of color 1
// there". §2's colour 1 is one class and p.44 proves it conflict-free ("Consequently,
// there is no conflict between any two edges with color 1"), so MERGING c1 and c2 must
// leave H crossing-free on three classes. `mergedPages` names the two that play colour 1.

// Restricted to H the merged class is a SUBSET of §2's colour-1 class, which is why the
// transfer is sound: §3 moves the border-crossing short edge out to c3, and p.57's swap
// ("if c0 != c2, we just switched the color of the edges that belong to v1 blocks with
// the color of the back edges to the leader v1") keeps exactly one of those two groups
// in the merged class. Dropping edges from a conflict-free class cannot create a
// conflict.

// The value is attribution: the global verifier reports a crossing between edges from
// two different depths without naming the cycle at fault, whereas this fails on one
// named cycle. If every level passes locally and the global embedding still fails, the
// bug is in the recycling and not the two-level machinery.
static void checkTwoLevelIsLegal(const Builder& B, const TwoLevelAnalysis& a,
                                 const vector<int>& K, const vector<int>& mergedPages,
                                 int peelDepth) {
  // H = K plus its level-1 interior; collect the edges we have coloured inside it.
  set<int> inH(K.begin(), K.end());
  for (int u : a.inner) inH.insert(u);
  vector<pair<int, int>> hEdges;
  map<pair<int, int>, int> hPage;
  for (auto& kv : B.page) {
    int x = kv.first.first, y = kv.first.second;
    if (!inH.count(x) || !inH.count(y)) continue;
    hEdges.push_back(kv.first);
    hPage[kv.first] = kv.second;
  }
  // Verify no two same-page edges of H cross, using the spine's induced order.
  for (size_t i = 0; i < hEdges.size(); i++)
    for (size_t j = i + 1; j < hEdges.size(); j++) {
      if (hPage[hEdges[i]] != hPage[hEdges[j]]) continue;
      int a1 = B.spine.rank(hEdges[i].first), b1 = B.spine.rank(hEdges[i].second);
      int a2 = B.spine.rank(hEdges[j].first), b2 = B.spine.rank(hEdges[j].second);
      if (edgesCross(a1, b1, a2, b2)) {
        // Which rule coloured each of the two, so the failure names the pair of rules
        // rather than only the pair of edges.
        auto rule = [&](const pair<int, int>& e) {
          auto it = B.provenance.find(e);
          return it == B.provenance.end() ? string("(ancestor)") : it->second;
        };
        LOG("§D crossing: (%d,%d) by [%s]", hEdges[i].first, hEdges[i].second,
            rule(hEdges[i]).c_str());
        // The placing rule for each endpoint too: a crossing whose endpoints were placed by
        // two DIFFERENT layout rules is a layout fault, and no recolouring can fix it.
        {
          const set<int> onK(K.begin(), K.end());
          for (int ep : {hEdges[i].first, hEdges[i].second})
            LOG("   endpoint %d %s placed by [%s]", ep, onK.count(ep) ? "ONK" : "interior",
                B.placedBy.count(ep) ? B.placedBy.at(ep).c_str() : "(never placed here)");
        }
        LOG("§D crossing: (%d,%d) by [%s]", hEdges[j].first, hEdges[j].second,
            rule(hEdges[j]).c_str());
      }
      CHECK(!edgesCross(a1, b1, a2, b2),
            "§D violated for the two-level graph of cycle %s (depth %d): edges "
            "(%d,%d) and (%d,%d) both on page %d cross. Y1989 Theorem 1 proves "
            "this subproblem is 3-page legal, so the two-level layout or its "
            "colouring is wrong for THIS cycle -- independently of recycling.",
            to_string(K).c_str(), peelDepth, hEdges[i].first, hEdges[i].second,
            hEdges[j].first, hEdges[j].second, hPage[hEdges[i]]);
    }
  // Theorem 1 proper: merge the two pages that play §2's colour 1 and re-run the same
  // crossing test on three classes. This is what the theorem actually asserts about the
  // subproblem, and unlike the per-page test above it can fail on a layout where each
  // individual page happens to be clean.
  CHECK(mergedPages.size() == 2,
        "§D: expected exactly two pages playing §2's colour 1, got %d",
        (int)mergedPages.size());
  auto klass = [&](const pair<int, int>& e) {
    const int pg = hPage[e];
    return (pg == mergedPages[0] || pg == mergedPages[1]) ? mergedPages[0] : pg;
  };
  for (size_t i = 0; i < hEdges.size(); i++)
    for (size_t j = i + 1; j < hEdges.size(); j++) {
      if (klass(hEdges[i]) != klass(hEdges[j])) continue;
      if (hPage[hEdges[i]] == hPage[hEdges[j]]) continue;  // reported by the test above
      const int a1 = B.spine.rank(hEdges[i].first), b1 = B.spine.rank(hEdges[i].second);
      const int a2 = B.spine.rank(hEdges[j].first), b2 = B.spine.rank(hEdges[j].second);
      if (!edgesCross(a1, b1, a2, b2)) continue;
      auto rule = [&](const pair<int, int>& e) {
        auto it = B.provenance.find(e);
        return it == B.provenance.end() ? string("(ancestor)") : it->second;
      };
      LOG("§D merged-class crossing: (%d,%d) pg=%d by [%s]", hEdges[i].first,
          hEdges[i].second, hPage[hEdges[i]], rule(hEdges[i]).c_str());
      LOG("                          (%d,%d) pg=%d by [%s]", hEdges[j].first,
          hEdges[j].second, hPage[hEdges[j]], rule(hEdges[j]).c_str());
      CHECK(false,
            "§D violated for the two-level graph of cycle %s (depth %d): edges (%d,%d) "
            "on page %d and (%d,%d) on page %d cross, and p.57 puts both pages in the "
            "class playing §2's colour 1, which Theorem 1 proves conflict-free",
            to_string(K).c_str(), peelDepth, hEdges[i].first, hEdges[i].second,
            hPage[hEdges[i]], hEdges[j].first, hEdges[j].second, hPage[hEdges[j]]);
    }
  LOG_IF(B.verbose >= 4,
         "§D: two-level graph of cycle %s (depth %d) is crossing-free per page and on "
         "the three classes of Theorem 1",
         to_string(K).c_str(), peelDepth);
}

// The only three operations that need to know which way logical order runs along the
// spine. Everything else in §2/§3 is stated in logical indices and uses none of them.

// `precedesLogically`  -- does x come before y in LOGICAL order, judged from the spine?
// `insertLogicallyBefore` -- put v immediately before `ref` in logical order, i.e. on the
//                        leader's side of it.
// `between`            -- the vertices strictly between two logical nodes.
struct SpineView {
  Builder& B;
  bool descending;

  bool precedesLogically(int x, int y) const {
    return descending ? B.spine.before(y, x) : B.spine.before(x, y);
  }
  void insertLogicallyBefore(int v, int ref) const {
    if (descending) B.spine.insertAfter(v, ref);
    else B.spine.insertBefore(v, ref);
    B.placedBy[v] = B.ruleTag + " ref=" + to_string(ref) + "@r" +
                    to_string(B.spine.rank(ref)) + " landed@r" +
                    to_string(B.spine.rank(v)) + " in[" + B.cycTag + "]";
    B.placedHere.push_back(v);
  }
  void insertLogicallyAfter(int v, int ref) const {
    if (descending) B.spine.insertBefore(v, ref);
    else B.spine.insertAfter(v, ref);
    B.placedBy[v] = B.ruleTag + " ref=" + to_string(ref) + " in[" + B.cycTag + "]";
    B.placedHere.push_back(v);
  }
  // Vertices lying strictly between the two given nodes on the spine, in logical order.

  // Deliberately does NOT call rank() per element: the loop walks `seq` in order, so the
  // position is just the loop counter, and `rank(v)` for a v drawn from `seq` would rescan
  // the whole list to recompute exactly that counter. Doing so made this O(n^2) per call
  // and the whole verification pass cubic.
  vector<int> between(int a, int b) const {
    const int ra = B.spine.rank(a), rb = B.spine.rank(b);
    const int lo = min(ra, rb), hi = max(ra, rb);
    vector<int> out;
    int r = 0;
    for (int v : B.spine.seq) {
      if (r > lo && r < hi) out.push_back(v);
      ++r;
    }
    if (descending) reverse(out.begin(), out.end());
    return out;
  }
};

// P1-P6 (Y1989 pp.48-50), asserted on ENTRY to EXPAND(C).

// §4's correctness argument is an induction with P1-P6 as its hypothesis, so these are
// preconditions, not results. Checking them here means a context built wrongly by a
// caller -- which is the failure mode Step 1b and Step 2 produce -- is reported at the
// call that built it, rather than as a crossing many levels deeper.

// P5 and P6 (p.49), factored out of `checkP1toP6`, which is its ONLY caller: they are ENTRY
// conditions, asserted when a cycle is entered.

// P1's "no interior vertex is on the spine" and P2's empty-gap clauses are deliberately NOT here:
// `checkP1toP6` keeps them, since they are the clauses a returned subtree necessarily falsifies and
// so belong only at entry.
static void checkP5andP6(const Builder& B, const CycleContext& ctx) {
  const vector<int>& C = ctx.nodes;
  const int p = (int)C.size();
  const SpineView sv{const_cast<Builder&>(B), ctx.descending};
  const int leader = ctx.leader();
  const int farEnd = ctx.farEnd();
  const bool hasBorder = (ctx.m < p - 1);
  (void)hasBorder;
  // P5, the property the four-page saving rests on. For the edges already coloured
  // that are NOT incident to nodes 1 and p:
  //   (a) all edges exiting [2, m-1]     have colour c1;
  //   (b) all edges exiting [m+2, p-1]   have colour c2;
  //   (c) all edges exiting [m, m+1]     have colour c1 or c2.
  // p.49 gives the equivalent form used here: by P2 and P4, clause (a) constrains
  // exactly the coloured edges incident to nodes 2..m-1 but not to the leader, and
  // likewise (b) for m+2..p-1.
  {
    // P5 constrains "the edges that are colored in L and are NOT INCIDENT to the first
    // and last nodes of C (nodes 1 and p)". The exemption covers either endpoint, so
    // both the node being scanned and its neighbour are checked against them.

    // It also constrains only the edges that EXIT the interval in question, and p.49
    // defines that precisely: "We say that an edge e exits an interval if one node of e is
    // in the interval and one outside." So an edge from an interval node to a vertex lying
    // strictly INSIDE that interval on the spine is not constrained -- which is what lets a
    // border node carry a c0 back edge to material sitting in the border itself.

    // Edges reaching outside C's span are NOT exempt: p.49's own gloss on clause (a) --
    // "all edges exiting the interval [2, m-1] have color c1" -- is exactly about edges from
    // C's interior nodes to material elsewhere in the layout, and it is what stops a
    // descendant cycle from reusing that page inside the span.
    // `loIdx`/`hiIdx` are indices into C; the interval is the spine span between those two
    // nodes inclusive. `v` need not be a node of C -- clause (c) also constrains the N2
    // vertices lying inside the border span.
    auto colouredEdgesOf = [&](int v, int loIdx, int hiIdx, auto&& fn) {
      if (v == leader || v == farEnd) return;
      const int r0 = B.spine.rank(C[loIdx]), r1 = B.spine.rank(C[hiIdx]);
      const int lo = min(r0, r1), hi = max(r0, r1);
      for (Vertex* nbv : B.g.vertices[v]->neighbors()) {
        const int w = nbv->index;
        auto pg = B.page.find(make_pair(min(v, w), max(v, w)));
        if (pg == B.page.end()) continue;
        const int rw = B.spine.rank(w);
        // p.49: "an edge e exits an interval if one node of e is in the interval and one
        // outside." The bound is INCLUSIVE, so an edge landing on an interval endpoint has
        // both ends inside and does not exit. This matters for clause (c), where the far end
        // may be a border node and the near end an N2 vertex within the span.
        if (rw >= lo && rw <= hi) continue;  // does not exit the interval
        fn(w, pg->second);
      }
    };
    // p.49 numbers C's nodes 1..p FROM THE LEADER, and P5's clauses are about those
    // logical numbers: "(a) All edges exiting the interval [2, m-1] have color c1; (b) all
    // edges exiting the interval [m+2, p-1] have color c2". `ctx.m` is an ARRAY index, so
    // the paper's m is ctx.m+1 when the leader is first and p-ctx.m when it is last, and
    // logical node j maps back to array index j-1 or p-j respectively.

    // Both clauses are inclusive at both ends. p.49's vacuity conditions -- "(a) is vacuous
    // if 2 = m, (b) if m >= p-2" -- then fall out of the bounds rather than being tested.
    const int mLogical = ctx.m + 1;
    auto idxOf = [&](int logical) { return logical - 1; };
    // The array indices of logical nodes 2..m-1 and m+2..p-1, as spans. Reading
    // right-to-left reverses each span, so take the endpoints and order them.
    const int aLo = min(idxOf(2), idxOf(mLogical - 1));
    const int aHi = max(idxOf(2), idxOf(mLogical - 1));
    const int bLo = min(idxOf(mLogical + 2), idxOf(p - 1));
    const int bHi = max(idxOf(mLogical + 2), idxOf(p - 1));
    const bool aNonEmpty = mLogical - 1 >= 2;
    const bool bNonEmpty = p - 1 >= mLogical + 2;

    // P5 interval oracle: what pages do the three P5 intervals ACTUALLY carry?

    // "Empty -> that side does not currently determine its role. One page -> the corresponding
    // role is forced to that page. More than one page -> upstream placement/colouring violation;
    // changing c1 or c2 cannot fix it."

    // Reported before the clause assertions below, so a failure is preceded by the full picture:
    // which role each side forces, and whether any assignment of (c1,c2) could satisfy P5 at all.
    {
      set<int> leftPages, rightPages, borderPages;
      if (aNonEmpty)
        for (int i = aLo; i <= aHi; i++)
          colouredEdgesOf(C[i], aLo, aHi, [&](int w, int pg) {
            if (w != leader && w != farEnd) leftPages.insert(pg);
          });
      if (bNonEmpty)
        for (int i = bLo; i <= bHi; i++)
          colouredEdgesOf(C[i], bLo, bHi, [&](int w, int pg) {
            if (w != leader && w != farEnd) rightPages.insert(pg);
          });
      LOG_IF(B.verbose >= 2,
             "P5OBL C=%s m=%d p=%d isR=%d c0=%d c1=%d c2=%d | left=%s right=%s",
             to_string(C).c_str(), ctx.m, p, (int)ctx.isRofCPrime, ctx.c0, ctx.c1, ctx.c2,
             to_string(vector<int>(leftPages.begin(), leftPages.end())).c_str(),
             to_string(vector<int>(rightPages.begin(), rightPages.end())).c_str());
      // A side carrying MORE THAN ONE page is an upstream placement/colouring violation, and no
      // assignment of (c1,c2) can satisfy P5 for it -- the clause demands a SINGLE colour on
      // everything exiting that interval. Asserted here rather than left to the clause below,
      // because the clause reports only the first offending edge and cannot say that the
      // obligation is unsatisfiable in principle.
      CHECK(leftPages.size() <= 1,
            "P5(a) obligations incompatible: edges exiting the leader-side interval of C=%s "
            "carry %d distinct pages {%s}, so no choice of c1 can satisfy P5(a) -- the fault is "
            "upstream, in the placement or colouring that produced them",
            to_string(C).c_str(), (int)leftPages.size(),
            to_string(vector<int>(leftPages.begin(), leftPages.end())).c_str());
      CHECK(rightPages.size() <= 1,
            "P5(b) obligations incompatible: edges exiting the far-side interval of C=%s carry "
            "%d distinct pages {%s}, so no choice of c2 can satisfy P5(b) -- the fault is "
            "upstream, in the placement or colouring that produced them",
            to_string(C).c_str(), (int)rightPages.size(),
            to_string(vector<int>(rightPages.begin(), rightPages.end())).c_str());
    }
    // Clause (a): logical nodes 2..m-1, the leader's side of the border, take c1.
    for (int i = aNonEmpty ? aLo : 1; aNonEmpty && i <= aHi; i++)
      colouredEdgesOf(C[i], aLo, aHi, [&](int w, int pg) {
        if (w == leader || w == farEnd) return;
        // Name the rule that coloured the offending edge: P5 is an ENTRY precondition, so the
        // culprit is an ancestor's Step 1a, not this cycle, and its provenance says which.
        if (pg != ctx.c1) {
          const auto pk = make_pair(min(C[i], w), max(C[i], w));
          auto pv = B.provenance.find(pk);
          LOG("P5(a) edge (%d,%d) provenance: %s", C[i], w,
              pv == B.provenance.end() ? "(none)" : pv->second.c_str());
        }
        CHECK(pg == ctx.c1,
              "P5(a) violated: edge (%d,%d) exits the leader-side interval with colour %d, "
              "not the first colour c1=%d (m=%d, C=%s, origin=%s)", C[i], w, pg, ctx.c1,
              ctx.m, to_string(C).c_str(), ctx.origin);
      });
    // Clause (b): logical nodes m+2..p-1, the far side of the border, take c2.
    for (int i = bNonEmpty ? bLo : 1; bNonEmpty && i <= bHi; i++)
      colouredEdgesOf(C[i], bLo, bHi, [&](int w, int pg) {
        if (w == leader || w == farEnd) return;
        // P5 is an ENTRY precondition, so a violation is an ancestor's colouring. Name the rule and
        // whether this cycle is p.62's block R, since p.62 is where the two P5 clauses swap roles --
        // diagnostic output only, so nothing here selects a rule.
        if (pg != ctx.c2) {
          const auto pk = make_pair(min(C[i], w), max(C[i], w));
          auto pv = B.provenance.find(pk);
          LOG("P5(b) edge (%d,%d) provenance: %s | C=%s isR=%d c0=%d c1=%d c2=%d", C[i], w,
              pv == B.provenance.end() ? "(none)" : pv->second.c_str(), to_string(C).c_str(),
              (int)ctx.isRofCPrime, ctx.c0, ctx.c1, ctx.c2);
        }
        CHECK(pg == ctx.c2,
              "P5(b) violated: edge (%d,%d) exits the far-side interval with colour %d, "
              "not the second colour c2=%d (m=%d, p=%d, leaderLast=%d)", C[i], w, pg,
              ctx.c2, ctx.m, p, (int)ctx.descending);
      });
    // Clause (c): the border nodes themselves. Vacuous when m == p, and p.49 also notes
    // "If m = p-1, clause (c) constrains only edges incident to p-1 and N2, but not the
    // edges incident to p" -- which is P5's blanket exemption for nodes 1 and p, applied
    // here because a border node can BE node p.
    if (hasBorder) {
      auto checkExits = [&](int v) {
        colouredEdgesOf(v, ctx.m, ctx.m + 1, [&](int w, int pg) {
          if (w == leader || w == farEnd) return;
          CHECK(pg == ctx.c1 || pg == ctx.c2,
                "P5(c) violated: edge (%d,%d) exits the border [m,m+1] with colour "
                "%d, which is neither c1=%d nor c2=%d (m=%d, C=%s, origin=%s)", v, w,
                pg, ctx.c1, ctx.c2, ctx.m, to_string(C).c_str(), ctx.origin);
        });
      };
      for (int i : {ctx.m, ctx.m + 1})
        if (C[i] != leader && C[i] != farEnd) checkExits(C[i]);  // P5 exempts 1 and p
      // p.49 reads [m, m+1] as a LAYOUT interval, not as the two-element set of C nodes:
      // "If m = p-1, clause (c) constraints only edges incident to p-1 AND N2, but not the
      // edges incident to p." So an edge from an N2 vertex that leaves the border span is
      // constrained to c1 or c2 as well.
      for (int v : sv.between(C[ctx.m], C[ctx.m + 1])) checkExits(v);
    }
  }

  // P6: "There is no edge of color c0 connecting node 2 to a node of N1." (N1 = the
  // nodes in the leader's interval (1,2).) It follows from P5 except when c0 == c2 and
  // m == 2, so it is asserted separately.
  if (p >= 2) {
    const int second = C[1];
    // N1 is the leader's own interval (1,2), i.e. whatever lies between logical nodes 1
    // and 2 -- which `between` locates whichever way logical order runs.
    const vector<int> n1 = sv.between(leader, second);
    for (int x : n1) {
      auto pg = B.page.find(make_pair(min(x, second), max(x, second)));
      if (pg == B.page.end()) continue;
      CHECK(pg->second != ctx.c0,
            "P6 violated: edge (%d,%d) joins node 2 to a vertex of N1 with the "
            "leader's colour c0=%d", x, second, ctx.c0);
    }
  }
}

static void checkP1toP6(const Builder& B, const CycleContext& ctx) {
  const vector<int>& C = ctx.nodes;
  const int p = (int)C.size();
  CHECK(p >= 3, "EXPAND called on a cycle with %d nodes", p);
  CHECK(ctx.c1 != ctx.c2, "P5 requires c1 != c2 (both are %d)", ctx.c1);
  CHECK(ctx.c1 != ctx.c0, "P5 requires c1 != c0 (both are %d)", ctx.c1);
  for (int c : {ctx.c0, ctx.c1, ctx.c2})
    CHECK(c >= 0 && c < 4, "colour %d is outside the four pages", c);
  // P2: "There is a node m of C, OTHER THAN ITS LEADER (i.e. 2 <= m <= p)" -- logical
  // node 2..p, so logical index 1..p-1.
  CHECK(ctx.m >= 1 && ctx.m <= p - 1,
        "P2 requires the turning point to be a non-leader node (m=%d, p=%d)", ctx.m, p);

  // P1: "The layout L includes all nodes of C, listed in circular (clockwise or
  // counterclockwise) order. It does not include any nodes inside C (in the planar
  // embedding)."
  const SpineView sv{const_cast<Builder&>(B), ctx.descending};
  for (int i = 0; i + 1 < p; i++) {
    // On failure, dump every node's rank with the turning point and the frame. P1 says only
    // "these two are out of order", but the fault is normally that one of p.60's two runs
    // (u_t..u_q and u_{q-1}..u_1) is listed against its placement, and that is only visible
    // with the whole run's ranks side by side.
    if (!sv.precedesLogically(C[i], C[i + 1])) {
      string ranks;
      for (int v : C)
        ranks += to_string(v) + "@" +
                 (B.spine.placed(v) ? to_string(B.spine.rank(v)) : string("np")) + " ";
      LOG("Cycle order: isR=%d desc=%d m=%d firstBadPair=%d ranks=%s", (int)ctx.isRofCPrime,
          (int)ctx.descending, ctx.m, i, ranks.c_str());
    }
    CHECK(sv.precedesLogically(C[i], C[i + 1]),
          "P1 violated: node %d of C does not precede %d in logical order along the "
          "spine, so C is not laid out in its own circular order. C=%s desc=%d "
          "ranks=%d,%d built by [%s]",
          C[i], C[i + 1], to_string(C).c_str(), (int)ctx.descending,
          B.spine.rank(C[i]), B.spine.rank(C[i + 1]), ctx.origin);
  }
  // The second sentence: nothing interior to C may be on the spine yet. EXPAND owns C's
  // interior, so a vertex of it already placed means an ancestor reached inside this
  // region -- which breaks O1's reserved-space claim and every disjointness argument
  // built on it. The interior is recomputed here rather than taken from the analysis,
  // which does not exist yet at entry.
  {
    const set<int> onC(C.begin(), C.end());
    set<int> outerFaceIds;
    for (auto v : B.g.outerFace.vertices) outerFaceIds.insert(v->index);
    set<int> visited;
    for (auto vptr : B.g.vertices) {
      const int start = vptr->index;
      if (onC.count(start) || visited.count(start)) continue;
      vector<int> comp, stack = {start};
      visited.insert(start);
      bool outside = false;
      while (!stack.empty()) {
        const int u = stack.back(); stack.pop_back();
        comp.push_back(u);
        if (outerFaceIds.count(u)) outside = true;
        for (Vertex* nbv : B.g.vertices[u]->neighbors()) {
          const int x = nbv->index;
          if (onC.count(x) || visited.count(x)) continue;
          visited.insert(x);
          stack.push_back(x);
        }
      }
      if (outside) continue;  // exterior component
      for (const int x : comp)
        CHECK(!B.spine.placed(x),
              "P1 violated: vertex %d lies inside cycle %s but is already on the spine, "
              "so something outside this call has laid out part of C's interior",
              x, to_string(C).c_str());
    }
  }

  // P2: "all intervals (i, i+1) between two consecutive nodes of C are empty, except
  // possibly for the interval (1,2) next to the leader, and for the interval
  // (m, m+1), if m < p."

  // `ctx.m` is the index such that the BORDER is the gap after it, and the leader's own
  // gap is at whichever end the leader sits: index 0 normally, index p-2 when the leader
  // is the last node (Case 3 and the K_s row of p.59, where the cycle is read
  // right-to-left).
  for (int i = 0; i + 1 < p; i++) {
    if (i == 0) continue;      // the leader's own interval (1,2), where N1 lives
    if (i == ctx.m) continue;  // the border (m,m+1) may be non-empty
    const vector<int> gap = sv.between(C[i], C[i + 1]);
    // CHECK takes at most 10 varargs, so the wordier context goes to a LOG first.
    if (!gap.empty()) {
      LOG("P2 context: C=%s desc=%d m=%d origin=%s", to_string(C).c_str(),
          (int)ctx.descending, ctx.m, ctx.origin);
      {
        string ranks;
        for (int q = 0; q < p; q++)
          ranks += " " + to_string(C[q]) + "@r" + to_string(B.spine.rank(C[q]));
        LOG("   C ranks:%s", ranks.c_str());
        string g;
        for (int x : gap) g += " " + to_string(x) + "@r" + to_string(B.spine.rank(x));
        LOG("   gap ranks:%s", g.c_str());
      }
      for (int x : gap)
        LOG("   foreign vertex %d was placed by cycle [%s]", x,
            B.placedBy.count(x) ? B.placedBy.at(x).c_str() : "(never placed by Step 1a)");
      LOG("   this cycle was built by [%s] from parent [%s]", ctx.origin,
          ctx.parentTag.c_str());
    }
    CHECK(gap.empty(),
          "P2 violated: %d foreign vertices sit in the interval (%d,%d) between nodes "
          "%d and %d of C, which is neither the leader's nor the border (m=%d)",
          (int)gap.size(), i + 1, i + 2, C[i], C[i + 1], ctx.m);
  }

  // P2 encodes "m == p" -- no border -- by putting the turning point at the node FARTHEST
  // from the leader, so the sentinel index is p-1 when the leader is first and 0 when it is
  // last (p.61's right-to-left reading).
  const bool hasBorder = (ctx.m < p - 1);

  // P3: "Nodes of N2 are not adjacent to any nodes of C except to only one of the
  // border nodes (m or m+1)" -- and that one is the attachment point. Vacuous when
  // there is no border.
  if (hasBorder) {
    CHECK(ctx.attachmentPoint == C[ctx.m] || ctx.attachmentPoint == C[ctx.m + 1],
          "P3: the attachment point %d is not a border node (%d or %d)",
          ctx.attachmentPoint, C[ctx.m], C[ctx.m + 1]);
    CHECK(ctx.freePoint == C[ctx.m] || ctx.freePoint == C[ctx.m + 1],
          "P3: the free point %d is not a border node (%d or %d)", ctx.freePoint,
          C[ctx.m], C[ctx.m + 1]);
    CHECK(ctx.attachmentPoint != ctx.freePoint,
          "P3: the attachment and free points are the same node %d",
          ctx.attachmentPoint);
    // N2 = the vertices strictly inside the border interval, whose ends are the two border
    // nodes. Which of them comes first ON THE SPINE depends on the direction the cycle is
    // read in (p.61's right-to-left reading), so bound the scan by rank rather than
    // assuming C[m] precedes C[m+1].
    const int r0 = B.spine.rank(C[ctx.m]), r1 = B.spine.rank(C[ctx.m + 1]);
    const int loR = min(r0, r1), hiR = max(r0, r1);
    const set<int> onC(C.begin(), C.end());
    for (int v : B.spine.seq) {
      const int rv = B.spine.rank(v);
      if (rv <= loR || rv >= hiR) continue;
      CHECK(!onC.count(v), "P3: node %d of C lies inside the border interval", v);
      for (Vertex* nbv : B.g.vertices[v]->neighbors()) {
        const int w = nbv->index;
        if (!onC.count(w)) continue;
        CHECK(w == ctx.attachmentPoint,
              "P3 violated: vertex %d of N2 is adjacent to node %d of C, but N2 may "
              "only reach the attachment point %d",
              v, w, ctx.attachmentPoint);
      }
    }
  }

  // P4: "Among the edges connecting nodes of C, only the edges incident to the leader
  // are colored in L. All of them, except possibly for the edge (1,p), have the same
  // color, called the leader's color c0."
  const int leader = ctx.leader();
  const int farEnd = ctx.farEnd();
  for (int i = 0; i < p; i++)
    for (int j = i + 1; j < p; j++) {
      const int u = C[i], w = C[j];
      auto pg = B.page.find(make_pair(min(u, w), max(u, w)));
      if (pg == B.page.end()) continue;  // uncoloured, as P4 permits
      // P4 admits NO exception here: among C's nodes, only leader-incident edges may
      // carry a colour on entry. A K_j inherits exactly one coloured edge from its
      // parent's Step 1a -- the chord that cut it off (p.57: "the only shared edges among
      // the new cycles are short edges of K which are colored in Step 1a") -- and that
      // chord joins K_j's first and last nodes, so it IS the long edge (1,p) and is
      // leader-incident. Nothing else needs permitting.
      CHECK(u == leader || w == leader,
            "P4 violated: edge (%d,%d) joins two nodes of C, neither of them the leader "
            "%d, yet it is already coloured %d", u, w, leader, pg->second);
      // "All of them, EXCEPT POSSIBLY FOR THE EDGE (1,p), have the same color". The
      // exemption is about the colour, not about membership: the long edge is still
      // leader-incident and still checked above.
      if (u == farEnd || w == farEnd) continue;
      CHECK(pg->second == ctx.c0,
            "P4 violated: leader-incident edge (%d,%d) has colour %d, not the "
            "leader's colour c0=%d", u, w, pg->second, ctx.c0);
    }

  checkP5andP6(B, ctx);
}

// Step 1a, Case 1: v_s is the leader, or v_s dominates no blocks. Covers the
// top-level call (m == p, no border) and chordless recursion. Lays out the
// level-1 inner graph H of K == C and colors its edges, then returns the child
// cycles to expand (nontrivial-block cycles; chord cycles Kj are none here).
// True if the first inner node `a` satisfies Yannakakis' convenient assumption
// (Y1989 §2 p.39), which is EXACTLY two clauses:
//   (1) `a` belongs to only one block, and
//   (2) that block is seen by v1 = K.front().
// When it fails, a fictitious first inner node is added.

// There is deliberately no third clause constraining `a`'s own outer
// neighbourhood: Lemma 1(2) constrains the leader against v_f/v_l, the
// first/last outer nodes adjacent to the OTHER block vertices u_1..u_t, not
// against `a`'s own neighbourhood. Adding such a clause is both stronger than
// the paper and about the wrong pair, and forces needless augmentation.
static bool firstInnerNodeIsClean(const PlanarGraph& g, const TwoLevelAnalysis& an,
                                  const vector<int>& K) {
  int a = an.firstInnerNode;
  if (a < 0) return true;  // no inner nodes

  // (1) `a` belongs to exactly one block. Located directly in the block list, not
  // via blockOfVertex: this predicate must be decidable on a RAW analysis, before
  // anything is rooted or assigned, since the augmentation it gates is a
  // precondition of the rooting (Y1989 p.39).
  int owner = -1, cnt = 0;
  for (int b = 0; b < (int)an.blocks.size(); b++) {
    const vector<int>& vs = an.blocks[b].vertices;
    if (find(vs.begin(), vs.end(), a) != vs.end()) { owner = b; cnt++; }
  }
  if (cnt != 1) return false;  // a is a cutpoint (belongs to > 1 block)

  // (2) that block is seen by v1
  int v1 = K.front();
  const Block& blk = an.blocks[owner];
  // Every block from biconnectedComponents carries its edges; a 1-vertex
  // degenerate block has no edge and cannot be "seen" at all.
  CHECK(!blk.edges.empty() || blk.vertices.size() == 1,
        "block %d has %d vertices but no edges", owner,
        (int)blk.vertices.size());
  for (auto& e : blk.edges)
    if (sees(g, v1, e.first, e.second)) return true;
  return false;
}

// Analyse the interior of `K`, augmenting first if Y1989 p.39's assumption about
// the first inner node fails. This is the ONLY way the construction should obtain
// a rooted analysis: the augmentation is a precondition of the rooting, so it has
// to happen between stage 1 and stage 2, and `analyzeTwoLevel` asserts as much.

// The fictitious node a' sits inside the triangle (v1, a, vk) and inherits a's
// level, so it is at the same level as a with respect to this cycle. After the
// insertion a' is the new first inner node, lying in the single trivial block
// (a,a'), which v1 sees.
static TwoLevelAnalysis analyzeTwoLevelAugmented(Builder& B,
                                                 const vector<int>& K) {
  TwoLevelAnalysis raw = analyzeTwoLevelRaw(B.g, K, B.level);
  if (raw.firstInnerNode >= 0 && !firstInnerNodeIsClean(B.g, raw, K)) {
    int v1 = K.front(), vk = K.back(), aNode = raw.firstInnerNode;
    // addFictitiousInner already grows `level` and gives a' the level of a.
    int fict = B.addFictitiousInner(v1, aNode, vk);
    raw = analyzeTwoLevelRaw(B.g, K, B.level);
    LOG_IF(B.verbose >= 3,
           "augmented: a=%d -> a'=%d, new first inner node=%d, #blocks=%d", aNode,
           fict, raw.firstInnerNode, (int)raw.blocks.size());
    CHECK(firstInnerNodeIsClean(B.g, raw, K),
          "augmentation did not clean the first inner node (a=%d, a'=%d, new "
          "fin=%d)", aNode, fict, raw.firstInnerNode);
  }
  return analyzeTwoLevel(B.g, K, B.level);
}

// p.52: "Let m be the turning point of C as in property P2. If m != p, then there is a
// unique short edge (v_s, v_{s+1}) of K that crosses over the border, i.e. with
// v_s <= m < m+1 <= v_{s+1}; s = 1 is a possibility. If m = p, let v_s be the last node
// of K."

// Note the comparison is by POSITION IN C, not by index into K: m need not be a node of
// K at all (it can lie on a chord cycle), which is why `ctx.m` indexes `ctx.nodes`.
// Returns the index of v_s in K.
static int borderCrossingEdgeOfK(const CycleContext& ctx, const vector<int>& K,
                                 const map<int, int>& posInC) {
  const int p = (int)ctx.nodes.size();
  const int klen = (int)K.size();
  // All indices here are LOGICAL: C is logical by CycleContext's contract, and Step 1
  // numbers K from the leader ("denote the nodes of K as u_1 = 1, u_2,..., u_k = p"), so
  // `posInC` and `ctx.m` are directly comparable and no direction test is needed.

  // "If m = p, let v_s be the last node of K" -- m == p is P2's no-border encoding.
  if (ctx.m >= p - 1) return klen - 1;
  for (int i = 0; i + 1 < klen; i++) {
    const int lo = posInC.at(K[i]), hi = posInC.at(K[i + 1]);
    if (lo <= ctx.m && ctx.m + 1 <= hi) return i;
  }
  ERROR("no short edge of K crosses the border (m=" + to_string(ctx.m) +
        ", p=" + to_string(p) + "), contradicting Y1989 p.52");
}

// Where Case 2 places the nodes assigned to T_R (p.54).
enum class TRPlacement { None, AfterVs, BeforeVs1 };

// ===========================================================================

// Which region of the enclosing cycle an operation belongs to. Case 3 splits the interior
// (p.54, Fig. 9); everything else is one region.
enum class PlacementRegion { Single, RegionI, RegionII };

static const char* placementRegionName(PlacementRegion r) {
  switch (r) {
    case PlacementRegion::Single: return "single";
    case PlacementRegion::RegionI: return "region-I";
    case PlacementRegion::RegionII: return "region-II";
  }
  return "unknown";
}

struct PlacementOp {
  int vertex{-1};
  int reference{-1};          // the already-placed node this is inserted next to
  bool logicallyBefore{true}; // before `reference` in LOGICAL order, or after it
  int block{-1};              // the block the vertex is assigned to
  int dominator{-1};          // the dominator of the group it was laid out in
  PlacementRegion region{PlacementRegion::Single};
  const char* rule{""};       // the paper rule that produced it
};

// Which of p.43's two methods a dominator group is laid out by, and WHY.

// p.43 offers both and lets each dominator choose: "the blocks dominated by v_i are listed one
// after the other in top-down order" (CONSECUTIVE) or "traverse the boundary of the subgraph
// induced by these blocks" (NESTED). Two sentences remove the choice, and one defers it:

//   p.53  the LEADER's group: "For v_1 we use the nested method if c0 != c2, and the consecutive
//         method if c0 == c2."
//   p.54  Case 2's T_R: "We use the nested method to lay out the nodes assigned to these blocks."
//   p.43  every other dominator: arbitrary, so production fixes one and records that it was free.

// The REASON is carried alongside the value because Rule 2 reads the value ("same dominator +
// nested => SAME colour as its father; consecutive => OPPOSITE"), so a group whose method is free
// and one whose method is forced are checkable against different obligations.
enum class GroupMethod { Consecutive, Nested };
enum class MethodBasis {
  LeaderP53,     // p.53's forced choice for the leader's own group
  Case2TRP54,    // p.54's nested T_R
  FreeP43,       // p.43 leaves it open; production's fixed choice
};

static const char* groupMethodName(GroupMethod m) {
  return m == GroupMethod::Nested ? "nested" : "consecutive";
}
static const char* methodBasisName(MethodBasis b) {
  switch (b) {
    case MethodBasis::LeaderP53: return "p.53 leader group";
    case MethodBasis::Case2TRP54: return "p.54 Case 2 T_R";
    case MethodBasis::FreeP43: return "p.43 free choice";
  }
  return "unknown";
}

struct PlacementPlan {
  vector<PlacementOp> operations;
  struct GroupRecord {
    int dominator{-1};
    vector<int> blocks;       // top-down
    GroupMethod method{GroupMethod::Consecutive};
    MethodBasis basis{MethodBasis::FreeP43};
    vector<int> order;        // the emitted vertex order for the whole group
    PlacementRegion region{PlacementRegion::Single};

    bool nested() const { return method == GroupMethod::Nested; }
  };
  vector<GroupRecord> groups;

  // Region II is deliberately ABSENT for a Case 3 plan: p.55 gives it to C''s own invocation, so
  // the parent plan has no method to record for those groups and must not invent one.
  map<int, GroupRecord*> methodOf;

  // Rebuild `methodOf` from `groups`. Called once the groups are complete; it FAILS on a duplicate
  // dominator, since two records for one group are two answers to a question that has one.
  void indexMethods() {
    methodOf.clear();
    for (auto& gr : groups) {
      CHECK(gr.dominator >= 0, "PlacementPlan: a group record has no dominator");
      const bool fresh = methodOf.emplace(gr.dominator, &gr).second;
      CHECK(fresh,
            "PlacementPlan: dominator %d has two group records, so its layout method is "
            "ambiguous -- p.43 gives one method per dominator group", gr.dominator);
    }
  }

  // The recorded method. FAILS when the dominator has no record: there is no default and no
  // fallback, because a missing entry means a consumer is asking about a group this plan did not
  // place (p.55's region II) or that the plan is incomplete -- and guessing either way is how the
  // layout and Rule 2 came to be able to disagree.
  GroupMethod methodFor(int dominator) const {
    auto at = methodOf.find(dominator);
    CHECK(at != methodOf.end(),
          "PlacementPlan: no layout method is recorded for dominator %d. Every group this plan "
          "places has exactly one, and p.55's region II belongs to C''s own invocation rather than "
          "to this plan -- so this is either an incomplete plan or a consumer reaching outside it",
          dominator);
    return at->second->method;
  }
  bool nestedFor(int dominator) const {
    return methodFor(dominator) == GroupMethod::Nested;
  }
};

// Apply a plan. The ONLY function that mutates the spine during placement.
static void applyPlacementPlan(Builder& B, const PlacementPlan& plan, bool descending) {
  const SpineView sv{B, descending};
  for (const auto& op : plan.operations) {
    CHECK(!B.spine.placed(op.vertex),
          "placement: vertex %d is already on the spine, but the plan places it again "
          "(rule %s, block %d)", op.vertex, op.rule, op.block);
    B.ruleTag = op.rule;
    if (op.logicallyBefore) sv.insertLogicallyBefore(op.vertex, op.reference);
    else sv.insertLogicallyAfter(op.vertex, op.reference);
  }
}

// Classify binding edges before assigning their pages.
enum class BindingKind { Back, Forward, Case2Near, Case2Far, CPrimeLevel1 };

static const char* bindingKindName(BindingKind k) {
  switch (k) {
    case BindingKind::Back: return "back";
    case BindingKind::Forward: return "forward";
    case BindingKind::Case2Near: return "case2-near";
    case BindingKind::Case2Far: return "case2-far";
    case BindingKind::CPrimeLevel1: return "cprime-level1";
  }
  return "unknown";
}

struct BindingRecord {
  pair<int, int> edge{-1, -1};   // (min,max), the page-map key
  int outer{-1};                 // the endpoint on K
  int inner{-1};                 // the endpoint in this analysis's inner set
  int block{-1};                 // the block `inner` is assigned to
  BindingKind kind{BindingKind::Back};
  // p.44's forward/back verdict, which is a separate fact from `kind`: Case 2's
  // near/far split is by DISTANCE from the placement endpoint (p.54) and cuts across
  // forward/back, so both are recorded. p.61's level-1 edges have no such verdict.
  bool forward{false};
  bool descending{false};        // the owning cycle's logical direction
  const char* rule{""};

};

struct BindingPlan {
  vector<BindingRecord> records;
};

// Apply a binding plan: the CLASSIFICATION only.

// This assigns no pages. `applyPagePlan` is the only operation that mutates Builder::page.
// Classification precedes page assignment and child-context construction.
static void applyBindingPlan(Builder& B, const BindingPlan& plan) {
  for (const auto& r : plan.records) {
    if (r.kind == BindingKind::CPrimeLevel1) {
      // p.61 treats these as level 1 edges of R, so they are deliberately absent from both
      // the binding-direction map and Lemma 5's set.
      B.firstInnerLevel1Edges.insert(r.edge);
      continue;
    }
    B.noteBindingEdge(r.edge.first, r.edge.second, r.descending);
    if (r.forward) B.noteForwardBinding(r.edge.first, r.edge.second);
  }
}

// (`planBindingPages` is defined with the page plan below, which it needs.)

// Plan page assignments using an effective page map so later rules see earlier decisions.
enum class PageOpKind { Assign, Require };

struct PageOp {
  pair<int, int> edge{-1, -1};
  int page{-1};
  PageOpKind kind{PageOpKind::Assign};
  const char* rule{""};
  const char* pageClass{""};
};

struct PagePlan {
  vector<PageOp> operations;
  // The effective-page map: `Builder::page` as it stood when the plan opened, updated by each
  // planned operation. Reads during planning go through `pageOf`, so a later rule sees an
  // earlier planned colour exactly as it would see an applied one.
  map<pair<int, int>, int> effective;

  void open(const map<pair<int, int>, int>& current) {
    effective = current;
  }
  bool has(int u, int v) const {
    return effective.count(make_pair(min(u, v), max(u, v))) != 0;
  }
  int pageOf(int u, int v) const {
    return effective.at(make_pair(min(u, v), max(u, v)));
  }
  void assign(int u, int v, int page, const char* rule, const char* cls) {
    const auto k = make_pair(min(u, v), max(u, v));
    operations.push_back(PageOp{k, page, PageOpKind::Assign, rule, cls});
    effective[k] = page;
  }
  void require(int u, int v, int page, const char* rule, const char* cls) {
    const auto k = make_pair(min(u, v), max(u, v));
    // Check the effective page immediately, then record the required value in the plan.
    auto at = effective.find(k);
    CHECK(at != effective.end(),
          "PagePlan::require(%d,%d,%d) [%s]: no page is in effect for this edge, so the "
          "requirement checks nothing", u, v, page, rule);
    CHECK(at->second == page,
          "PagePlan::require(%d,%d,%d) [%s]: the effective page is %d. The rule that assigned "
          "it and this one disagree", u, v, page, rule, at->second);
    operations.push_back(PageOp{k, page, PageOpKind::Require, rule, cls});
  }
};

//   p.53  Back     "Back edges to the leader v_1 receive its color c_0; all other back edges get
//                  color c_1."
//   p.53  Forward  the colour opposite the block's own, i.e. the other of {c3,c4}.
//   p.54  Case2Far "Binding edges... to the FURTHEST of v_s, v_{s+1}... receive color c3 or c4
//                  opposite to that of R"
//   p.54  Case2Near "... and binding edges to the CLOSER one receive color c1."
//   p.61  CPrimeLevel1 "All edges from u entering the interval [v_s,v_l] go to other nodes of R,
//                  and they all have the color of the block R."
static void planBindingPages(PagePlan& pp, const TwoLevelAnalysis& a, const BindingPlan& bplan,
                             const vector<int>& blockColor, const vector<int>& K, int c0, int c1,
                             int c3, int c4, int R) {
  for (const auto& r : bplan.records) {
    const int blkColour = blockColor[r.block];
    const int oppositeBlock = (blkColour == c3) ? c4 : c3;
    int page = -1;
    switch (r.kind) {
      case BindingKind::Forward:      page = oppositeBlock; break;
      case BindingKind::Back:         page = (r.outer == K.front()) ? c0 : c1; break;
      case BindingKind::Case2Far:     page = (blockColor[R] == c3) ? c4 : c3; break;
      case BindingKind::Case2Near:    page = c1; break;
      case BindingKind::CPrimeLevel1: page = blockColor[a.rootBlock]; break;
    }
    pp.assign(r.edge.first, r.edge.second, page, r.rule,
              r.kind == BindingKind::CPrimeLevel1 ? "cprime-omitted-first-inner"
                                                 : "binding-edge");
  }
}

// Apply a page plan. The ONLY function that mutates `Builder::page` during Step 1a.
static void applyPagePlan(Builder& B, const PagePlan& plan) {
  for (const auto& op : plan.operations) {
    B.ruleTag = op.rule;
    if (op.kind == PageOpKind::Assign) B.assignPage(op.edge.first, op.edge.second, op.page);
    else B.requirePage(op.edge.first, op.edge.second, op.page);
  }
}

// Step 1a. `R` is -1 in Case 1; in Case 2 it is the highest block dominated by v_s, whose
// subtree T_R is laid out by the nested method at `trPlace` instead of by the Case 1 rule.
// The properties that hold of a WHOLE Step 1a, checked once after every call it made -- one
// in Cases 1 and 2, two in Case 3 (T' and C'). Both are about the combined result:

//   Lemma 5 (p.45) is unconditional -- "There is no conflict between any pair of forward
//   binding edges" -- so a region I forward binding edge must not conflict with a region II
//   one either. Checking each call on its own would let exactly that pair through.

//   §D transfers Theorem 1 to the two-level graph of K, which spans both regions.
static void checkStep1aOutput(const Builder& B, const TwoLevelAnalysis& a,
                              const vector<int>& K, const GcDecomposition& gc,
                              const vector<int>& C, int c1, int c2, int m) {
  map<int, int> posInC;
  for (int i = 0; i < (int)C.size(); i++) posInC[C[i]] = i;
  const int cPrimeLeader = B.cPrimeNodesHere.empty() ? -1 : B.cPrimeNodesHere.front();
  const int cPrimeFarEnd = B.cPrimeNodesHere.empty() ? -1 : B.cPrimeNodesHere.back();
  const set<int> cPrimeNodes(B.cPrimeNodesHere.begin(), B.cPrimeNodesHere.end());
  // `forwardBindingHere` is recorded by whichever rule coloured each edge, so a site that
  // forgets `noteForwardBinding` would silently shrink Lemma 5's edge set. Recompute the set
  // from the finished layout, by p.44's definition -- "a binding edge (v_i, u) is a back edge
  // if v_i comes before u in the layout; otherwise, it is forward" -- and require equality.

  // "Before in the layout" is logical order, which for a cycle read right-to-left is the
  // reverse of spine order; the direction is per-cycle, so it is taken from the recorded
  // classification of the OWNING instance rather than re-derived here: this check compares
  // the two ways of naming the same set, and needs only the set membership to agree.
  {
    const set<int> onK(K.begin(), K.end());
    const set<int> inner(a.inner.begin(), a.inner.end());
    for (const auto& e : B.colouredHere) {
      const bool aOnK = onK.count(e.first) != 0, bOnK = onK.count(e.second) != 0;
      const bool aIn = inner.count(e.first) != 0, bIn = inner.count(e.second) != 0;
      const bool isBinding = (aOnK && bIn) || (bOnK && aIn);
      if (!isBinding) continue;
      const int outerV = aOnK ? e.first : e.second;
      const int innerV = aOnK ? e.second : e.first;
      // p.44: forward iff the INNER node precedes the outer one in the layout. `bindDir`
      // records the logical direction of the instance that coloured this edge, so this
      // reproduces the classification from the layout alone.
      // p.61's edges from C''s already-placed first inner node are level 1 edges of R, not
      // binding edges, so they are exempt -- but by NAME, not by turning up missing.
      if (B.firstInnerLevel1Edges.count(e)) continue;
      auto it = B.bindDir.find(e);
      CHECK(it != B.bindDir.end(),
            "binding edge (%d,%d) of K=%s was coloured without recording its cycle's direction, "
            "so Lemma 5's edge set cannot be verified for it", e.first, e.second,
            to_string(K).c_str());
      const bool desc = it->second;
      const int rInner = B.spine.rank(innerV), rOuter = B.spine.rank(outerV);
      const bool innerFirst = desc ? (rInner > rOuter) : (rInner < rOuter);
      CHECK(innerFirst == (B.forwardBindingHere.count(e) != 0),
            "binding edge (%d,%d) of K=%s is %s by p.44's layout test but %s in Lemma 5's "
            "edge set -- a colouring site's forward/back verdict disagrees with the layout",
            e.first, e.second, to_string(K).c_str(), innerFirst ? "forward" : "back",
            B.forwardBindingHere.count(e) ? "present" : "absent");
    }
  }
  // Step 1a's OWNERSHIP. p.53 enumerates exactly what this step colours: "we color the short
  // edges of K", "the binding edges", and "the edges of a (trivial or nontrivial) block B
  // incident to its leader". Everything else in C's interior belongs to a later cycle by O2
  // ("EXPAND will color the edges of C that are not incident to the leader and the edges that
  // lie in the interior of C"). Asserting the exact set catches both an edge coloured here that
  // is not this step's, and -- via the global verifier's completeness check -- one it dropped.
  {
    const set<int> onK(K.begin(), K.end());
    const set<int> inner(a.inner.begin(), a.inner.end());
    set<pair<int, int>> shortEdges;
    for (size_t i = 0; i + 1 < K.size(); i++)
      shortEdges.insert(make_pair(min(K[i], K[i + 1]), max(K[i], K[i + 1])));
    set<pair<int, int>> leaderLevel1;
    for (const auto& blk : a.blocks)
      for (const auto& e : blk.edges)
        if (e.first == blk.leader || e.second == blk.leader)
          leaderLevel1.insert(make_pair(min(e.first, e.second), max(e.first, e.second)));
    for (const auto& e : B.colouredHere) {
      if (shortEdges.count(e) || leaderLevel1.count(e)) continue;
      const bool aOnK = onK.count(e.first) != 0, bOnK = onK.count(e.second) != 0;
      const bool aIn = inner.count(e.first) != 0, bIn = inner.count(e.second) != 0;
      if ((aOnK && bIn) || (bOnK && aIn)) continue;      // a binding edge
      // Case 3 adds one more class, and p.55 states it: the edges from C''s leader v_l to the
      // other nodes of C' ("Give color c1 to these edges (v_l, i)"), which the caller colours
      // so that P4 holds on entry to the C' call. Both endpoints are nodes of C, so they fall
      // outside the three classes above.

      // Membership of `cPrimeLeaderEdges` is not the test -- that set is filled by the very
      // colouring under audit, so accepting on it alone would certify itself. Check the
      // STRUCTURE p.55 describes: one endpoint is v_l, the other another node of C', and the
      // pair is not C''s fictitious long edge.
      if (B.cPrimeLeaderEdges.count(e)) {
        CHECK(cPrimeLeader >= 0,
              "Step 1a of cycle K=%s coloured (%d,%d) as an edge from C''s leader, but this "
              "call has no C'", to_string(K).c_str(), e.first, e.second);
        const int other = (e.first == cPrimeLeader) ? e.second : e.first;
        CHECK(e.first == cPrimeLeader || e.second == cPrimeLeader,
              "Step 1a coloured (%d,%d) as an edge from C''s leader %d, but neither endpoint "
              "is that leader", e.first, e.second, cPrimeLeader);
        CHECK(cPrimeNodes.count(other),
              "Step 1a coloured (%d,%d) as an edge from C''s leader, but %d is not a node of "
              "C'", e.first, e.second, other);
        CHECK(other != cPrimeFarEnd,
              "Step 1a coloured C''s fictitious long edge (%d,%d), which p.55 says does not "
              "exist", e.first, e.second);
        continue;
      }
      // And Step 2's own class, p.53: "We also have to choose a leader for each cycle K_j and
      // COLOR ITS INCIDENT EDGES." Those are chords of C from a K_j's leader to its other
      // nodes, coloured so P4 holds on entry to that K_j. Both endpoints are nodes of C.
      // Likewise structural, not by membership: p.53's K_j leader edges run from a K_j's
      // leader to another node of that same K_j, so both endpoints are nodes of C and they are
      // consecutive-or-chord within one chord cycle's span.
      if (B.kjLeaderEdges.count(e)) {
        CHECK(posInC.count(e.first) && posInC.count(e.second),
              "Step 1a coloured (%d,%d) as a K_j leader edge, but not both endpoints are nodes "
              "of C", e.first, e.second);
        bool inSomeKj = false;
        for (const auto& cc : gc.chordCycles) {
          const int lo = min(posInC.at(e.first), posInC.at(e.second));
          const int hi = max(posInC.at(e.first), posInC.at(e.second));
          if (lo >= cc.first && hi <= cc.second) { inSomeKj = true; break; }
        }
        CHECK(inSomeKj,
              "Step 1a coloured (%d,%d) as a K_j leader edge, but it does not lie within any "
              "chord cycle's span of C", e.first, e.second);
        continue;
      }
      CHECK(false,
            "Step 1a of cycle K=%s coloured edge (%d,%d), which is none of the classes p.53 "
            "and p.55 give it -- not a short edge of K, not a binding edge, not a block's "
            "leader-incident level 1 edge, not an edge from C''s leader",
            to_string(K).c_str(), e.first, e.second);
    }
  }
  const vector<pair<int, int>> fwd(B.forwardBindingHere.begin(),
                                   B.forwardBindingHere.end());
  for (size_t x = 0; x < fwd.size(); x++)
    for (size_t y = x + 1; y < fwd.size(); y++) {
      if (fwd[x].first == fwd[y].first || fwd[x].first == fwd[y].second ||
          fwd[x].second == fwd[y].first || fwd[x].second == fwd[y].second)
        continue;   // sharing an endpoint is not a conflict
      if (!edgesCross(B.spine.rank(fwd[x].first), B.spine.rank(fwd[x].second),
                      B.spine.rank(fwd[y].first), B.spine.rank(fwd[y].second)))
        continue;
      LOG("Lemma 5 context: K=%s", to_string(K).c_str());
      // The block tree and the spine as they stand, so a Lemma 5 failure can be traced by hand
      // from the log alone: the two edges' provenance names the instance that coloured them, and
      // this names the blocks and node order that instance was working from.
      {
        string bs;
        for (int b = 0; b < (int)a.blocks.size(); b++)
          bs += "  blk" + to_string(b) + " lead=" + to_string(a.blocks[b].leader) +
                " dom=" + to_string(a.blocks[b].dominator) +
                " par=" + to_string(a.blocks[b].parent) +
                " V=" + to_string(a.blocks[b].vertices) + "\n";
        LOG("   isCPrime=%d rootBlock=%d firstInner=%d nblocks=%d\n%s", (int)a.isCPrime,
            a.rootBlock, a.firstInnerNode, (int)a.blocks.size(), bs.c_str());
        string sp;
        for (int i = 0; i < 4 * B.nOrig; i++)
          for (int v = 0; v < (int)B.g.vertices.size(); v++)
            if (B.spine.placed(v) && B.spine.rank(v) == i)
              sp += to_string(v) + "@" + to_string(i) + " ";
        LOG("   spine so far: %s", sp.c_str());
      }
      LOG("   forward edge (%d,%d) at ranks %d,%d [%s]", fwd[x].first, fwd[x].second,
          B.spine.rank(fwd[x].first), B.spine.rank(fwd[x].second),
          B.provenance.at(fwd[x]).c_str());
      LOG("   forward edge (%d,%d) at ranks %d,%d [%s]", fwd[y].first, fwd[y].second,
          B.spine.rank(fwd[y].first), B.spine.rank(fwd[y].second),
          B.provenance.at(fwd[y]).c_str());
      // The premise Lemma 5's same-block argument runs on: the clockwise sequence, each
      // endpoint's index in it, and Gamma as POSITIONS along this instance's own cycle. A
      // conflict is only interpretable against those, so dump them here.
      {
        map<int, int> posC;
        for (int i = 0; i < (int)C.size(); i++) posC[C[i]] = i;
        auto describe = [&](const pair<int, int>& e) {
          const int inner = a.blockOfVertex.count(e.first) ? e.first : e.second;
          const int outer = (inner == e.first) ? e.second : e.first;
          const int blkIdx = a.blockOfVertex.count(inner) ? a.blockOfVertex.at(inner) : -1;
          string cwTxt, gammaTxt;
          int idx = -1;
          if (blkIdx >= 0) {
            vector<int> cw(a.blocks[blkIdx].vertices.begin() + 1,
                           a.blocks[blkIdx].vertices.end());
            if (!a.isCPrime) reverse(cw.begin(), cw.end());
            for (int i = 0; i < (int)cw.size(); i++)
              if (cw[i] == inner) idx = i + 1;
            cwTxt = to_string(cw);
            set<int> gs;
            for (Vertex* nb : B.g.vertices[inner]->neighbors())
              if (posC.count(nb->index)) gs.insert(posC.at(nb->index));
            gammaTxt = to_string(vector<int>(gs.begin(), gs.end()));
          }
          LOG("   Lemma 5: edge(%d,%d) inner=%d outer=%d@pos%d blk=%d cwIndex=%d cw=%s "
              "GammaPos=%s", e.first, e.second, inner, outer,
              posC.count(outer) ? posC.at(outer) : -1, blkIdx, idx, cwTxt.c_str(),
              gammaTxt.c_str());
        };
        describe(fwd[x]);
        describe(fwd[y]);
        // Which frame this Lemma 5 check is running in, and the block table it sees. The
        // colouring instance and the checking instance need not be the same cycle, so both
        // have to be named or the numbers cannot be interpreted.
        LOG("   Lemma 5: frame: C=%s K=%s isCPrime=%d rootBlock=%d", to_string(C).c_str(),
            to_string(K).c_str(), (int)a.isCPrime, a.rootBlock);
        for (int bb = 0; bb < (int)a.blocks.size(); bb++) {
          vector<int> cw(a.blocks[bb].vertices.begin() + 1, a.blocks[bb].vertices.end());
          if (!a.isCPrime) reverse(cw.begin(), cw.end());
          string gam;
          for (int v : cw) {
            set<int> gs;
            for (Vertex* nb : B.g.vertices[v]->neighbors())
              if (posC.count(nb->index)) gs.insert(posC.at(nb->index));
            gam += to_string(v) + ":" + to_string(vector<int>(gs.begin(), gs.end())) + "  ";
          }
          LOG("   Lemma 5: blk%d lead=%d dom=%d cw=%s gammaPos= %s", bb, a.blocks[bb].leader,
              a.blocks[bb].dominator, to_string(cw).c_str(), gam.c_str());
        }
        // Lemma 1(2) is the PLANE anchor for the clockwise direction: "v_f sees the edge
        // (u, u_1), and v_l sees the edge (u_t, u)". Report which of the leader's two
        // boundary neighbours the dominator actually sees, since that -- not the store
        // convention -- decides which end is u_1.
        {
          const int inner = a.blockOfVertex.count(fwd[x].first) ? fwd[x].first : fwd[x].second;
          const int blkIdx = a.blockOfVertex.count(inner) ? a.blockOfVertex.at(inner) : -1;
          if (blkIdx >= 0 && a.blocks[blkIdx].vertices.size() >= 3) {
            const Block& blk = a.blocks[blkIdx];
            const int lead = blk.leader;
            const int nb1 = blk.vertices[1];
            const int nbT = blk.vertices.back();
            LOG("   Lemma 5: lemma1(2): leader=%d dom=%d storeNext=%d storeLast=%d "
                "domSees(lead,storeNext)=%d domSees(lead,storeLast)=%d", lead, blk.dominator,
                nb1, nbT, (int)sees(B.g, blk.dominator, lead, nb1),
                (int)sees(B.g, blk.dominator, lead, nbT));
          }
        }
      }
      CHECK(false,
            "Lemma 5 violated: forward binding edges (%d,%d) and (%d,%d) conflict, so the "
            "forward/back classification is wrong for at least one of them",
            fwd[x].first, fwd[x].second, fwd[y].first, fwd[y].second);
    }
  // c1 and c2 are the two pages p.57 puts in place of §2's single colour 1.
  checkTwoLevelIsLegal(B, a, K, {c1, c2}, m);
}

// p.55's two exceptions when the algorithm is applied to C', passed to the Case 1/2 engine
// so that it needs no knowledge of Case 3:

//   "(i) we omit the first inner node u (since it has been already laid out) and (ii) in
//    Rule 1, we give to the root block R color opposite to that of its parent in T."

// `rootBlockColor` is exception (ii): -1 means Rule 1 applies as written (p.53), otherwise
// the root block takes this colour. `alreadyPlaced` is exception (i).
struct CPrimeExceptions {
  int rootBlockColor{-1};
  int alreadyPlaced{-1};
  // Filled in by the engine: the block colours it assigned, so Case 3's second call can read
  // R's parent's colour for exception (ii) without recomputing them.
  vector<int>* blockColourOut{nullptr};

};

static void expandStep1a(Builder& B, const CycleContext& ctx,
                         const GcDecomposition& gc, TwoLevelAnalysis& a, int s_idx,
                         int R, int l_idx, TRPlacement trPlace,
                         vector<CycleContext>& children,
                         const CPrimeExceptions& exc = CPrimeExceptions{}) {
  const vector<int>& K = gc.K;
  const SpineView sv{B, ctx.descending};
  int p = (int)ctx.nodes.size();
  // Same definition as in checkP1toP6: the no-border sentinel sits at whichever end of the
  // array is farthest from the leader.
  const bool hasBorder =
      (ctx.m < p - 1);

  const PlanarGraph& g = B.g;
  B.cycTag = to_string(ctx.nodes) + " m=" + to_string(ctx.m) + " c0=" + to_string(ctx.c0) +
             " c1=" + to_string(ctx.c1) + " c2=" + to_string(ctx.c2);
  // The per-instance records are cleared by the CALLER, in expand(), not here: Case 3 runs
  // this engine twice for one Step 1a -- T' then C' -- and the properties they feed are about
  // the whole of C's Step 1a, so a second call must accumulate rather than reset.

  map<int, int> posInC;
  for (int i = 0; i < p; i++) posInC[ctx.nodes[i]] = i;

  int c0 = ctx.c0, c1 = ctx.c1, c2 = ctx.c2;
  auto [c3, c4] = otherColors(c1, c2);

  // --- Node layout: blocks placed after their dominator v_r, right before ---
  // v_{r+1}. Blocks dominated by v1 (= leader) go right before node 2.
  // Vertices within a block: counterclockwise from the block's leader.
  // Order of blocks with the same dominator: top-down in the block tree.

  // We reproduce the block traversal order used by analyzeTwoLevel's tree.
  // For each dominator, list its blocks top-down (BFS/preorder), and for each
  // block emit its assigned vertices in the block's stored vertex order.

  // Placement reference: the outer node v_{r+1} (successor of the dominator in
  // K). Nodes are inserted right before v_{r+1}. Blocks dominated by the last
  // outer node would have no successor, but Lemma 1 guarantees every block has
  // dominator < last, so v_{r+1} always exists.

  int klen = (int)K.size();
  map<int, int> posInK;
  for (int i = 0; i < klen; i++) posInK[K[i]] = i;

  int nb = (int)a.blocks.size();

  vector<int> blockColor(nb, -1);
  bool c0IsC3orC4 = (c0 != c2);

  // The placement method is stored in the plan and used by both placement and Rule 2. For a shared
  // dominator, nested groups keep the parent's color and consecutive groups use the opposite
  // color.

  PlacementPlan plan;

  // In Case 2, "From the processing of T', a color has been given to the parent of R in
  // the tree T. Associate the opposite color (c3 or c4) with ALL the blocks of T_R (as in
  // Rule 2 of the coloring of blocks)" (p.54). So T_R is monochromatic, not alternating.
  // p.53: R is the highest block dominated by v_s and v_l the last node of K that sees it;
  // T_R (the subtree at R) lies in region II and T' = T - T_R in region I (p.54, Fig. 9).
  // Case 2 is l == s+1 and Case 3 is l > s+1; in Case 1 there is no R.
  const bool caseTwo = (R >= 0 && l_idx == s_idx + 1);
  const bool caseThree = (R >= 0 && l_idx > s_idx + 1);
  const bool hasTR = (R >= 0);
  vector<char> inTR(nb, 0);
  if (hasTR) {
    vector<int> st = {R};
    while (!st.empty()) {
      int b = st.back(); st.pop_back();
      inTR[b] = 1;
      for (int ch : a.blocks[b].children) st.push_back(ch);
    }
    if (caseTwo) {
      // p.54: with l = s+1, T_R's blocks "can only be adjacent to outer nodes between v_s
      // and v_l = v_{s+1}... Thus, they are all dominated by v_s", so T_R is exactly the
      // v_s dominator group and the layout below can treat it as one group.
      for (int b = 0; b < nb; b++)
        if (inTR[b])
          CHECK(a.blocks[b].dominator == K[s_idx],
                "Case 2: block %d of T_R is dominated by %d, not by v_s=%d, contradicting "
                "p.54", b, a.blocks[b].dominator, K[s_idx]);
    } else {
      // p.54: "every block of T_R is dominated by a node v_i with s <= i < l".
      for (int b = 0; b < nb; b++)
        if (inTR[b]) {
          const int di = posInK.at(a.blocks[b].dominator);
          CHECK(di >= s_idx && di < l_idx,
                "Case 3: block %d of T_R has dominator at position %d, outside [s=%d, l=%d)",
                b, di, s_idx, l_idx);
        }
    }
  }

  // Region II is laid out by the BACKWARD dominator (p.55: "we take now the dominator of a
  // block B in region II to be the last node u_i of K (highest i) that sees B"), and Rule 2
  // is stated in terms of the dominator that defines the GROUP a block is laid out in ("if
  // the parent of B has the same dominator v_i and the blocks dominated by v_i are ordered
  // by the nested method (resp. the consecutive method)"). So for a T_R block in Case 3 the
  // relevant dominator is the backward one; using the forward dominator groups it against
  // blocks it is not laid out beside.
  // Case 3's "internal Case 2" needs no machinery here. p.61 -- "If the last node of K that
  // sees a block B of region II is u_{s+1}, then B is seen only by nodes u_s and u_{s+1}; all
  // such blocks are placed next to u_s or u_{s+1} as explained in Case 2" -- describes what
  // C''s OWN dispatch does: expanding C' reaches Case 2 exactly when C''s v_s dominates
  // blocks, and then p.54 applies to it unchanged, with C''s root block as its R.

  // ---- THE PLAN'S METHOD RECORD, built before any colour is assigned. ----------------------

  // One entry per dominator group this call places, each with the paper sentence that fixed it.
  // Rule 2's propagation below reads the method from here, and so does the layout further down, so
  // the two cannot disagree.

  // WHICH GROUPS GET A RECORD: exactly the groups THIS call places.

  // p.55 assigns region II -- both its layout AND its colouring -- to C''s own invocation: "To lay
  // out region II... we want to expand the cycle C'... Regard v_l as the leader of C'", and that
  // invocation runs the ordinary Rule 1/Rule 2 in its own reading, with its own dominators (p.61's
  // backward dominator) and its own root-block override (p.55's exception (ii)). A T_R group's
  // METHOD is therefore not this call's to state: this call never lays that group out, so it has no
  // method for it, and the group's blocks are coloured by the C' invocation rather than here.

  // A parent record for such a group is worse than redundant. The method it would state is measured
  // against the FORWARD dominator grouping, while C' lays the group out against the backward one
  // (p.61), so the two calls group the same blocks differently -- and a record built from the wrong
  // grouping is a wrong answer, not a spare one. Rule 2's traversal below therefore stops at T_R,
  // and `methodFor` is left to fail loudly if any consumer reaches outside this call's plan.
  {
    map<int, vector<int>> byDomForMethod;
    for (int b = 0; b < nb; b++) {
      // p.55: region II belongs to C''s invocation, which states its own methods.
      if (caseThree && inTR[b]) continue;
      byDomForMethod[a.blocks[b].dominator].push_back(b);
    }
    for (const auto& kv : byDomForMethod) {
      PlacementPlan::GroupRecord gr;
      gr.dominator = kv.first;
      gr.blocks = kv.second;
      if (caseTwo && kv.first == K[s_idx]) {
        // p.54: "We use the nested method to lay out the nodes assigned to these blocks."
        gr.method = GroupMethod::Nested;
        gr.basis = MethodBasis::Case2TRP54;
      } else if (kv.first == K.front()) {
        // p.53: "For v_1 we use the nested method if c0 != c2... and the consecutive method if
        // c0 == c2."
        gr.method = c0IsC3orC4 ? GroupMethod::Nested : GroupMethod::Consecutive;
        gr.basis = MethodBasis::LeaderP53;
      } else {
        gr.method = GroupMethod::Consecutive;
        gr.basis = MethodBasis::FreeP43;
      }
      plan.groups.push_back(gr);
    }
    plan.indexMethods();

  }

  // --- Node layout: for each outer node v_r (in K order), place the blocks ---
  // dominated by v_r, right before v_{r+1}, in top-down (preorder) block order,
  // each block's assigned vertices in stored (counterclockwise-from-leader)
  // order. Blocks dominated by the leader go right before node 2 (= K[1]).

  // Build, for each dominator position, its blocks in preorder.
  {
    // preorder index of each block, to sort block groups top-down. The blocks form
    // one tree, so the traversal from the root reaches all of them; a block left at
    // -1 would sort arbitrarily, so that is asserted rather than tolerated.
    vector<int> preIndex(nb, -1);
    {
      int cnt = 0;
      function<void(int)> dfs = [&](int b) {
        preIndex[b] = cnt++;
        for (int ch : a.blocks[b].children) dfs(ch);
      };
      if (nb > 0) dfs(a.rootBlock);
      for (int b = 0; b < nb; b++)
        CHECK(preIndex[b] >= 0,
              "block %d was not reached from the root block %d", b, a.rootBlock);
    }

    // group blocks by dominator
    // Blocks are grouped by dominator; the groups are laid out in the order
    // their dominators appear ALONG THE CYCLE (p.43: "for j = 1..k, the
    // blocks dominated by u_j are embedded right next to u_j"), which is not the
    // order a std::map keyed by vertex index would give.
    map<int, vector<int>> byDom;
    for (int b = 0; b < nb; b++) {
      // In Case 3, T_R is laid out separately below by the reversed rule, so it must not be
      // grouped with T' here -- "The tree T' is processed exactly as in Case 1" (p.54).
      if (caseThree && inTR[b]) continue;
      byDom[a.blocks[b].dominator].push_back(b);
    }
    // Within a group: "in top-down order of T" (p.43) and
    // Y1989's consecutive method ("first the nodes assigned to the highest
    // block, then the nodes assigned to its child"), i.e. parent blocks first.
    for (auto& kv : byDom)
      sort(kv.second.begin(), kv.second.end(),
           [&](int x, int y) { return preIndex[x] < preIndex[y]; });

    vector<int> domOrder;
    for (auto& kv : byDom) domOrder.push_back(kv.first);
    sort(domOrder.begin(), domOrder.end(), [&](int x, int y) {
      CHECK(posInK.count(x) && posInK.count(y),
            "dominator %d or %d is not on the cycle", x, y);
      return posInK.at(x) < posInK.at(y);
    });

    for (int domKey : domOrder) {
      auto& kv = *byDom.find(domKey);
      int dom = kv.first;
      if (caseTwo && dom == K[s_idx]) {
        // Case 2 (p.54): T_R is laid out by the NESTED method -- "We use the nested method
        // to lay out the nodes assigned to these blocks" -- and "the nodes are placed right
        // next to v_s or v_{s+1}" according to the subcase: next to the free point in 2a,
        // right after v_s in 2b, right before v_{s+1} in 2c.
        // The record already exists, with p.54 as its basis; the layout adds the region and the
        // emitted order. Reading the method from it rather than passing `true` here keeps ONE value
        // -- the nested-ness Rule 2 already consumed above is the same one the order is built from.
        PlacementPlan::GroupRecord& gr = *plan.methodOf.at(dom);
        gr.blocks = kv.second;   // p.43's top-down order, established by the layout
        CHECK(gr.basis == MethodBasis::Case2TRP54 && gr.nested(),
              "Case 2: T_R's group (dominator %d) is recorded as %s on the basis of %s, but p.54 "
              "makes it nested", dom, groupMethodName(gr.method), methodBasisName(gr.basis));
        const vector<int> trOrder = blockGroupOrder(a, kv.second, gr.nested());
        gr.region = PlacementRegion::RegionII;
        // "right after v_s" and "right before v_{s+1}" are LOGICAL directions, so both go
        // through the view: for a cycle read right-to-left each is the opposite spine
        // operation. Placing after v_s means the group's first node is adjacent to v_s, so
        // the anchor advances; placing before v_{s+1} keeps one anchor and the group builds
        // up against it, which is what preserves trOrder in the layout.
        if (trPlace == TRPlacement::AfterVs) {
          int anchor = K[s_idx];
          for (int v : trOrder) {
            if (v == exc.alreadyPlaced) continue;  // p.55 exception (i)
            PlacementOp op;
            op.vertex = v;
            op.reference = anchor;
            op.logicallyBefore = false;
            op.block = a.blockOfVertex.count(v) ? a.blockOfVertex.at(v) : -1;
            op.dominator = dom;
            op.region = PlacementRegion::RegionII;
            op.rule = "layoutCase2b";
            plan.operations.push_back(op);
            gr.order.push_back(v);
            anchor = v;
          }
        } else {
          CHECK(trPlace == TRPlacement::BeforeVs1,
                "Case 2 reached with no T_R placement chosen");
          for (int v : trOrder) {
            if (v == exc.alreadyPlaced) continue;  // p.55 exception (i)
            PlacementOp op;
            op.vertex = v;
            op.reference = K[s_idx + 1];
            op.logicallyBefore = true;
            op.block = a.blockOfVertex.count(v) ? a.blockOfVertex.at(v) : -1;
            op.dominator = dom;
            op.region = PlacementRegion::RegionII;
            op.rule = "layoutCase2c";
            plan.operations.push_back(op);
            gr.order.push_back(v);
          }
        }
        continue;
      }
      CHECK(posInK.count(dom), "dominator %d not in K", dom);
      // "The nodes assigned to each block B are placed in the FIRST RESERVED SPACE OF C
      // after the node v_f of K that dominates B; i.e., right before v_{f+1}" (p.53).

      // The reserved spaces are the gaps between consecutive nodes of C (O1), so the
      // successor meant here is the one along C, not along K. p.59 settles it for the
      // case where the two differ -- when (v_f, v_{f+1}) is a chord of C it cuts off a
      // K_j, and of that cycle p.59 says "Step 1a inserted nodes only between N1 and
      // NODE 2", node 2 being the second node of K_j, i.e. of C. Inserting before K's
      // successor instead would drop the group into the middle of K_j's span, which P2
      // then reports as foreign vertices inside K_j.

      // The two coincide whenever C is chordless, which is why this is invisible until
      // chord cycles exist.
      CHECK(posInC.count(dom), "dominator %d is not a node of C", dom);
      // A dominator is a node of K, never one strictly interior to a chord cycle K_j. p.51
      // partitions C's interior into K and the K_j, and p.59 says the intermediate nodes of a
      // K_j "are not adjacent to any nodes which lie inside K" -- so a block of K's interior
      // cannot be dominated by one, and the group always has a reserved space of C to go in.
      // If this fires, the interior computation for K has taken in a vertex belonging to a
      // K_j's interior.
      CHECK(posInK.count(dom),
            "the dominator %d of a block of K's interior is not a node of K = %s (it is at "
            "position %d of C = %s), so it lies strictly inside a chord cycle K_j, which "
            "p.51/p.59 rule out",
            dom, to_string(K).c_str(), posInC.at(dom), to_string(ctx.nodes).c_str());
      const int cpos = posInC.at(dom);
      CHECK(cpos + 1 < p,
            "dominator %d is the last node of C, contradicting Y1989 p.44 (every block "
            "is adjacent to at least two cycle nodes)", dom);
      // p.52: "in the first reserved space of C after the node v_f of K that dominates B;
      // i.e., right before v_{f+1}". v_{f+1} is C's successor of the dominator.

      // The target is C's successor of the dominator, not the first EMPTY gap after it:
      // p.52 names the reserved space "after the node v_f... i.e. right before v_{f+1}",
      // and p.59 confirms a K_j's leader gap legitimately holds the parent's blocks --
      // "Step 1a inserted nodes only between N1 and node 2" (K_1) and "only next to the
      // leader" (K_j, 1 < j < s). Those become the K_j's own N1 under P3.
      int refNode = ctx.nodes[cpos + 1];
      // The whole dominator group in one order, by the method p.53 prescribes for this
      // dominator -- the same predicate Rule 2 reads above.
      // The group record already exists, with its method and the paper sentence that fixed it;
      // the layout fills in the region and the emitted order. `methodOf` points into `groups`, so
      // this is the same record every other consumer reads.
      PlacementPlan::GroupRecord& gr = *plan.methodOf.at(dom);
      // Same membership, and now in p.43's TOP-DOWN (preorder) order, which the layout establishes
      // -- the method record is built before the preorder is known, so it holds the group's members
      // but not their order.
      CHECK(set<int>(gr.blocks.begin(), gr.blocks.end()) ==
                set<int>(kv.second.begin(), kv.second.end()),
            "placement: dominator %d's group was recorded with blocks %s but the layout groups it "
            "as %s", dom, to_string(gr.blocks).c_str(), to_string(kv.second).c_str());
      gr.blocks = kv.second;   // p.43's top-down order
      gr.region = caseThree ? PlacementRegion::RegionI : PlacementRegion::Single;
      // p.52 places the group "in the first reserved space of C after the node v_f of K that
      // dominates B; i.e., right before v_{f+1}" -- a statement about WHICH GAP the group
      // occupies, not a per-node instruction.

      // Inserting every node logically before the same v_{f+1} REVERSES the group: emitting
      // a,b,c that way lands them as c,b,a. That destroys p.45's run, whose order is the whole
      // content of `blockGroupOrder`'s output, and it is not a cosmetic difference -- Lemma 5's
      // same-block argument depends on the run's direction:

      //   p.46: "If a != x, then x and y are two nodes of B other than its leader. The claim
      //   follows from part (1) of Lemma 1."

      // That step needs "x precedes y in the layout" to imply index(x) > index(y), which holds
      // only for p.45's decreasing run u,u_t,...,u_1. Reversed, x before y gives
      // index(x) < index(y), Lemma 1(1) gives Gamma(x) <= Gamma(y), and two forward binding
      // edges of one block interleave on one page.

      // So the anchor WALKS: the first node goes before v_{f+1} and each subsequent node goes
      // after the one just placed, which keeps the group's own order. Both forms put the group
      // in the same gap, so both satisfy p.52's sentence; only this one preserves p.45.

      // Case 2's 2b branch already walks its anchor for the same reason, and says so.

      // The direction of the store is anchored to the plane, not to a convention: §5's alpha
      // "traces the boundary of the inner graph in CLOCKWISE order" (p.65), and reversing the
      // store's tail reproduces alpha from the leader. The store is u,u_t,...,u_1,
      // so emitting it in order preserves p.45's run.
      int anchor = refNode;
      bool firstOfGroup = true;
      for (int v : blockGroupOrder(a, kv.second, gr.nested())) {
        // p.55's exception (i): on C''s call "we omit the first inner node u (since it has
        // been already laid out)".
        if (v == exc.alreadyPlaced) continue;
        PlacementOp op;
        op.vertex = v;
        op.reference = anchor;
        // The first node lands logically before v_{f+1}; the rest chain after their
        // predecessor. For a cycle read right-to-left both are the mirrored spine operation,
        // which `SpineView` handles.
        op.logicallyBefore = firstOfGroup;
        op.block = a.blockOfVertex.count(v) ? a.blockOfVertex.at(v) : -1;
        op.dominator = dom;
        op.region = gr.region;
        op.rule = "layoutCase1";
        plan.operations.push_back(op);
        gr.order.push_back(v);
        anchor = v;
        firstOfGroup = false;
      }
    }

    // ---- Case 3 (p.55): region II, laid out right-to-left. ------------------
    // p.55 says region II's node layout "follow[s] from our description for Cases 1 and 2
    //... remember only that now we proceed right-to-left", but the insertion point is NOT
    // the mirror image of Case 1's. Case 1 places a group "in the first reserved space of C
    // after the node v_f of K that dominates B; i.e., right before v_{f+1}" (p.52) -- before
    // the dominator's SUCCESSOR. p.61 states region II's rule separately and it names the
    // dominator itself: "for i > s+1 the nodes assigned to B are inserted RIGHT BEFORE u_i".

    // So this loop is not the one above with a direction reversed: p.61 states region II's
    // insertion point separately, and it names the dominator itself rather than the
    // dominator's successor.
    // "To lay out region II... Imagine that there is an edge (v_s, v_l) drawn on the plane
    // in region I, and that we want to expand the cycle C' = (v_s, v_{s+1},..., v_l)...
    // Regard v_l (the last node of C') as the leader of C'."

    // p.61 spells out the consequence for the layout: "we take now the dominator of a block
    // B in region II to be the LAST node u_i of K (highest i) that sees B; for i > s+1 the
    // nodes assigned to B are inserted RIGHT BEFORE u_i. If the last node of K that sees a
    // block B of region II is u_{s+1}, then B is seen only by nodes u_s and u_{s+1}; all
    // such blocks are placed next to u_s or u_{s+1} as explained in Case 2."
    // Region II is not laid out here: Case 3 lays it out by expanding C', a second call
    // into this engine, so this call handles only T'.

    {
      // The plan as data, at -verbose=4. A placement defect is a statement about which
      // group emitted what order and where each vertex was anchored, so that is what the
      // trace prints -- not the resulting spine, which is the symptom.
      if (B.verbose >= 4)
        for (const auto& gr : plan.groups) {
          string mapped;
          for (int v : gr.order)
            mapped += to_string(v) + "(b" +
                      (a.blockOfVertex.count(v) ? to_string(a.blockOfVertex.at(v)) : "?") +
                      ") ";
          LOG("GROUP dom=%d nested=%d region=%s blocks=%s desc=%d order=%s", gr.dominator,
              (int)gr.nested(), placementRegionName(gr.region), to_string(gr.blocks).c_str(),
              (int)ctx.descending, mapped.c_str());
        }
      if (B.verbose >= 4)
        for (const auto& op : plan.operations)
          LOG("PLAN %s v=%d ref=%d before=%d blk=%d dom=%d region=%s in C=%s K=%s s=%d",
              op.rule, op.vertex, op.reference, (int)op.logicallyBefore, op.block,
              op.dominator, placementRegionName(op.region), to_string(ctx.nodes).c_str(),
              to_string(K).c_str(), s_idx);
      applyPlacementPlan(B, plan, ctx.descending);
    }
  }

  // assign block colors via a preorder over the tree
  {
    // The blocks form one tree rooted at rootBlock (Y1989 p.39: the inner graph of
    // a chordless K is connected), so seeding the root colours everything. A cycle
    // with no inner vertices has no blocks and no root.
    vector<int> stackB;
    if (nb > 0) {
      // Rule 1, amended (p.53): "If c0 in {c3,c4} (i.e. c0 != c2), then the root block gets
      // color c0; otherwise the choice of the color for the root block is ARBITRARY (c3 or
      // c4)."

      // Where the choice is free, c3 is taken. Any fixed choice satisfies the paper; the
      // construction is deterministic, so it must be a rule rather than left open.

      // p.55's exception (ii) overrides Rule 1 when this is C''s call: "in Rule 1, we give
      // to the root block R color opposite to that of its parent in T."
      blockColor[a.rootBlock] =
          (exc.rootBlockColor >= 0) ? exc.rootBlockColor : (c0IsC3orC4 ? c0 : c3);
      stackB.push_back(a.rootBlock);
    }
    while (!stackB.empty()) {
      int b = stackB.back(); stackB.pop_back();
      for (int ch : a.blocks[b].children) {
        // CASE 3: THE TRAVERSAL STOPS AT T_R. p.55 hands region II to C''s own invocation, and
        // that includes Rule 1 and Rule 2 for its blocks: C' applies its own exception (ii) to R
        // ("in Rule 1, we give to the root block R color opposite to that of its parent in T") and
        // then alternates through region II with p.61's BACKWARD dominators. Colouring those blocks
        // here would answer the same question twice, from a different grouping -- and it is the
        // grouping Rule 2 turns on, so the two answers need not agree.

        // This call therefore computes the colours of T' only. It still computes the colour of R's
        // PARENT, which is a region I block, and that is exactly what the C' invocation needs:
        // `blockColourOut` carries it out, and the caller derives R's override colour from it.
        if (caseThree && inTR[ch]) continue;
        bool sameDom = (a.blocks[ch].dominator == a.blocks[b].dominator);
        int parentColor = blockColor[b];
        int flipped = (parentColor == c3) ? c4 : c3;
        if (ch == R) {
          // p.54's Case 2: R takes the colour opposite its PARENT's. (In Case 3 the same rule is
          // p.55's exception (ii) and belongs to the C' invocation, which is why the guard above
          // has already skipped R there.)
          blockColor[ch] = flipped;
        } else if (caseTwo && inTR[b]) {
          // Case 2 only: "Associate the opposite color (c3 or c4) with ALL the blocks of
          // T_R", so T_R is monochromatic. In Case 3 region II is a full two-level instance
          // in its own right and Rule 2 alternates through it as usual.
          blockColor[ch] = parentColor;
        } else if (!sameDom) {
          blockColor[ch] = flipped;  // different dominator -> opposite
        } else {
          // Rule 2, unamended -- which is also what p.62 requires of region II. Its two
          // edge classes on R's nodes are "(1) forward edges (in the right-to-left
          // direction), and (2) level 1 edges that belong to blocks which are children of
          // R", and both carry "the same color, c3 or c4, opposite to the color of R". A
          // forward edge takes the opposite of its own block (p.44), but a level 1 edge
          // takes the colour OF its block (p.43), so class (2) forces
          // colour(child of R) = opposite(R) -- exactly Rule 2's consecutive branch. The
          // paper derives it the same way: "SINCE THE u_l BLOCKS ARE LAID OUT BY THE
          // CONSECUTIVE METHOD, all these edges have the same color".
          blockColor[ch] = plan.nestedFor(a.blocks[b].dominator) ? parentColor : flipped;
        }
        stackB.push_back(ch);
      }
    }
  }
  if (exc.blockColourOut != nullptr) *exc.blockColourOut = blockColor;

  // Rule 1 and Rule 2, re-checked against the paper's statements rather than against the loop
  // that produced them. The loop above threads several amendments together (p.53's Rule 1 for
  // the root, p.54's monochromatic T_R, p.55's exception (ii)), and a mistake in the threading
  // would otherwise validate itself.

  // Rule 2 (p.43): "If the parent of B has a DIFFERENT dominator, then B gets a color opposite
  // to that of its father. If the parent of B has the SAME dominator v_i, and if the blocks
  // dominated by v_i are ordered by the nested method (resp. the consecutive method), then B
  // gets the same (resp. opposite) color as its father."
  for (int b = 0; b < nb; b++) {
    // Case 3's region II is uncoloured HERE by design -- p.55 gives it to the C' invocation, which
    // runs this same rule in its own frame. Its colours are that call's obligation and are checked
    // on that call, so this loop states nothing about them. `blockColor[b]` is left at -1, and any
    // consumer that reads a T_R colour on this call is a defect the skips below expose rather than
    // hide.
    if (caseThree && inTR[b]) continue;
    CHECK(blockColor[b] == c3 || blockColor[b] == c4,
          "block %d has colour %d, which is neither c3=%d nor c4=%d", b, blockColor[b], c3,
          c4);
    const int par = a.blocks[b].parent;
    if (par < 0) {
      // Rule 1, as amended on p.53: "If c0 in {c3,c4} then the root block gets color c0;
      // otherwise the choice... is arbitrary." p.55's exception (ii) overrides it on C''s
      // call, and the caller supplies that colour, so only the unamended case is checkable.
      if (exc.rootBlockColor < 0 && c0IsC3orC4)
        CHECK(blockColor[b] == c0,
              "Rule 1 violated: the root block %d has colour %d, but c0=%d is one of c3/c4 so "
              "p.53 requires the root to take c0", b, blockColor[b], c0);
      continue;
    }
    // p.54 amends Rule 2 for Case 2's T_R: "Associate the opposite color with ALL the blocks
    // of T_R", so the subtree is monochromatic and Rule 2 does not apply within it.
    if (caseTwo && inTR[b] && inTR[par]) {
      CHECK(blockColor[b] == blockColor[par],
            "p.54 violated: blocks %d and %d are both in Case 2's T_R, which is monochromatic, "
            "but their colours are %d and %d", b, par, blockColor[b], blockColor[par]);
      continue;
    }
    if (b == R) continue;   // p.54/p.55 fix R's colour relative to its parent's, checked there
    const bool sameDom = (a.blocks[b].dominator == a.blocks[par].dominator);
    const bool wantSame = sameDom && plan.nestedFor(a.blocks[par].dominator);
    CHECK((blockColor[b] == blockColor[par]) == wantSame,
          "Rule 2 violated: block %d (dominator %d) and its parent %d (dominator %d) have "
          "colours %d and %d, but the %s case of p.43's Rule 2 requires them %s", b,
          a.blocks[b].dominator, par, a.blocks[par].dominator, blockColor[b], blockColor[par],
          sameDom ? (wantSame ? "same-dominator nested" : "same-dominator consecutive")
                  : "different-dominator",
          wantSame ? "equal" : "opposite");
  }

  if (!caseTwo && !caseThree && s_idx > 0 && hasBorder) {
    for (int b = 0; b < nb; b++)
      CHECK(a.blocks[b].dominator != K[s_idx],
            "Case 1 with s=%d: block %d is dominated by v_s=%d, which p.52 excludes from "
            "Case 1", s_idx, b, K[s_idx]);
  }
  PagePlan pp;
  pp.open(B.page);
  // p.53: "The edge (v_1,v_2) has already been colored c0. All other edges before the
  // border, i.e. edges (v_j, v_{j+1}) with j < s, receive color c2. Edges (v_j, v_{j+1})
  // after the border (i.e. j > s) receive color c1. If s != 1, the edge (v_s, v_{s+1})
  // that crosses the border receives color c3."
  // Which short edge is "(v_1,v_2)" -- the one already coloured c0 -- depends on which end
  // the leader occupies: the first pair normally, the last pair when the cycle is read
  // right-to-left from a leader at the far end (p.55/p.61).
  // "(v_1,v_2)" is the pair at logical positions 1 and 2, and Step 1 numbers K from the
  // leader, so it is always K's first pair.
  const int preColouredPair = 0;
  for (int i = 0; i + 1 < klen; i++) {
    int u = K[i], w = K[i + 1];
    if (i == preColouredPair) {
      // P4 makes every coloured edge among C's nodes leader-incident, so this is the
      // only such short edge, and the caller owns it.
      pp.require(u, w, c0, "shortEdgeOfK", "short-edge-of-K");
      continue;
    }
    // In Case 3 the short edges from v_s to v_l are K''s, not K's: p.55 says "the edge of K'
    // that crosses the border is (v_s, v_{s+1})", and T''s own processing covers only "the
    // part of the layout outside the interval (v_s, v_l)" (p.54). C''s call colours them.
    if (caseThree && i >= s_idx && i < l_idx) continue;
    int col = (i < s_idx) ? c2 : (i == s_idx ? c3 : c1);
    // p.54: "The edge (v_s, v_{s+1}) receives color c3 or c4 OPPOSITE to that assigned to
    // block R." In Case 1 there is no R and p.53's plain c3 applies.

    // Case 3 reaches the same rule through C'. p.55: the edge of K' that crosses the
    // border is (v_s, v_{s+1}), and "if we apply the algorithm to C' we will arrive at
    // Case 1 or Case 2". C' is read right-to-left from v_l, so its own "v_s" is v_{s+1};
    // it lands in Case 2 exactly when v_{s+1} dominates blocks in that reading, which is
    // what `internalR` records. Then p.54's rule applies with C''s root block in place
    // of R. When C' lands in Case 1 instead, p.53's plain c3 stands.
    const int borderR = caseTwo ? R : -1;
    if (i == s_idx && borderR >= 0)
      col = (blockColor[borderR] == c3) ? c4 : c3;
    // A short edge this cycle SHARES with its parent's K was already coloured IN THE
    // PARENT'S Step 1a, and p.57 makes that the authoritative assignment: "the only shared
    // edges among the new cycles are short edges of K which are colored in Step 1a". The
    // parent colours it once, for all the new cycles that share it, so this call must not
    // recolour it by its own s -- the two cycles measure "before" and "after the border"
    // against different borders, so their rules genuinely disagree on it.

    // No other short edge of K can already be coloured: P4 admits only the leader-incident
    // edges of C, and `preColouredPair` above consumes the one such short edge. So `assignPage`
    // owns it outright and reports any second claimant itself, rather than this site inferring
    // ownership from the page it finds.
    pp.assign(u, w, col, "shortEdgeOfK", "short-edge-of-K");
  }

  // Binding + level-1 edges.
  // "A binding edge is forward if the inner vertex PRECEDES the outer vertex" (BBKR §2.3,
  // restating p.43) -- precedes IN THE LAYOUT, which is the paper's logical order. Using raw
  // spine order instead inverts forward and back for every descending cycle, which sends a
  // back edge to the leader to c1 rather than c0 and produces a cross-level collision.
  auto before = [&](int x, int y) { return sv.precedesLogically(x, y); };

  BindingPlan bplan;
  {
  for (int u : a.inner) {
    int b = a.blockOfVertex.at(u);
    for (Vertex* nbv : g.vertices[u]->neighbors()) {
      int w = nbv->index;
      auto keyw = posInK.find(w);
      if (keyw == posInK.end()) continue;  // not a binding edge to this cycle
      BindingRecord rec;
      rec.edge = make_pair(min(u, w), max(u, w));
      rec.inner = u;
      rec.outer = w;
      rec.block = b;
      rec.descending = ctx.descending;
      // The group p.61 routes into Case 2 takes NO separate binding rule. p.54's
      // closer/further rule belongs to Case 2's T_R, whose blocks are monochromatic and
      // whose two cycle nodes are v_s and v_{s+1}; this group is an ordinary consecutive
      // group of the simulated C' instance, so p.55's import governs it -- "the coloring of
      // edges... follow from our description for Cases 1 and 2; remember only that now we
      // proceed right-to-left" -- which is the mirrored forward/back rule just below. Its
      // blocks are also seen by u_s and u_{s+1} only (p.61), so the mirrored rule sends the
      // edge to u_{s+1} and the edge to u_s to different colours, as p.54 intends.
      // In Case 3 the binding edges of region II belong to C''s call, which colours them by
      // the ordinary Cases 1/2 rules in C''s own reading (p.55). Skip them here -- both those
      // of T_R's own vertices, and those of R's leader u that enter region II: u is assigned
      // to R's PARENT in T (region I), but p.61 puts its edges into [v_s,v_l] on the other
      // side of the split -- "All edges from u entering the interval [v_s,v_l] go to other
      // nodes of R".
      if (caseThree && inTR[b]) { continue; }
      if (caseThree && u == a.blocks[R].leader) {
        const int wpos = posInK.count(w) ? posInK.at(w) : -1;
        if (wpos >= s_idx && wpos <= l_idx) {
          continue;
        }
      }
      if (caseTwo && inTR[b]) {
        // p.54: "Binding edges from the inner nodes assigned to the blocks of T_R to the
        // FURTHEST of v_s, v_{s+1} (e.g. the attachment point in Case 2a) receive color
        // c3 or c4 opposite to that of R, and binding edges to the CLOSER one receive
        // color c1."

        // T_R's nodes are adjacent only to v_s and v_{s+1} (p.54), so "furthest" and
        // "closer" are measured from where the group was placed: in 2b it sits right
        // after v_s, so v_{s+1} is the furthest; in 2c the reverse.
        const int furthest =
            (trPlace == TRPlacement::AfterVs) ? K[s_idx + 1] : K[s_idx];
        CHECK(w == K[s_idx] || w == K[s_idx + 1],
              "Case 2: vertex %d of T_R binds to cycle node %d, which is neither v_s=%d "
              "nor v_{s+1}=%d, contradicting p.54", u, w, K[s_idx], K[s_idx + 1]);
        rec.kind = (w == furthest) ? BindingKind::Case2Far : BindingKind::Case2Near;
        rec.rule = "case2Binding";
        // p.54 assigns these colours by FURTHEST/CLOSER, which is not p.44's forward/back
        // partition -- the furthest anchor's edges need not be the forward ones. Lemma 5 is
        // about forward edges as p.44 defines them, so classify by the layout test here too.
        rec.forward = before(u, w);
        bplan.records.push_back(rec);
        continue;
      }
      // p.61 fixes the edges of the already-placed first inner node u on C''s call, and they
      // are not ordinary binding edges: u sits outside [v_s,v_l] instead of "right before
      // v_l... as it would if C' was expanded normally", and "All edges from u entering the
      // interval [v_s,v_l] go to other nodes of R, and they all have THE COLOR OF THE BLOCK
      // R". R is this instance's root block, so that colour is its own.
      if (u == exc.alreadyPlaced) {
        rec.kind = BindingKind::CPrimeLevel1;
        rec.rule = "cPrimeFirstInnerEdge";
        // Not a binding edge in p.44's sense -- p.61 treats it as a level 1 edge of R -- so it
        // is deliberately absent from both the binding-direction map and Lemma 5's set.
        bplan.records.push_back(rec);
        continue;
      }
      // binding edge (u inner, w outer)
      rec.forward = before(u, w);   // inner precedes outer => forward
      if (rec.forward) {
        rec.kind = BindingKind::Forward;
        rec.rule = "forwardBinding";
      } else {
        // p.53: "Back edges to the leader v_1 receive its color c_0; all other back
        // edges get color c_1."
        rec.kind = BindingKind::Back;
        rec.rule = "backBinding";
      }
      bplan.records.push_back(rec);
    }
  }

  {

    if (B.verbose >= 4)
      for (const auto& r : bplan.records)
        LOG("BIND %s (%d,%d) inner=%d outer=%d blk=%d kind=%s fwd=%d desc=%d", r.rule,
            r.edge.first, r.edge.second, r.inner, r.outer, r.block, bindingKindName(r.kind),
            (int)r.forward, (int)r.descending);
    applyBindingPlan(B, bplan);
    planBindingPages(pp, a, bplan, blockColor, K, c0, c1, c3, c4, R);
  }
  }
  // Level-1 edges. §3 colours FEWER of these than §2 does. p.43's two-level rule is
  // "every level 1 edge gets the color of its block", but Step 1a (p.53) narrows it to
  // the leader-incident ones: "We color the edges of a (trivial or nontrivial) block B
  // incident to its leader as follows. If B is dominated by v_1 and c0 in {c3,c4}, then
  // we give them color c1; in all other cases... we give them the color of the block."

  // The remaining edges of a nontrivial block are the short edges and chords of the
  // cycle bounding it, and O2 makes them that cycle's own responsibility: "EXPAND will
  // color the edges of C that are not incident to the leader and the edges that lie in
  // the interior of C". Colouring them here instead would both break P4 on entry to the
  // child and take the child's c1/c2 decision away from it.

  // A trivial block is a single edge incident to its leader, so it is fully coloured
  // here; an isolated-vertex block has no edges at all.
  for (int b = 0; b < nb; b++) {
    // In Case 3 the level 1 edges of region II belong to C''s call, as its own blocks'.
    if (caseThree && inTR[b]) continue;
    const Block& blk = a.blocks[b];
    const bool domByLeader = (blk.dominator == K.front());
    int leaderColour = (domByLeader && c0IsC3orC4) ? c1 : blockColor[b];
    // CASE 2 only: "The leader's color and the color of the long edge for the cycles bounding
    // the blocks of region II is the color of R" (STOC 1986, p.107). That sentence sits inside
    // the 1986 abstract's "Case2. l = s+1" paragraph, bounded below by Case 2's own K_s clause,
    // so it is not a Case 3 rule. In Case 2 T_R is monochromatic (p.54), so "the colour of R"
    // and "the colour of the block" agree and this is a restatement.

    // In CASE 3 Rule 2 alternates through T_R, and applying it there put a child's leader edges
    // on R's own page -- where they cross the edges from R's leader, which p.61 puts on exactly
    // that page ("All edges from u entering the interval [v_s,v_l] go to other nodes of R, and
    // they all have the color of the block R").
    if (caseTwo && inTR[b]) leaderColour = blockColor[R];
    // No Case 3 override here. p.62's clause (2) -- the level 1 edges of R's children take
    // "the same color... opposite to the color of R" -- is discharged by Rule 2 giving those
    // children opposite(R) in the first place, so "the colour of the block" already IS
    // opposite(R). Overriding the colour here instead would state the same rule twice, and
    // would be wrong for a grandchild, whose level 1 edges Rule 2 flips back.
    for (auto& e : blk.edges)
      if (e.first == blk.leader || e.second == blk.leader)
        pp.assign(e.first, e.second, leaderColour, "blkLeaderEdge", "block-leader-level1");
  }

  // Apply the coloring decisions before constructing child contexts.
  {
    if (B.verbose >= 4)
      for (const auto& op : pp.operations)
        LOG("PAGE %s (%d,%d) pg=%d kind=%s class=%s", op.rule, op.edge.first, op.edge.second,
            op.page, op.kind == PageOpKind::Assign ? "assign" : "require", op.pageClass);
    applyPagePlan(B, pp);
  }

  // §D: the two-level subproblem Step 1a just solved must be legal on this instance's
  // four roles. p.57: "the node layout part of the algorithm is identical to that of
  // Section 2... where colors c3 and c4 are used in place of colors 2 and 3 there, and
  // colors c1 and c2 are used in place of color 1 there." So §2's Theorem 1 applies with
  // colour 1 split in two, and the roles are exactly {c1,c2,c3,c4}.

  // Run BEFORE the recursion, so a failure names the cycle whose Step 1a produced it
  // rather than surfacing many levels deeper in the global verifier.
  // Lemma 4, as p.60 restates it: "The only possible child of B that is dominated by v_r has
  // u_q as its leader." u_q is the block's turning point. If a same-dominator child's leader is
  // some other node, the block tree or the turning point is wrong -- and the child's level 1
  // edges then land on a node p.62 does not account for.
  for (int b = 0; b < nb; b++) {
    const int par = a.blocks[b].parent;
    if (par < 0) continue;
    if (a.blocks[b].dominator != a.blocks[par].dominator) continue;
    if ((int)a.blocks[par].vertices.size() < 2) continue;   // isolated vertex: no u_q
    // u_q is computed from THIS analysis's dominator. It is deliberately not cached on the
    // block: a block reachable from two cycles gets a different dominator in each analysis, so
    // one stored value is wrong for at least one of them.
    vector<int> pcw;
    const int pq = lemma4UqIndex(B.g, a.blocks[par], a.blocks[par].dominator, a.isCPrime, &pcw);
    CHECK(pq >= 0, "no node of block %d is adjacent to its dominator %d", par,
          a.blocks[par].dominator);
    const int parUq = pcw[pq];
    CHECK(a.blocks[b].leader == parUq,
          "Lemma 4 violated: block %d shares dominator %d with its parent %d, so its leader "
          "must be the parent's u_q=%d, but it is %d",
          b, a.blocks[b].dominator, par, parUq, a.blocks[b].leader);
  }
  // p.54: "all nodes assigned to blocks of T' (including the leader u of R) are laid out in the
  // intervals (v_1,v_s), (v_l,v_k)" while "the nodes assigned to blocks of T_R will be laid out
  // in the interval (v_s,v_l)". So in Case 3 the two trees occupy disjoint stretches of spine,
  // separated by v_s and v_l. Checked here, where a violation names the cycle whose Step 1a did
  // it; the region I/II boundary is what the §D crossings below straddle.
  if (caseThree && R >= 0) {
    const int rs = B.spine.rank(K[s_idx]), rl = B.spine.rank(K[l_idx]);
    const int lo = min(rs, rl), hi = max(rs, rl);
    for (int b = 0; b < nb; b++)
      for (int v : a.blocks[b].vertices) {
        if (a.blockOfVertex.at(v) != b) continue;   // only vertices assigned to b
        if (!B.spine.placed(v)) continue;
        const int rv = B.spine.rank(v);
        const bool inside = (rv > lo && rv < hi);
        if (inTR[b] && b != R) {
          CHECK(inside,
                "p.54 violated: vertex %d of T_R block %d sits at rank %d, outside region II's "
                "span [%d,%d] between v_s=%d and v_l=%d",
                v, b, rv, lo, hi, K[s_idx], K[l_idx]);
        } else if (!inTR[b]) {
          CHECK(!inside,
                "p.54 violated: vertex %d of T' block %d sits at rank %d, inside region II's "
                "span [%d,%d] between v_s=%d and v_l=%d",
                v, b, rv, lo, hi, K[s_idx], K[l_idx]);
        }
      }
  }
  // Lemma 5 and §D are checked once per Step 1a by `checkStep1aOutput`, which the caller runs
  // after every call this step made -- in Case 3 that is both T' and C', and the properties
  // are about the combined result.

  // --- Step 1b: the cycles bounding nontrivial blocks. ---------------------
  // p.53: "The leader of a cycle bounding a nontrivial block is the leader of the
  // block." Its leader-incident edges were coloured just above, which is what makes P4
  // hold on entry to the child, and their colour is the child's c0.

  // p.60 fixes the rest of the child's state:
  //   turning point  = u_q (Lemma 4), and the attachment point is u_q as well;
  //   first colour   = "c3 or c4, opposite to the color of B";
  //   second colour  = c1, "or c0 if B is dominated by v_1".
  for (int b = 0; b < nb; b++) {
    const Block& blk = a.blocks[b];
    if ((int)blk.vertices.size() < 3) continue;  // trivial: bounds no cycle
    const bool domByLeader = (blk.dominator == K.front());
    const int leaderColour =
        (domByLeader && c0IsC3orC4) ? c1 : blockColor[b];

    // In Case 3 the block cycles of region II are built by C''s own call, from the ordinary
    // Case 1/2 rules applied in C''s reading (p.55). This call owns only T'.
    if (caseThree && inTR[b]) continue;

    CycleContext child;
    child.origin = "step1bBlock";
    // A block cycle is one peeling level deeper (§4's "the new cycles of Step 1b have
    // nodes at level i+1 of G"), and it closes on a real edge of G.
    child.cyclePath = ctx.cyclePath + "/blk" + to_string(b);
    child.peelDepth = ctx.peelDepth + 1;
    // p.61/p.62's block R is the one block whose leader is ACTIVELY LAST, because the parent's
    // T' pass laid it out outside [v_s,v_l]. Everything else follows p.43's leader-first.
    const bool leaderActivelyLast = (a.isCPrime && b == a.rootBlock);
    child.nodes = childCycleOfBlock(B, blk, b, a.isCPrime, leaderActivelyLast);
    CHECK(child.nodes.front() == blk.leader,
          "block %d's cycle %s does not start with its leader %d", b,
          to_string(child.nodes).c_str(), blk.leader);
    // The child's spine direction, from the PAPER rather than from the ranks P1 will read.

    // Derive the direction from the constructor rule, independently of the ranks that P1 checks
    // against it.

    // The paper states it directly. p.43 defines the child's logical order as the traversal
    // this very call emitted the block's nodes in -- "starting at the leader of B traverse its
    // boundary in counterclockwise order, and list the nodes assigned to B as they are
    // encountered" -- and this call emitted that list in ITS OWN logical direction. So the
    // child's logical order runs along the spine the same way the parent's does:

    //     child.descending = ctx.descending

    // p.62 is the same statement for a C' call, whose own direction is right-to-left (p.55):
    // "each cycle bounding a (nontrivial) block is laid out in clockwise order FROM RIGHT TO
    // LEFT starting with the leader." Descending parent, descending child.

    // `childCycleOfBlock` has separately put the cycle in the matching logical SENSE, keyed on
    // `a.isCPrime` -- which is a different question: it asks whose frame the boundary was
    // STORED in, not which way this cycle runs. An ordinary block cycle inside a descending
    // parent has `ctx.descending` true and `a.isCPrime` false.

    // P1's check on entry is then a real test of the placement: if the run the parent produced
    // disagrees with the direction the paper assigns, P1 fires -- which is what it is for.

    // Block R is the exception in this too, and for the same reason its cycle's sense flips:
    // its leader sits at the opposite end of the run from every sibling's, so reading the same
    // cycle leader-first traverses it the other way round the spine. p.62 says exactly that --
    // R's leader is "laid out FIRST" where the others end with theirs.
    child.descending = leaderActivelyLast ? !ctx.descending : ctx.descending;
    child.c0 = leaderColour;
    // p.60 DEFINES a block cycle's two colours by which edges its nodes carry, rather than
    // prescribing values: the near-leader nodes u_t..u_{q+1} carry the forward and level-1
    // edges, and "all colored edges incident to u_t,...,u_{q+1} which do not go to the leader
    // u have the same color, namely c3 or c4, opposite to the color of B. This is the FIRST
    // color of B"; the far nodes u_{q-1}..u_1 carry the back edges, and "they all have the
    // same color (c1 or c0 if B is dominated by v_1). This is the SECOND color of B".

    // For a Case 1 block those edges are coloured by the ordinary forward/back rules, giving
    // the values below. A block of T_R in Case 2 is coloured by p.54's own rule instead --
    // "Binding edges... to the FURTHEST of v_s, v_{s+1} receive color c3 or c4 opposite to
    // that of R, and binding edges to the CLOSER one receive color c1".

    // p.60 identifies the two colours by WHICH EDGES carry them, so for a Case 2 T_R block the
    // question is which of v_s, v_{s+1} its BACK edges go to: that anchor's colour is the
    // second, and the other anchor's is the first. p.44 defines back by layout order -- "(v_i,
    // u) is a back edge if v_i comes before u in the layout" -- so the back anchor is the one
    // preceding the block's nodes. p.54 then supplies the two colours: the FURTHEST of the two
    // anchors carries opposite-R, the closer one c1.

    if (caseTwo && inTR[b]) {
      const int oppR = (blockColor[R] == c3) ? c4 : c3;
      CHECK(trPlace != TRPlacement::None,
            "Case 2: block %d of T_R has no placement, so its cycle's first and second "
            "colours are undetermined", b);
      // The two colours follow from p.60 and p.54 together, in two steps.

      // p.60 says WHICH EDGES carry them: the second colour is on the back edges of the
      // far-side nodes u_{q-1}..u_1, the first on the forward and level 1 edges of the
      // near-leader nodes u_t..u_{q+1}.

      // p.54 says which COLOUR each anchor's edges get: "Binding edges from the inner nodes
      // assigned to the blocks of T_R to the FURTHEST of v_s, v_{s+1}... receive color c3 or c4
      // opposite to that of R, and binding edges to the CLOSER one receive color c1."

      //   2b, group right after v_s:      closer v_s (c1),   furthest v_{s+1} (oppR)
      //                                   back edges -> v_s -> back-side colour c1
      //   2c, group right before v_{s+1}: closer v_{s+1} (c1), furthest v_s (oppR)
      //                                   back edges -> v_s -> back-side colour oppR

      // Both inputs are logical-order facts, so the two RUNS' colours are
      // direction-invariant.
      const int backSideColourTR = (trPlace == TRPlacement::AfterVs) ? c1 : oppR;
      const int forwardSideColourTR = (backSideColourTR == oppR) ? c1 : oppR;
      // WHICH P5 clause governs which run is frame-INDEPENDENT, exactly as in the ordinary
      // branch below: `childCycleOfBlock` presents every block cycle in its frame's own
      // counterclockwise sense, so the child's layout is p.45's u, u_t,..., u_q, u_{q-1},
      //..., u_1 in both frames and logical indices 1..m-1 are the forward/level-1 run.

      // The first and second color roles follow the mirrored block run; the C' frame alone does
      // not exchange them.
      child.c1 = forwardSideColourTR;
      child.c2 = backSideColourTR;
      // CROSS-CHECK, not a definition: the colour p.54 actually put on a far-side node's
      // binding edge must be the second colour just derived. This is the assertion the previous
      // version could not make, because it took that colour AS the definition.

      // u_q splits the two node groups. It uses `blk.dominator`, the one notion of the group's
      // dominator -- which Case 2's setup CHECK proves equals v_s for every T_R block, since
      // p.54 derives that rather than imposing it.
      {
        vector<int> cw;
        const int qIdx = lemma4UqIndex(B.g, blk, blk.dominator, a.isCPrime, &cw);
        CHECK(qIdx >= 0, "Case 2: no node of block %d is adjacent to its dominator v_s=%d", b,
              blk.dominator);
        // Only edges THIS Step 1a coloured count: an ancestor may have coloured an edge between
        // the same two vertices under its own rules.
        for (int i = 0; i < qIdx; i++)
          for (int anchor : {K[s_idx], K[s_idx + 1]}) {
            const auto pk = make_pair(min(cw[i], anchor), max(cw[i], anchor));
            if (!B.colouredHere.count(pk)) continue;
            auto it = B.page.find(pk);
            if (it == B.page.end()) continue;
            // Lemma 4 also bounds WHICH anchor a far-side node may reach: u_i with i < q is
            // "adjacent to v_f but to no other outer node", and v_f here is v_s. So an edge
            // from a far-side node to v_{s+1} contradicts Lemma 4 outright.
            CHECK(anchor == K[s_idx],
                  "Lemma 4 violated: far-side node %d of block %d (index %d < q=%d) has a "
                  "binding edge to v_{s+1}=%d, but Lemma 4 allows only the dominator v_s=%d",
                  cw[i], b, i, qIdx, K[s_idx + 1], K[s_idx]);
            // The colour p.54 actually put on a far-side node's BACK edge must be the
            // back-side run's colour. Stated against the RUN, not against `child.c2`: which
            // P5 clause reports that run depends on the frame.
            CHECK(it->second == backSideColourTR,
                  "Case 2: block %d's far-side node %d binds to %d with colour %d, but p.54 "
                  "and p.60 put the back-edge run of this cycle on %d (subcase %s, c1=%d, "
                  "opposite-R=%d)", b, cw[i], anchor, it->second, backSideColourTR,
                  trPlace == TRPlacement::AfterVs ? "2b" : "2c", c1, oppR);
          }
      }
    } else {
      // p.60 identifies the two colours BY WHICH EDGES CARRY THEM, not by position:
      //   * the nodes u_t..u_{q+1} carry the forward and level-1 edges, whose colour is "c3 or
      //     c4, opposite to the color of B. This is the FIRST color of B";
      //   * the nodes u_{q-1}..u_1 carry the back edges, "c1 or c0 if B is dominated by v_1.
      //     This is the SECOND color of B".
      const int forwardSideColour = (blockColor[b] == c3) ? c4 : c3;
      const int backSideColour = domByLeader ? c0 : c1;
      // WHICH P5 clause governs which run follows from where u_q sits in the CHILD'S OWN
      // layout order.

      // For every block except p.62's R that is p.45's shape in BOTH frames -- u, u_t,
      //..., u_q, u_{q-1},..., u_1 -- because `childCycleOfBlock` presents the boundary in the
      // frame's own counterclockwise sense (p.55's right-to-left import of p.43's traversal).
      // The nodes at logical indices 1..m-1 are then u_t..u_{q+1}, the forward/level-1 run, and
      // P5(a)'s interval [2,m-1] is exactly those: P5(a) carries the forward-side colour.

      // Block R is the exception, and p.62's own text is what makes it one. It prints R's
      // layout as "u, u_1,..., u_t" -- the INCREASING order -- and then names the runs by
      // p.60's labels against that order:

      //   "nodes u_t,..., u_{q+1} (if q < t) are only incident to BACK edges to u_l. These
      //    edges have all color c_1, which is the FIRST color of R. Nodes u_{q-1},..., u_1
      //    (if q > 1) are incident to (1) forward edges (in the right-to-left direction), and
      //    (2) level 1 edges... all these edges have the same color, c_3 or c_4, opposite to
      //    the color of R. This is the SECOND color."

      // In that layout the nodes at indices 1..m-1 are u_1..u_{q-1}, the FORWARD run, which
      // p.62 puts on the SECOND colour -- so for R the clause letters are swapped relative to
      // p.60's. This follows from R's reversed cycle order, not
      // about C' frames in general.

      // Only block R receives the role exchange stated on p.62. Other C' blocks use the ordinary
      // roles in their mirrored runs.
      if (leaderActivelyLast) {
        child.c1 = backSideColour;
        child.c2 = forwardSideColour;
      } else {
        child.c1 = forwardSideColour;
        child.c2 = backSideColour;
      }
      // p.62 states the constraint that makes P6 hold for block R: "P6 follows because the
      // leader's colour is different than the second colour." Asserted rather than assumed --
      // where p.62 leaves R's second colour free (q = 1 makes its defining run empty), this is
      // the one condition the paper does impose on it.
      if (a.isCPrime && b == a.rootBlock)
        CHECK(child.c2 != child.c0,
              "p.62 violated for block R: its second colour %d equals its leader's colour, but "
              "p.62 makes P6 follow precisely because they differ (c1=%d, blockColor=%d)",
              child.c2, child.c1, blockColor[b]);
    }
    // m is the POSITION of u_q in the child's layout order.

    // u_q is Lemma 4's "node of B with highest index q that is adjacent to v_f", where v_f is
    // the dominator OF THE GROUP THIS BLOCK IS LAID OUT IN. That is `blk.dominator` here, with
    // no Case 2 override: p.54 does not DECLARE T_R dominated by v_s, it DERIVES it -- "they are
    // all adjacent to v_s and v_{s+1}... Thus, they are all dominated by v_s" -- so for a
    // correctly computed p.42 dominator the two are the same node, and the assertion at the top
    // of Case 2's setup proves it holds on every input reaching here. Writing `K[s_idx]` instead
    // would be a second notion of the same quantity, which is how a check and the construction
    // come to disagree; there is one notion, and Case 2's own CHECK is what licenses it.
    {
      int uq = -1;
      {
        vector<int> cw;
        // p.62's exception applies to block R of a C' call, which is that analysis's root block.
        // p.62's LEAST-index rule applies to EVERY block of a C' call, not only to R. p.62
        // states it in R's paragraph, but the reason is the reading direction, which its
        // general sentence gives to every inner cycle of C': "each cycle bounding a
        // (nontrivial) block is laid out in clockwise order FROM RIGHT TO LEFT starting with
        // the leader". Under that reading the layout order IS the clockwise order u_1..u_t, so
        // p.50's "first node in the layout adjacent to the dominator" is the LEAST index. R
        // differs from its siblings only in where the leader sits, not in the extremum.
        child.isRofCPrime = a.isCPrime && (b == a.rootBlock);
        // The turning point is LEMMA 4's u_q: "the node of B with highest index q that is
        // adjacent to v_f", over the clockwise order u_1..u_t of this analysis's frame.

        // NOT p.50's gloss "m is the first node in the layout (other than the leader) that is
        // adjacent to the dominator of the block". The two agree for an ordinary block and
        // differ for a C' block. The construction uses Lemma 4's definition:

        //   * An ordinary block's layout is p.45's u, u_t,..., u_q, u_{q-1},..., u_1. Lemma
        //     4's first part makes the nodes adjacent to v_f a PREFIX u_1..u_q of the
        //     clockwise order, so that prefix appears REVERSED at the end of the layout and
        //     the first of them encountered from the leader is u_q. Both readings agree.
        //   * A C' block's layout IS the clockwise order (p.62: "laid out in clockwise order
        //     from right to left STARTING WITH THE LEADER"), so scanning from the leader
        //     reaches u_1 first while Lemma 4 still names u_q. They agree only when the
        //     prefix has length one.

        // Three statements select u_q -- Lemma 4, p.43's nested splice point ("the leader of
        // B' is u_q"), and p.60's "P2 and P3 are satisfied with u_q as the turning point and
        // the attachment point" -- and p.60's is the one P2 and P3 are PROVED from. p.50's
        // clause is a parenthetical restatement of the lemma it glosses ("that is,..."), so
        // the construction uses Lemma 4; p.50's phrasing applies to the ordinary layout direction.

        // ONE reading for every frame: Lemma 4's HIGHEST index over the ACTIVE clockwise sequence.
        // The frame belongs to that SEQUENCE -- `a.isCPrime` selects which way it is read -- and the
        // extremum over it does not move with the frame, so there is no per-block variant here and
        // `lemma4UqIndex` offers none. p.62's "least index q" names
        // the same VERTEX against the unmirrored indexing, so applying a second flip on top of the
        // frame's mirror would return u_1 instead of u_q on every C' block.
        const int qi = lemma4UqIndex(B.g, blk, blk.dominator, a.isCPrime, &cw);
        CHECK(qi >= 0,
              "Step 1b: no node of block %d is adjacent to its group's dominator %d, so "
              "Lemma 4's u_q does not exist and P2 has no legal m", b, blk.dominator);
        uq = cw[qi];
        checkLemma4FirstPart(B.g, cw, qi, blk.dominator, K, b);
      }
      auto at = find(child.nodes.begin(), child.nodes.end(), uq);
      CHECK(at != child.nodes.end(),
            "Step 1b: the turning point %d of block %d is not one of its boundary "
            "nodes (%s)", uq, b, to_string(child.nodes).c_str());
      child.m = (int)(at - child.nodes.begin());
      CHECK(child.m >= 1,
            "Step 1b: the turning point of block %d is its leader, which P2 forbids", b);
      // p.50's back-edge characterisation of m, used by p.60's proof of clause (a):
      // "nodes of the block that PRECEDE m in the layout are not incident to any back edges,
      // while nodes m+1,..., p are ONLY incident to back edges."
      // This concerns back edges; the turning point itself is chosen using Lemma 4 above.

      // What IS still assertable without begging the question: by Lemma 4's first part the
      // nodes adjacent to the dominator form the prefix u_1..u_q of the clockwise order, so
      // no node AFTER u_q in that order may see the dominator. That is Lemma 4 stated
      // forwards, it is colour-free, and it localises a wrong u_q at the site that chose it.
      {
        vector<int> cwSeq(blk.vertices.begin() + 1, blk.vertices.end());
        if (!a.isCPrime) reverse(cwSeq.begin(), cwSeq.end());
        bool pastUq = false;
        for (int v : cwSeq) {
          if (v == uq) { pastUq = true; continue; }
          if (!pastUq) continue;
          CHECK(!B.g.vertices[v]->adjacent(B.g.vertices[blk.dominator]),
                "Lemma 4 violated for block %d: node %d follows u_q=%d in the clockwise order "
                "%s yet is adjacent to the dominator %d, so the nodes adjacent to it are not "
                "the prefix u_1..u_q that Lemma 4's first part requires and u_q is wrong", b,
                v, uq, to_string(cwSeq).c_str(), blk.dominator);
        }
      }
      // p.60: "Properties P2 and P3 are satisfied with u_q as the turning point and the
      // attachment point." The free point is then the other border node.
      if (child.m < (int)child.nodes.size() - 1) {
        child.attachmentPoint = uq;
        child.freePoint = child.nodes[child.m + 1];
      }
    }
    // p.60 lays a block out as "u, u_t,..., u_q, u_{q-1},..., u_1" -- two runs split at u_q.
    // Run A is positions 1..m. If it is not monotone in the PARENT's logical frame then the
    // placement and the boundary cycle order disagree, and P1 will fire on the child's own
    // entry check with no indication of which run went wrong. Logged here, where the block and
    // its frame are still in hand.
    {
      const SpineView psv{B, ctx.descending};
      bool runAok = true;
      for (int i = 1; i + 1 <= child.m; i++)
        if (!psv.precedesLogically(child.nodes[i], child.nodes[i + 1])) runAok = false;
      string ranks;
      for (int v : child.nodes)
        ranks += to_string(v) + "@" +
                 (B.spine.placed(v) ? to_string(B.spine.rank(v)) : string("np")) + " ";
      LOG_IF(B.verbose >= 2, "S1B isCPrime=%d isR=%d parentDesc=%d m=%d nested=%d runAok=%d ranks=%s",
          (int)a.isCPrime, (int)child.isRofCPrime, (int)ctx.descending, child.m,
          (int)plan.nestedFor(blk.dominator), (int)runAok, ranks.c_str());
    }
    child.parentTag = B.cycTag;
    LOG_IF(B.verbose >= 3,
           "CHILD blk%d nodes=%s desc=%d m=%d c0=%d c1=%d c2=%d origin=%s", b,
           to_string(child.nodes).c_str(), (int)child.descending, child.m, child.c0,
           child.c1, child.c2, child.origin);

    children.push_back(child);
  }

  // --- Step 2: the cycles K_j cut off by short edges of K that are chords of C. ---
  // p.59 tabulates each K_j's state. Every K_j other than K_s has its turning point at
  // its LAST node -- "We let the turning point be v_{j+1} (the last node of K_j)" -- so
  // it has no border; only K_s inherits C's.

  // p.53: "We also have to choose a leader for each cycle K_j and color its incident
  // edges. If s != 1 and the edge (v_s,v_{s+1}) is a chord of C, then one of v_s,
  // v_{s+1} is not a border node. We let the leader of K_s be this node.... In all
  // other cases (i.e. j != s or j = s = 1) we let the leader of the cycle K_j be v_j
  // (the first node of the cycle). For all K_j the leader's color is the color of the
  // edge (v_j, v_{j+1})."
  for (auto& cc : gc.chordCycles) {
    const vector<int> kj = chordCycleNodes(B, ctx.nodes, cc);
    // Which short edge of K cut this cycle off: its endpoints are kj.front()/kj.back().
    const int jpos = posInK.at(kj.front());
    // In Case 3 the cycles cut off between v_s and v_l belong to C', whose own Step 2 expands
    // them: p.55 gives C' its own chord decomposition ("To expand C' we will first add to it
    // the chords"), and the short edge cutting each one off is an edge of K'.
    if (caseThree && jpos >= s_idx && jpos + 1 <= l_idx) continue;
    CHECK(posInK.count(kj.back()) && posInK.at(kj.back()) == jpos + 1,
          "K_j (%s) is not cut off by a short edge of K: %d and %d are not consecutive "
          "on K", to_string(kj).c_str(), kj.front(), kj.back());

    CycleContext child;
    child.origin = "step2Kj";
    // A K_j stays at its parent's peeling depth (§4: "if C has nodes at level i of G, then
    // the cycles K_j have also nodes at level i"), which is why its termination measure is
    // the cycle length rather than the depth.
    child.cyclePath = ctx.cyclePath + "/Kj" + to_string(jpos);
    child.peelDepth = ctx.peelDepth;
    child.nodes = kj;
    // A K_j is a run of the parent's LOGICAL sequence, so its own logical order runs along
    // the spine the same way the parent's does.
    child.descending = ctx.descending;
    // EXCEPT inside Case 3's region II. There the cycle being expanded is C' = (v_s,..., v_l)
    // with v_l as its leader (p.55), so C' is read RIGHT-TO-LEFT and a K_j cut off by a chord
    // of C' is a sub-cycle of C' in that reading. p.53's "we let the leader of the cycle K_j
    // be v_j (the first node of the cycle)" then names the first node OF C', i.e. the endpoint
    // at the v_l end, not the v_s end. So reverse the slice to put that endpoint first and
    // flip the direction bit with it.

    // The K_s row below is excluded: it chooses its own leader by p.53's border rule and
    // reverses on its own terms. Only the cycles strictly inside region II are affected.
    const bool kjInRegionII =
        caseThree && jpos > s_idx && jpos + 1 <= l_idx;
    if (kjInRegionII) {
      reverse(child.nodes.begin(), child.nodes.end());
      child.descending = !child.descending;
    }
    // "For all K_j the leader's color is the color of the edge (v_j, v_{j+1})", which
    // Step 1a has just assigned.
    const auto key = make_pair(min(kj.front(), kj.back()), max(kj.front(), kj.back()));
    auto pg = B.page.find(key);
    CHECK(pg != B.page.end(),
          "K_j (%s): its closing edge (%d,%d) was not coloured by Step 1a",
          to_string(kj).c_str(), kj.front(), kj.back());
    child.c0 = pg->second;
    child.m = (int)kj.size() - 1;  // default: turning point at the last node, no border

    // CASE 2's exception for K_s (p.54, last sentence): "If (v_s, v_{s+1}) is a chord of C,
    // the leader of the corresponding cycle K_s is v_s in Case 2b (v_{s+1} in Case 2c) WITH
    // COLOR c2 (resp. c1)."

    // So in Case 2 the K_s leader's colour is c2 or c1 by subcase -- NOT the colour of the
    // closing edge, which p.53 prescribes for every other K_j. The two differ here because
    // p.54 gives the border edge "color c3 or c4 opposite to that assigned to block R", the
    // same value the binding edges to the furthest of v_s/v_{s+1} take, so taking it as the
    // leader's colour would put the K_s leader edges on that page too, where they conflict
    // with those binding edges.
    if (caseTwo && jpos == s_idx) {
      child.c0 = (trPlace == TRPlacement::AfterVs) ? c2 : c1;
    }
    // The rows of p.59. The cycle that CONTAINS the border inherits it; every other K_j has
    // its turning point at its last node and so has no border.

    // K_1 with s = 1 is the first of those: "If s = 1 (i.e. m+1 <= v_2), then K_1 INHERITS
    // FROM C the turning point m, the free point, the first color c1 and the second color c2."
    // With s_idx == 0 the border-crossing short edge of K is (v_1,v_2), so K_1 straddles the
    // border and takes C's own m/c1/c2 rather than the no-border row -- which is exactly the
    // configuration where the no-border row would hand it a first colour equal to its leader's
    // colour, since p.53 colours the short edges after the border c1.
    if (jpos == s_idx && hasBorder) {
      // "Cycle K_s, with s != 1.... The cycle K_s inherits the border and the free
      // point from C. Thus, if its leader is v_s (in which case v_s < m), then the
      // turning point is m, the first color is c1 and the second color is c2. If the
      // leader of K_s is v_{s+1} (in which case m+1 < v_{s+1}), then the turning point is
      // m+1, the first color is c2 and the second color is c1."

      // And p.53 chooses that leader: "If s != 1 and the edge (v_s,v_{s+1}) is a chord of
      // C, then one of v_s, v_{s+1} is not a border node. We let the leader of K_s be
      // this node. That is, if v_s < m we choose v_s to be the leader of K_s, otherwise
      // we choose v_{s+1}." p.59 explains why not simply v_s: "If the attachment point of
      // C was m+1 (the second node of the cycle K_s), then P5 and P6 could be violated
      // because the color of the edges between N2 and m+1 is not restricted."
      const int posVs = posInC.at(kj.front()), posVs1 = posInC.at(kj.back());
      // Both p.59 rows -- K_1 with s = 1, and K_s with s != 1 -- inherit C's border, so the
      // cycle must contain it. The shared code below then picks the row by which side of the
      // border the leader falls on, which covers s = 1 (leader v_1, before it) without a
      // separate case.
      CHECK(posVs <= ctx.m && ctx.m + 1 <= posVs1,
            "K_j (%s) inherits C's border but does not straddle it: positions %d..%d vs m=%d",
            to_string(kj).c_str(), posVs, posVs1, ctx.m);
      // The border, in K_s's own indexing: the gap between the two nodes of C at
      // positions m and m+1, both of which lie on K_s (its nodes are C[posVs..posVs1]).
      const int mInKj = ctx.m - posVs;
      // WHICH END IS THE LEADER. p.53 chooses by the border ("if v_s < m we choose v_s...
      // otherwise v_{s+1}"), but that is the Case 1 rule. In Case 2 p.54 chooses by SUBCASE
      // instead: "the leader of the corresponding cycle K_s is v_s in Case 2b (v_{s+1} in
      // Case 2c)". The two disagree whenever 2c applies with v_s < m, and then it matters for
      // P2: p.61 says of 2c that "all new nodes inserted in the interval (v_s, v_{s+1}) are
      // next to the leader v_{s+1}", i.e. the T_R group Case 2c places before v_{s+1} becomes
      // that cycle's own N1 and is exempt. Read with v_s as leader the same vertices sit in a
      // gap P2 requires empty.
      const bool leaderIsVs = caseTwo ? (trPlace == TRPlacement::AfterVs) : (posVs < ctx.m);
      if (leaderIsVs) {
        // Leader is v_s, the FIRST node: turning point m, first colour c1, second c2.
        child.m = mInKj;
        child.c1 = c1;
        child.c2 = c2;
        // K_s's color pair is fixed by p.59. The permission to choose
        // another second color applies to K_1 and 1<j<s, not to K_s. Its prescribed pair is:

        //   "if its leader is v_s (in which case v_s < m), then the turning point is m, the
        //    first color is c_1 and the second color is c_2. If the leader of K_s is v_{s+1}
        //    (in which case m+1 < v_{s+1}), then the turning point is m+1, the first color is
        //    c_2 and the second color is c_1."

        // So if the paper-prescribed assignment is inconsistent with P5 on some input, that is
        // a fact to report, not to repair: the fault is upstream in whoever chose this cycle's
        // leader colour, and silently exchanging the roles here would hide it. Asserted below,
        // after both branches, where the leader's colour is known.
      } else {
        // v_s IS the turning point m, so p.53 makes the leader v_{s+1}, the LAST node, and
        // the cycle is read right-to-left: "the turning point is m+1, the first color is
        // c2 and the second color is c1".

        // The leader is v_{s+1}, the LAST node of the slice, so reverse to put it first and
        // mark that logical order now runs against the slice's own direction.

        // The turning point is "m+1", not m: reversing sends slice index i to L-1-i, so the
        // border -- the gap between the slice's mInKj and mInKj+1 -- becomes the gap between
        // L-2-mInKj and L-1-mInKj. P2 names a gap by its LOWER logical index, so the turning
        // point is L-2-mInKj, which is where the node at parent position m+1 lands. Taking
        // the reversal of m itself gives L-1-mInKj, one too high, and when mInKj is 0 that is
        // exactly p-1 -- P2's no-border sentinel -- so the cycle would silently lose the
        // border it inherits here, and its N2 would then read as foreign vertices in a gap
        // P2 requires empty.
        reverse(child.nodes.begin(), child.nodes.end());
        child.descending = !child.descending;
        child.m = (int)kj.size() - 2 - mInKj;
        child.c1 = c2;
        child.c2 = c1;
        // The leader's colour is the colour of (v_s,v_{s+1}) either way (p.53).
      }
      // "The cycle K_s inherits the border and the free point from C."
      child.attachmentPoint = ctx.attachmentPoint;
      child.freePoint = ctx.freePoint;
      // P2 requires the turning point to be a node other than the leader: logical index
      // 1..p-1, `nodes` is always logical.
      CHECK(child.m >= 1 && child.m <= (int)kj.size() - 1,
            "K_s (%s): the inherited turning point %d is out of range",
            to_string(kj).c_str(), child.m);
      // p.59's K_s pair, taken as stated, must satisfy P5's c1 != c0. If it does not, the
      // leader's colour and p.59's row disagree and the fault is upstream -- in p.53's
      // short-edge rule or p.54's Case 2 override, whichever assigned it. Reported here rather
      // than repaired: p.59 grants the K_s row no latitude in either colour.
      CHECK(child.c1 != child.c0,
            "K_s (%s): p.59 fixes its first colour at %d for a leader at the %s end, but that "
            "equals the leader's own colour c0=%d, which P5 forbids. p.59 states the K_s pair "
            "outright -- its 'any other color' latitude belongs to the K_1 and 1<j<s rows -- so "
            "the disagreement is upstream, in whichever rule coloured (v_s,v_{s+1}): p.53's "
            "short-edge rule, or p.54's Case 2 override (caseTwo=%d, trPlace=%s, parent c1=%d "
            "c2=%d)", to_string(kj).c_str(), child.c1, leaderIsVs ? "v_s" : "v_{s+1}",
            child.c0, (int)caseTwo,
            trPlace == TRPlacement::AfterVs ? "2b" : (trPlace == TRPlacement::BeforeVs1 ? "2c"
                                                                                       : "none"),
            c1, c2);
    } else {
      // "Cycle K_j with 1 < j < s. The leader is v_j, the first node of this cycle, with
      // color c2... We let the turning point be v_{j+1} (the last node of K_j) and the
      // FIRST COLOR c1; we may take c2 as the second color... The case s < j is
      // analogous."

      // The row is chosen by POSITION relative to the border, which is how p.59 states it.
      // "Analogous" is forced from two directions. By the parent's P5: a K_j before the
      // border has its interior edges leaving with the parent's c1, one after the border
      // with c2. And by P5's own c1 != c0: p.53 gives the short edges after the border
      // colour c1, so for j > s the leader's colour IS c1, and c1 cannot also be the first
      // colour.
      if (jpos > s_idx) {
        child.c1 = c2;
      } else {
        child.c1 = c1;
      }
      // The SECOND colour is free here: "we may take c2 (OR ANY OTHER COLOR BESIDES c1) as the
      // second color" (p.59). Take the leader's own colour.

      // Why it matters rather than being cosmetic: c3 and c4 are defined as the two pages
      // OTHER than c1 and c2, so whenever c2 != c0 the leader's page c0 is itself one of
      // {c3,c4}, and a block can then be assigned the page P4/O2 reserve for leader-incident
      // edges. p.53's escape ("If B is dominated by v_1 and c0 in {c3,c4}, then we give them
      // color c1") covers only blocks dominated by v_1 -- p.57 confirms v_1 is meant, "the
      // edges of the v_1 blocks have color c1" -- so a block dominated by any other node has
      // no escape and its leader edges collide on c0.

      // Choosing c2 = c0 removes the collision at its source, and it is the same choice the
      // top-level call makes for the same reason. P5 permits it: "The second color c2 may be
      // the same as the leader's color c0" (p.49).
      child.c2 = child.c0;
    }
    // Verification, not repair: with the positional row above this holds because p.53's
    // short-edge colours put the leader's colour on the other side of the border from the
    // first colour. If it fires, the closing edge disagrees with that rule -- the real
    // anomaly, which is worth reporting rather than silently swapping around.
    CHECK(child.c1 != child.c0,
          "K_j (%s): its first colour %d equals the leader's colour %d (jpos=%d, s=%d), so "
          "the closing edge disagrees with p.53's short-edge colours",
          to_string(kj).c_str(), child.c1, child.c0, jpos, s_idx);

    // p.53: "We also have to choose a leader for each cycle K_j and COLOR ITS INCIDENT
    // EDGES." §4's colour-c1 list names them: "in case this edge is a chord, the edges
    // connecting the leader v_j of K_j to other nodes of K_j (i.e. the edges or chords
    // (v_j, i) of C, where... v_j < i <= v_{j+1})". They take the leader's colour, which
    // p.53 gives as "the color of the edge (v_j, v_{j+1})", so the PARENT owns them --
    // colouring them here is what makes P4 hold on entry to K_j.

    // This runs after the row selection above, because that is what CHOOSES the leader:
    // for the K_s row where p.53 picks v_{s+1}, the leader is the LAST node and the
    // p.53: "we let the leader of the cycle K_j be v_j (the FIRST node of the cycle)".
    // `kj` is a slice of the parent's LOGICAL order, so v_j is simply its front -- the
    // parent's reading direction is already accounted for by that order, and the child
    // inherits it through `descending` below. The K_s row above may have reversed the
    // slice, which is why the leader is read off `child.nodes` and not off `kj`.
    const int kjLeader = child.nodes.front();
    // The other end of K_j: its closing edge (kj.front(), kj.back()) is K_j's LONG edge, and
    // P4 exempts exactly that one from the leader's colour -- "All of them, EXCEPT POSSIBLY
    // FOR THE EDGE (1,p), have the same color, called the leader's color". It keeps whatever
    // the short-edge rule gave it (in Case 2, p.54's "opposite to that assigned to block R"),
    // which is why the leader's colour may differ from it.
    const int kjFarEnd = (kjLeader == kj.front()) ? kj.back() : kj.front();
    {
      PagePlan kjp;
      kjp.open(B.page);
      for (int v : kj) {
        if (v == kjLeader || v == kjFarEnd) continue;
        if (!B.g.vertices[kjLeader]->adjacent(B.g.vertices[v])) continue;
        const auto ek = make_pair(min(kjLeader, v), max(kjLeader, v));
        if (kjp.has(kjLeader, v)) {
          // Already coloured by the short-edge rule above; the two must agree.
          kjp.require(kjLeader, v, child.c0, "kjLeaderEdge", "kj-leader-level0");
        } else {
          B.kjLeaderEdges.insert(ek);
          kjp.assign(kjLeader, v, child.c0, "kjLeaderEdge", "kj-leader-level0");
        }
      }

      applyPagePlan(B, kjp);
    }

    // p.59 on the INTERMEDIATE nodes of K_j (all but its two ends): "the intermediate nodes
    // of K_j... are not adjacent to any nodes which lie inside K or inside another cycle
    // K_i, because of the planarity of the graph. Therefore, apart from the edges incident to
    // the leader of K_j, neither Step 1a nor the expansion of any other new cycle will add
    // any edges to the intermediate nodes of K_j."

    // This is what makes P5 vacuous for a K_j on entry, and hence what makes p.59's "we may
    // take c2 as the second color" a genuinely free choice rather than one this code has to
    // derive. If it fails, the defect is upstream in whoever laid out C.
    for (size_t t = 1; t + 1 < kj.size(); t++) {
      const int mid = kj[t];
      for (Vertex* nbv : B.g.vertices[mid]->neighbors()) {
        const int w = nbv->index;
        if (w == kjLeader) continue;              // edges to the leader are expected
        if (w == kj[t - 1] || w == kj[t + 1]) continue;  // K_j's own short edges
        auto pg = B.page.find(make_pair(min(mid, w), max(mid, w)));
        if (pg == B.page.end()) continue;
        // p.59's claim is about what "Step 1a [and] the expansion of any other new cycle"
        // add, i.e. edges coloured by THIS instance or later. An edge an ancestor cycle
        // coloured predates K_j and is not one of them -- P1 already places K_j's nodes and
        // P4 governs what may be coloured among them on entry.
        const auto ek = make_pair(min(mid, w), max(mid, w));
        if (!B.colouredHere.count(ek)) continue;
        CHECK(false,
              "p.59 violated for K_j %s: intermediate node %d already has a coloured edge to "
              "%d (page %d) not incident to the leader %d [%s]",
              to_string(kj).c_str(), mid, w, pg->second, kjLeader,
              B.provenance.count(ek) ? B.provenance.at(ek).c_str() : "(unrecorded)");
      }
    }
    child.parentTag = B.cycTag;

    children.push_back(child);
  }
}

// The p.52 dispatch: pick Case 1, 2 or 3 for one cycle and run Step 1a accordingly.

// Case 3 calls this AGAIN, on C'. That is what makes p.55's "if we apply the algorithm to C'
// we will arrive at Case 1 or Case 2" an actual call: C' gets the same three-way decision, so
// it reaches Case 2 exactly when its own v_s dominates blocks, and Case 1 otherwise. `exc`
// carries p.55's two differences for that call and is empty for the outer one.

static void dispatchStep1a(Builder& B, const CycleContext& ctx, const GcDecomposition& gc,
                           TwoLevelAnalysis& a, vector<CycleContext>& children,
                           const CPrimeExceptions& exc = CPrimeExceptions{});
static void expandOutputChecks(Builder& B, const CycleContext& ctx,
                               const vector<CycleContext>& children);

static void expand(Builder& B, const CycleContext& ctx) {
  checkP1toP6(B, ctx);

  // Step 1 numbers K "as u_1 = 1, u_2,..., u_k = p", so u_1 must be logical node 1, the
  // leader. `ctx.nodes` is logical by CycleContext's contract, so the trace starts at the
  // leader for every cycle, including leader-last cycles.
  GcDecomposition gc = decomposeGc(B.g, ctx.nodes);
  const vector<int>& K = gc.K;

  TwoLevelAnalysis a = analyzeTwoLevelAugmented(B, K);

  // Step 1 analyses the interior of K, so that is the interior-bounding cycle, while
  // Gamma and the dominators are measured along C. The two coincide when C is chordless.

  // Step 1a's per-instance records, cleared once: Case 3's Step 1a makes two calls into the
  // engine and Lemma 5, §D and O1 are all about their combined result.
  B.colouredHere.clear();
  B.forwardBindingHere.clear();
  B.bindDir.clear();
  B.cPrimeLeaderEdges.clear();
  B.kjLeaderEdges.clear();
  B.firstInnerLevel1Edges.clear();
  B.cPrimeNodesHere.clear();
  B.placedHere.clear();

  vector<CycleContext> childrenOut;
  dispatchStep1a(B, ctx, gc, a, childrenOut);
  // Everything Step 1a coloured, checked once -- in Case 3 that spans both regions. This is where
  // Lemma 5 (p.45) and §D / two-level legality (Theorem 1) are enforced for the WHOLE Step 1a.
  checkStep1aOutput(B, a, K, gc, ctx.nodes, ctx.c1, ctx.c2, ctx.m);
  // O1/O2 (p.50): the reserved-space partition and the leader-colour promise.
  expandOutputChecks(B, ctx, childrenOut);

  for (const auto& child : childrenOut) expand(B, child);
}

static void dispatchStep1a(Builder& B, const CycleContext& ctx, const GcDecomposition& gc,
                           TwoLevelAnalysis& a, vector<CycleContext>& children,
                           const CPrimeExceptions& exc) {
  const vector<int>& K = gc.K;
  const int p = (int)ctx.nodes.size();
  map<int, int> posInC;
  for (int i = 0; i < p; i++) posInC[ctx.nodes[i]] = i;
  const int s_idx = borderCrossingEdgeOfK(ctx, K, posInC);
  const int v_s = K[s_idx];

  // ---- The three-way dispatch of p.52. -------------------------------------
  // "Case 1. s = 1 or s != 1 but node v_s does not dominate any blocks. Included here is
  // also the case that there are no nodes in the interior of K (v_s does not dominate any
  // blocks, because there are none), and the case that m = p (the last outer node does
  // not dominate any blocks)."

  // Otherwise (p.53) R is the highest block dominated by v_s and v_l the last node of K
  // that sees R; "Case 2. l = s+1" and "Case 3. l > s+1".

  // Note Case 1 is NOT the same as "no border": a bordered cycle whose v_s dominates
  // nothing is Case 1.
  vector<int> vsBlocks;
  for (int b = 0; b < (int)a.blocks.size(); b++)
    if (a.blocks[b].dominator == v_s) vsBlocks.push_back(b);

  if (s_idx == 0 || vsBlocks.empty()) {

    expandStep1a(B, ctx, gc, a, s_idx, /*R=*/-1, /*l_idx=*/-1,
                 TRPlacement::None, children, exc);
  } else {
    // R = the HIGHEST block (in the block tree) dominated by v_s. Lemma 3 makes the
    // blocks with a common dominator a directed path, so "highest" is the unique one
    // whose parent is not in the group.
    int R = -1;
    for (int b : vsBlocks) {
      const int par = a.blocks[b].parent;
      if (find(vsBlocks.begin(), vsBlocks.end(), par) == vsBlocks.end()) {
        CHECK(R == -1,
              "two blocks (%d and %d) dominated by v_s=%d have no parent in the group, "
              "contradicting Lemma 3's directed path", R, b, v_s);
        R = b;
      }
    }
    CHECK(R >= 0, "no highest block among those dominated by v_s=%d", v_s);
    // v_l = the last node (highest index) of K that SEES R. p.53's Fig. 9 argument uses
    // exactly the `sees` relation here, not plain adjacency.
    int l_idx = -1;
    for (int i = 0; i < (int)K.size(); i++)
      for (auto& e : a.blocks[R].edges)
        if (sees(B.g, K[i], e.first, e.second)) { l_idx = i; break; }
    CHECK(l_idx >= 0,
          "no node of K sees the highest v_s block R=%d, but v_s=%d dominates it", R,
          v_s);
    CHECK(l_idx > s_idx,
          "the last node of K seeing R=%d is at position %d, not after v_s at %d", R,
          l_idx, s_idx);
    {
      // ---- The 2a/2b/2c subcase (p.54), which fixes where the blocks seen only by v_s
      // and v_{s+1} go. Case 3 needs it too: p.61 says of region II's blocks whose last
      // seeing node is u_{s+1} that "all such blocks are placed next to u_s or u_{s+1} AS
      // EXPLAINED IN CASE 2".
      const int posVs = posInC.at(K[s_idx]), posVs1 = posInC.at(K[s_idx + 1]);
      // "(2a) v_s = m and v_{s+1} = m+1; i.e. (v_s, v_{s+1}) is the border of C."
      const bool a2 = (posVs == ctx.m && posVs1 == ctx.m + 1);
      // "If (2a) does not hold, then by the planarity of the graph, either (2b) there is
      // no edge from v_s to another node j != v_{s+1} of C that crosses the border
      // (j >= m+1), or (2c) there is no edge from v_{s+1} to another node j != v_s of C
      // that crosses the border (j <= m)."
      // "Crosses the border" means the edge spans the interval (m, m+1) -- one endpoint at
      // or left of m and the other at or right of m+1 -- so an edge that merely ENDS on a
      // border node does not cross it. From v_s (at position <= m) the crossing targets
      // are the nodes at positions >= m+1; from v_{s+1} (at position >= m+1) they are the
      // nodes at positions <= m. Each end's own border node is excluded, since the border
      // edge itself is not a crossing.
      // The LONG edge (v_p, v_1) is never a crossing. Every cycle has it, and if it
      // counted then a v_s or v_{s+1} that happens to be an endpoint of it would block its
      // subcase unconditionally -- which would contradict p.56's proof that one of
      // 2a/2b/2c always applies. P4 already treats the long edge as the one exception
      // among C's own edges ("all of them, EXCEPT POSSIBLY FOR THE EDGE (1,p)").
      const int firstNode = ctx.nodes.front(), lastNode = ctx.nodes.back();
      auto isLongEdge = [&](int x, int y) {
        return (x == firstNode && y == lastNode) || (x == lastNode && y == firstNode);
      };
      auto crossesFrom = [&](int from, int excluded, bool toRight) {
        for (Vertex* nbv : B.g.vertices[from]->neighbors()) {
          const int w = nbv->index;
          if (w == excluded) continue;
          if (isLongEdge(from, w)) continue;
          auto it = posInC.find(w);
          if (it == posInC.end()) continue;
          // p.54 states the ranges: from v_s the crossing targets are j >= m+1, and from
          // v_{s+1} they are j <= m. Inclusive at the border nodes -- p.56 relies on
          // exactly that when it derives "in Case 2b we must have v_s < m BECAUSE node m
          // is adjacent to m+1": were the edge (m, m+1) not counted as a crossing, that
          // derivation would not follow.
          if (toRight ? (it->second >= ctx.m + 1) : (it->second <= ctx.m)) return true;
        }
        return false;
      };
      const bool b2 = !crossesFrom(K[s_idx], K[s_idx + 1], /*toRight=*/true);
      const bool c2case = !crossesFrom(K[s_idx + 1], K[s_idx], /*toRight=*/false);

      TRPlacement trPlace;
      if (a2) {
        // "In Case 2a place the nodes assigned to the blocks of T_R next to the FREE POINT
        // of the border" -- and O1 says the same of any nodes laid out in the border.
        CHECK(ctx.freePoint == K[s_idx] || ctx.freePoint == K[s_idx + 1],
              "Case 2a: the free point %d is not an endpoint of the border edge (%d,%d)",
              ctx.freePoint, K[s_idx], K[s_idx + 1]);
        trPlace = (ctx.freePoint == K[s_idx]) ? TRPlacement::AfterVs
                                              : TRPlacement::BeforeVs1;
      } else {
        // p.56 proves 2b and 2c exhaust the rest: "If v_s and v_{s+1} are consecutive
        // nodes of C, then we must have v_s = m and v_{s+1} = m+1... Thus, 2a applies in
        // this case. If v_s and v_{s+1} are not consecutive then either 2b or 2c applies."
        // So this is a genuine case split, and a failure means planarity or the border is
        // wrong -- not something to resolve by preference.
        // p.56 derives, rather than assumes, that 2b implies v_s < m and 2c implies
        // v_{s+1} > m+1; they are consequences of the crossing test above, so they are
        // asserted here instead of used to gate the choice.
        const bool b2ok = b2, c2ok = c2case;
        if (b2ok) CHECK(posVs < ctx.m, "subcase 2b but v_s is at m (%d)", posVs);
        if (c2ok)
          CHECK(posVs1 > ctx.m + 1, "subcase 2c but v_{s+1} is at m+1 (%d)", posVs1);
        CHECK(b2ok || c2ok,
              "neither subcase 2b nor 2c applies to the border edge (%d,%d) of cycle %s "
              "(m=%d), which Y1989 p.56 proves impossible by planarity",
              K[s_idx], K[s_idx + 1], to_string(ctx.nodes).c_str(), ctx.m);
        // "in Case 2b they are placed right after v_s, and in Case 2c they are placed
        // right before v_{s+1}." When both hold either is legal; take 2b.
        trPlace = b2ok ? TRPlacement::AfterVs : TRPlacement::BeforeVs1;
      }

      if (l_idx <= s_idx + 1) {
        expandStep1a(B, ctx, gc, a, s_idx, R, l_idx, trPlace, children, exc);
      } else {

        vector<int> tPrimeColours;
        {
          CPrimeExceptions tPrimeExc = exc;
          tPrimeExc.blockColourOut = &tPrimeColours;
          expandStep1a(B, ctx, gc, a, s_idx, R, l_idx, trPlace, children, tPrimeExc);
        }

        // "Imagine that there is an edge (v_s, v_l) drawn on the plane in region I, and that
        // we want to expand the cycle C' = (v_s, v_{s+1},..., v_l) which is formed by this
        // edge and EDGES OF C. Regard v_l (the last node of C') as the leader of C'."

        // The run is taken along C, not along K: K skips C's nodes that lie on chord cycles,
        // and those nodes are part of C'.
        CycleContext cp;
        {
          const int cs = posInC.at(K[s_idx]), cl = posInC.at(K[l_idx]);
          CHECK(cs < cl, "Case 3: v_s at %d does not precede v_l at %d along C", cs, cl);
          cp.nodes.assign(ctx.nodes.begin() + cs, ctx.nodes.begin() + cl + 1);
        }
        reverse(cp.nodes.begin(), cp.nodes.end());   // leader v_l first
        cp.origin = "casePrime";
        cp.parentTag = B.cycTag;
        cp.descending = !ctx.descending;             // C' is read right-to-left
        cp.cyclePath = ctx.cyclePath + "/C'";
        cp.peelDepth = ctx.peelDepth;
        // C' is the one case whose closing edge is imagined -- p.55's
        // "Imagine that there is an edge (v_s, v_l)... this edge does not exist".
        cp.frameFictitiousClosure =
            !B.g.vertices[cp.nodes.front()]->adjacent(B.g.vertices[cp.nodes.back()]);
        // "let c1 be the leader's color... The first color of C' is c2 and the second color
        // is c1" (p.55).
        cp.c0 = ctx.c1;
        cp.c1 = ctx.c2;
        cp.c2 = ctx.c1;
        // "The cycle C' has the same border and free point as C; only, its turning point is
        // m+1 because its leader is v_l (the last node)."
        cp.attachmentPoint = ctx.attachmentPoint;
        cp.freePoint = ctx.freePoint;
        {
          const int borderHigh = ctx.nodes[ctx.m + 1];
          auto at = find(cp.nodes.begin(), cp.nodes.end(), borderHigh);
          CHECK(at != cp.nodes.end(),
                "Case 3: C''s turning point m+1 (%d) is not a node of C'=%s", borderHigh,
                to_string(cp.nodes).c_str());
          cp.m = (int)(at - cp.nodes.begin());
        }

        // P4 must hold on entry, and p.55 says who establishes it: "By planarity, node v_l may
        // only be adjacent to other nodes i of C' between v_{l-1} and v_l... Give color c1 to
        // these edges (v_l, i)" -- that c1 is C''s leader colour c0. The fictitious long edge
        // (v_s, v_l) stays uncoloured: "this is not really necessary since this edge does not
        // exist".
        {
          // Recorded for the ownership check BEFORE the loop, not inside it: p.55 lets v_l have
          // no such edge at all, and then the loop body never runs. Setting it there would leave
          // the check with an empty C' while a C' call is in flight.
          B.cPrimeNodesHere = cp.nodes;
          const set<int> onCPrime(cp.nodes.begin(), cp.nodes.end());
          const int lead = cp.nodes.front();
          PagePlan cpp;
          cpp.open(B.page);
          for (Vertex* nbv : B.g.vertices[lead]->neighbors()) {
            const int w = nbv->index;
            if (!onCPrime.count(w) || w == cp.nodes.back()) continue;
            // p.55 gives every edge (v_l, i) the leader colour c0. An edge already coloured when
            // this plan opened -- an ancestor's short edge shared with C' -- is not this call's to
            // ASSIGN, but it is still C''s leader edge and p.55 fixes its colour, so REQUIRE that
            // the effective page is c0 rather than skipping it silently. A skip left the intended
            // colour unchecked, so a shared edge on the wrong page went unnoticed.
            if (cpp.has(lead, w)) {
              cpp.require(lead, w, cp.c0, "cPrimeLeaderEdge", "cprime-leader-level0");
              continue;
            }
            cpp.assign(lead, w, cp.c0, "cPrimeLeaderEdge", "cprime-leader-level0");
            B.cPrimeLeaderEdges.insert(make_pair(min(lead, w), max(lead, w)));
          }

          applyPagePlan(B, cpp);
        }

        // C''s own analysis, which p.55 states outright rather than leaving to be derived,
        // with its dominators measured against C''s node order -- that is what turns p.55's
        // mirrored dominator into the ordinary one.
        TwoLevelAnalysis ap = restrictToRegionII(a, cp.nodes, R);
        {
          const vector<int> domp = dominatorsToward(B.g, ap);
          for (int b = 0; b < (int)ap.blocks.size(); b++) ap.blocks[b].dominator = domp[b];
        }

        // The boundaries came from the parent's analysis; C' reads them mirrored (p.55). Lemma
        // 1(1) is the arbiter of whether that reading is admissible, and Lemma 5's same-block
        // case is proved from it, so assert it here rather than discovering a violation later as
        // a crossing.
        checkLemma1Part1(B.g, ap, "C'");
        int rootColourII = -1;
        {
          const int parentOfR = a.blocks[R].parent;
          CHECK(parentOfR >= 0, "Case 3: R=%d has no parent in T", R);
          CHECK(parentOfR < (int)tPrimeColours.size() && tPrimeColours[parentOfR] >= 0,
                "Case 3: the T' call left R's parent %d uncoloured", parentOfR);
          auto [k3r, k4r] = otherColors(ctx.c1, ctx.c2);
          rootColourII = (tPrimeColours[parentOfR] == k3r) ? k4r : k3r;
        }

        CPrimeExceptions cpExc;
        cpExc.alreadyPlaced = ap.firstInnerNode;     // (i) omit u, already laid out
        {
          // (ii) "in Rule 1, we give to the root block R color opposite to that of its parent
          // in T." The parent's colour was fixed by the T' call above; c3/c4 are the pages
          // that are neither c1 nor c2 of the enclosing cycle C.
          cpExc.rootBlockColor = rootColourII;
        }
        // "To expand C' we will first add to it the chords", then the same dispatch: C'
        // reaches Case 1 or Case 2 on its own terms.
        GcDecomposition gcp = decomposeGc(B.g, cp.nodes);

        // The closure IS always fictitious here, and that is a consequence of the
        // construction rather than an accident of the sample: K is chordless (asserted in
        // `decomposeGc`), and Case 3 means l > s+1, so v_s and v_l are non-consecutive
        // nodes of K. An edge (v_s,v_l) would therefore be a chord of K, which cannot
        // exist. p.55's "Imagine that there is an edge (v_s, v_l)... this edge does not
        // exist" is exactly that fact.
        {

          CHECK(cp.frameFictitiousClosure,
                "Case 3: C''s closing edge (%d,%d) exists in G, but K is chordless and "
                "l=%d > s+1=%d makes v_s and v_l non-consecutive on K, so such an edge "
                "would be a chord of K. p.55 says the edge 'does not exist'.",
                cp.nodes.front(), cp.nodes.back(), l_idx, s_idx + 1);

        }
        dispatchStep1a(B, cp, gcp, ap, children, cpExc);

      }
    }
  }
}

// O1 and O2 (p.50) are the OUTPUT constraints -- what EXPAND promises its caller, as
// against P1-P6 which are what it demands. §4 proves both, so a violation is a defect
// here. Checked before recursing, so the cycle named is the one whose Step 1a is at
// fault rather than a descendant.
static void expandOutputChecks(Builder& B, const CycleContext& ctx,
                               const vector<CycleContext>& children) {

  // O1: "EXPAND(C) will lay out the nodes inside C in... the reserved space of C." The
  // reserved space lies strictly between C's extreme nodes, so every vertex this call
  // placed must sit inside that span, and the new cycles must occupy disjoint intervals
  // (p.51: "the latter cycles occupy DISJOINT INTERVALS (except for their endpoints)").
  {
    const int rFirst = B.spine.rank(ctx.nodes.front());
    const int rLast = B.spine.rank(ctx.nodes.back());
    const int loC = min(rFirst, rLast), hiC = max(rFirst, rLast);
    const set<int> onC(ctx.nodes.begin(), ctx.nodes.end());
    for (int v : B.placedHere) {
      const int rv = B.spine.rank(v);
      CHECK(rv > loC && rv < hiC,
            "O1 violated: vertex %d placed by cycle %s sits at rank %d, outside C's own "
            "span [%d,%d] -- it is not in the reserved space of C",
            v, to_string(ctx.nodes).c_str(), rv, loC, hiC);
    }
    // p.51's partition, checked as stated: "every node inside C is either laid out in Step 1a,
    // or is in the interior of exactly one new cycle and thus is laid out when this cycle is
    // expanded." That is about C's INTERIOR, not about spine spans -- a block cycle's leader is
    // a cutvertex the parent owns, placed in a different gap from the block's other vertices,
    // so spans legitimately overlap and a span-disjointness test rejects valid layouts.

    // The interiors are computed from the plane, the same way `analyzeTwoLevelRaw` does it:
    // remove the cycle's own nodes and take the components that do not reach the graph's outer
    // face. Quadratic per cycle, which this file's other checks already are.
    {
      set<int> outerFaceIds;
      for (auto v : B.g.outerFace.vertices) outerFaceIds.insert(v->index);
      auto interiorOf = [&](const vector<int>& cyc) {
        const set<int> onCyc(cyc.begin(), cyc.end());
        set<int> visited, interior;
        for (auto vp : B.g.vertices) {
          const int s0 = vp->index;
          if (onCyc.count(s0) || visited.count(s0)) continue;
          vector<int> comp, stack = {s0};
          visited.insert(s0);
          bool outside = false;
          while (!stack.empty()) {
            const int u = stack.back(); stack.pop_back();
            comp.push_back(u);
            if (outerFaceIds.count(u)) outside = true;
            for (Vertex* nb : B.g.vertices[u]->neighbors()) {
              const int x = nb->index;
              if (onCyc.count(x) || visited.count(x)) continue;
              visited.insert(x);
              stack.push_back(x);
            }
          }
          if (!outside) interior.insert(comp.begin(), comp.end());
        }
        return interior;
      };
      const set<int> interiorC = interiorOf(ctx.nodes);
      const set<int> placed(B.placedHere.begin(), B.placedHere.end());
      map<int, int> covered;
      for (int v : interiorC) covered[v] = placed.count(v) ? 1 : 0;
      for (const auto& child : children)
        for (int v : interiorOf(child.nodes)) {
          // A child's interior lies inside C's, so anything else means the child is not a new
          // cycle of C.
          CHECK(interiorC.count(v),
                "O1 violated: vertex %d is inside new cycle %s but not inside C=%s", v,
                to_string(child.nodes).c_str(), to_string(ctx.nodes).c_str());
          covered[v]++;
        }
      for (int v : interiorC)
        CHECK(covered[v] == 1,
              "p.51's partition violated: vertex %d of C=%s's interior is accounted for %d "
              "times -- it must be laid out by Step 1a or inside exactly one new cycle", v,
              to_string(ctx.nodes).c_str(), covered[v]);
    }
    // O2: "all (new) edges incident to the leader receive color c0" (p.50), with no
    // exception. P4's "except possibly for the edge (1,p)" is about C's colouring on
    // ENTRY, so it does not license a NEW leader-incident edge to hold another colour --
    // and the long edge cannot be new at all: P4 has it coloured already, and O2 makes it
    // the caller's. So assert this call did not claim it, rather than skipping it.
    const int leader = ctx.nodes.front(), farEnd = ctx.nodes.back();
    const auto longEdge = make_pair(min(leader, farEnd), max(leader, farEnd));
    CHECK(!B.colouredHere.count(longEdge),
          "O2 violated: cycle %s coloured its own long edge (%d,%d), which P4 has coloured "
          "on entry and O2 leaves to the caller",
          to_string(ctx.nodes).c_str(), longEdge.first, longEdge.second);
    for (const auto& e : B.colouredHere) {
      if (e.first != leader && e.second != leader) continue;
      CHECK(B.page.at(e) == ctx.c0,
            "O2 violated: cycle %s coloured leader-incident edge (%d,%d) with page %d, not "
            "the leader's colour c0=%d",
            to_string(ctx.nodes).c_str(), e.first, e.second, B.page.at(e), ctx.c0);
    }
  }
}

}  // namespace

Result fourPageEmbedding(const PlanarGraph& graph, int verbose) {
  CHECK(graph.numberOfVertices() >= 3, "graph too small");
  CHECK(graph.isMaximal(), "input must be a MAXIMAL planar graph (m = 3n-6)");

  Builder B(graph, verbose);
  B.level = computeLevels(B.g);
  int maxLevel = *max_element(B.level.begin(), B.level.end());
  LOG_IF(verbose >= 2, "peeled into %d level(s)", maxLevel + 1);

  // Top level (p.50): "We lay out the nodes of C, say in clockwise order, pick the
  // first node as the leader, and color its incident edges with an arbitrary color
  // c0. We let the turning point m be the last node, pick arbitrarily colors c1, c2,
  // and call EXPAND(C)."
  vector<int> outer;
  for (auto v : B.g.outerFace.vertices) outer.push_back(v->index);
  CHECK((int)outer.size() == 3, "expected triangular outer face, got %d",
        (int)outer.size());

  for (int v : outer) B.spine.pushBack(v);

  CycleContext ctx;
  ctx.nodes = outer;
  ctx.m = (int)outer.size() - 1;  // m == p: single zone, no border
  // Top-level colors. Yannakakis: leader color c0, first color c1 (!= c0),
  // second color c2 (may equal c0), and the level-1 machinery uses the other
  // two colors c3,c4 = {0..3}\{c1,c2}. Choose c2 == c0 so that {c3,c4} are the
  // two pages disjoint from c0 and c1 -- otherwise c3 could collide with c0 and
  // level-1 (c3) edges would share the leader/level-0 page (c0). With c0=0,
  // c1=1, c2=0 we get {c3,c4} = {2,3}: four roles -> distinct pages as needed.
  ctx.c0 = 0;              // leader's color
  ctx.c1 = 1;              // first color (c1 != c0)
  ctx.c2 = 0;              // second color (== c0, allowed by P5)
  ctx.cyclePath = "top";
  ctx.peelDepth = 0;
  // Only the LEADER's edges, per P4: "Among the edges connecting nodes of the cycle
  // C, only the edges incident to the leader are colored in L." The remaining short
  // edge (v_2,v_3) is coloured by Step 1a, which owns it -- colouring it here too
  // would be two rules claiming one edge, and with c2 != c0 they would disagree.

  {
    PagePlan tp;
    tp.open(B.page);
    for (int i = 1; i < 3; i++)
      tp.assign(outer[0], outer[i], ctx.c0, "topLeaderEdge", "top-leader-level0");

    applyPagePlan(B, tp);
  }

  expand(B, ctx);

  // Extract the embedding on the ORIGINAL vertices only. Fictitious vertices
  // (index >= nOrig) are dropped from the order; their incident edges are not
  // original edges and are ignored.
  Result emb(ResultCode::SAT);
  vector<int> position;
  map<pair<int, int>, int> page;
  int numPages = 0;
  for (int v : B.spine.seq)
    if (!B.isFictitious(v)) emb.order.push_back(v);
  position.assign(B.nOrig, -1);
  for (int i = 0; i < (int)emb.order.size(); i++) position[emb.order[i]] = i;
  for (auto& kv : B.page) {
    if (!B.isFictitious(kv.first.first) && !B.isFictitious(kv.first.second)) {
      page[kv.first] = kv.second;
      numPages = max(numPages, kv.second + 1);
    }
  }
  // Check the final layout independently of the local cycle checks: every original vertex occurs
  // exactly once, positions invert the order, every original edge has one page in [0,3], no same-
  // page edges cross, and no fictitious vertices or edges are returned.
  {
    CHECK((int)emb.order.size() == B.nOrig,
          "Final layout: the layout has %d of the %d original vertices", (int)emb.order.size(), B.nOrig);
    {
      set<int> seen;
      for (int v : emb.order) {
        CHECK(v >= 0 && v < B.nOrig,
              "Final layout: the order contains %d, which is not an original vertex of [0,%d)", v,
              B.nOrig);
        CHECK(seen.insert(v).second,
              "Final layout: original vertex %d appears more than once in the order", v);
      }
    }
    for (int v = 0; v < B.nOrig; v++)
      CHECK(position[v] >= 0, "Final layout: original vertex %d was never placed on the spine", v);
    // (2) `position` IS THE INVERSE OF `order`, in both directions. Every consumer -- including
    // the crossing test below -- reads positions rather than the order, so a disagreement
    // between the two would silently validate a different layout than the one returned.
    CHECK((int)position.size() == B.nOrig,
          "Final layout: position has %d entries for %d original vertices", (int)position.size(),
          B.nOrig);
    for (int i = 0; i < (int)emb.order.size(); i++)
      CHECK(position[emb.order[i]] == i,
            "Final layout: order[%d] = %d but position[%d] = %d, so position is not the inverse of order",
            i, emb.order[i], emb.order[i], position[emb.order[i]]);
    for (int v = 0; v < B.nOrig; v++)
      CHECK(position[v] >= 0 && position[v] < (int)emb.order.size() &&
                emb.order[position[v]] == v,
            "Final layout: position[%d] = %d does not point back at %d in the order", v,
            position[v], v);
    // (3) EVERY ORIGINAL EDGE HAS EXACTLY ONE PAGE, and the returned map holds NOTHING ELSE. The
    // `page` map is keyed by the normalised pair, so "exactly one" is the presence of every original
    // edge plus the absence of any non-original key -- which is also (6)'s fictitious-edge half.
    {
      set<pair<int, int>> originalKeys;
      for (auto& e : graph.extractEdgesId()) {
        const auto key = make_pair(min(e.first, e.second), max(e.first, e.second));
        originalKeys.insert(key);
        CHECK(page.count(key), "Final layout: original edge (%d,%d) was never assigned a page",
              e.first, e.second);
      }
      for (const auto& kv : page)
        CHECK(originalKeys.count(kv.first),
              "Final layout: the returned embedding pages (%d,%d), which is not an edge of the input "
              "graph -- only original edges may appear", kv.first.first, kv.first.second);
      CHECK(page.size() == originalKeys.size(),
            "Final layout: the embedding pages %d edge(s) for %d original edge(s)",
            (int)page.size(), (int)originalKeys.size());
    }
    // (4) EVERY PAGE IS IN [0,3]. Stated per edge: `numPages <= 4` below is a maximum and would
    // accept a negative page, which would then index a page that does not exist.
    for (const auto& kv : page)
      CHECK(kv.second >= 0 && kv.second <= 3,
            "Final layout: edge (%d,%d) is on page %d, outside the four pages [0,3]", kv.first.first,
            kv.first.second, kv.second);
    // (6) NO FICTITIOUS VERTEX OR EDGE IS RETURNED. p.39's a' is an artefact of the construction,
    // so it must not reach the caller: neither in the order, nor as a position, nor as a page key.
    // The extraction above filters them; this asserts the filter worked rather than trusting it.
    for (int v : emb.order)
      CHECK(!B.isFictitious(v),
            "Final layout: fictitious vertex %d (>= nOrig = %d) appears in the returned order", v,
            B.nOrig);
    for (const auto& kv : page)
      CHECK(!B.isFictitious(kv.first.first) && !B.isFictitious(kv.first.second),
            "Final layout: the returned embedding pages (%d,%d), which touches a fictitious vertex "
            "(nOrig = %d)", kv.first.first, kv.first.second, B.nOrig);
    const vector<pair<int, int>> edges = graph.extractEdgesId();
    for (size_t i = 0; i < edges.size(); i++)
      for (size_t j = i + 1; j < edges.size(); j++) {
        const auto ki = make_pair(min(edges[i].first, edges[i].second),
                                  max(edges[i].first, edges[i].second));
        const auto kj = make_pair(min(edges[j].first, edges[j].second),
                                  max(edges[j].first, edges[j].second));
        if (page.at(ki) != page.at(kj)) continue;
        // (5) NO TWO EDGES ON ONE PAGE CROSS. The whole-embedding statement: §D is per-cycle, so it
        // cannot see a collision between edges coloured by two different cycles.
        CHECK(!edgesCross(position[ki.first], position[ki.second],
                          position[kj.first], position[kj.second]),
              "Final layout: edges (%d,%d) and (%d,%d), both on page %d, cross", ki.first, ki.second,
              kj.first, kj.second, page.at(ki));
      }
    CHECK(numPages <= 4, "Final layout: the layout uses %d pages", numPages);
  }

  // Rule and cycle behind every colour, for attributing a crossing to the two rules that
  // produced it. -verbose=5 only; it is a diagnostic, not part of the construction.
  if (verbose >= 5)
    for (auto& kv : B.provenance)
      LOG("PROV (%d,%d) %s", kv.first.first, kv.first.second, kv.second.c_str());
  // Result uses the caller's edge order, independently of the working graph's
  // augmented edges and the endpoint-keyed construction map.
  for (const auto& edge : graph.extractEdgesId())
    emb.pages.push_back({page.at(edge)});
  emb.pageTypes.assign(4, true);
  emb.pageNames.assign(4, "stack");
  return emb;
}

