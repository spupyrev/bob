#pragma once

#include "planar_graph.h"
#include "bob/glucoseMain.h"

// FOUR-PAGE ALGORITHM: Yannakakis 1989 §3, implemented directly from that paper.
//   M. Yannakakis, "Embedding planar graphs in four pages", JCSS 38(1):36-67, 1989
//   (cited Y1989).  https://doi.org/10.1016/0022-0000(89)90032-9
// A few rules are disambiguated against the extended abstract: M. Yannakakis, "Four
// pages are necessary and sufficient for planar graphs", STOC 1986, pp. 104-108.
//   https://doi.org/10.1145/12130.12141
// Construction: Y1989 §§2–3; correctness proof: §4.

// Maximal plane input with a designated triangular outer face. The input is not
// modified. Construction assertions and final layout checks always run.
// Result::pages is indexed by graph.extractEdgesId(); all page types are stacks.
Result fourPageEmbedding(const PlanarGraph& graph, int verbose = 0);
