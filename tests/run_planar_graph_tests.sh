#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
if [[ -d "$root/src/combinatorial" ]]; then
  planar="$root/src/combinatorial"
  common="$root/src/bob"
else
  planar="$root/bob"
  common="$root/bob"
fi
# Build only the graph and parser code; no SAT solver is needed.
build="$root/build/planar_graph_tests"
mkdir -p "$build"
"${CXX:-g++}" -std=c++17 -O0 -g -I"$root/src" -I"$planar" -I"$common" \
  "$root/tests/test_planar_graph.cpp" \
  "$planar/planar_graph.cpp" "$planar/planar_graph_io.cpp" \
  "$common/common.cpp" "$common/graph_algorithms.cpp" \
  "$common/dot_parser.cpp" "$common/gml_parser.cpp" \
  -o "$build/test_planar_graph"
"$build/test_planar_graph" "$build/input.gml"
