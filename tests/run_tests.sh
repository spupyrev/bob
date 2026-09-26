#!/usr/bin/env bash

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BOB="${1:-$ROOT_DIR/build/bob}"
TIMEOUT_SECONDS="${BOB_TEST_TIMEOUT_SECONDS:-20}"
PASS_COUNT=0

run_expect_all() {
  local name="$1"
  shift
  local -a patterns=()

  while [[ $# -gt 0 && "$1" != "--" ]]; do
    patterns+=("$1")
    shift
  done
  shift

  local output
  output="$(timeout "${TIMEOUT_SECONDS}s" "$@" 2>&1)"
  local status=$?

  if [[ $status -ne 0 ]]; then
    printf 'FAIL: %s (exit status %d)\n%s\n' "$name" "$status" "$output" >&2
    exit 1
  fi

  local pattern
  for pattern in "${patterns[@]}"; do
    if ! grep -Fq -- "$pattern" <<<"$output"; then
      printf 'FAIL: %s (missing output: %s)\n%s\n' "$name" "$pattern" "$output" >&2
      exit 1
    fi
  done

  PASS_COUNT=$((PASS_COUNT + 1))
  printf 'PASS: %s\n' "$name"
}

if [[ ! -x "$BOB" ]]; then
  printf 'Solver executable not found: %s\n' "$BOB" >&2
  exit 1
fi

run_expect_all "three-stack layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/graph.dot" -stacks=3 -verbose=1

run_expect_all "two-stack obstruction" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/graph.dot" -stacks=2 -verbose=1

run_expect_all "two-queue layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/k33.dot" -queues=2 -verbose=1

run_expect_all "one-queue obstruction" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/k33.dot" -queues=1 -verbose=1

run_expect_all "six-track layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/weakly_6tracks.gml" -tracks=6 -verbose=1

run_expect_all "five-track obstruction" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/weakly_6tracks.gml" -tracks=5 -verbose=1

run_expect_all "tree page" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/tree.dot" -stacks=1 -constraints=trees -verbose=1

run_expect_all "cycle is not a tree page" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/cycle.dot" -stacks=1 -constraints=trees -verbose=1

run_expect_all "star-forest queues" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/triangle.dot" -queues=2 -constraints=star -verbose=1

run_expect_all "Satsuma preprocessing" "applying Satsuma" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/k33.dot" -queues=2 -satsuma -verbose=1

run_expect_all "fixed-order stack obstruction" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -stacks=1 -fixedOrder=true -verbose=1

run_expect_all "mixed stack-queue layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -stacks=1 -queues=1 -fixedOrder=true -verbose=1

run_expect_all "bounded-twist obstruction" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -twists=1 -fixedOrder=true -verbose=1

run_expect_all "bounded-twist layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -twists=2 -fixedOrder=true -verbose=1

run_expect_all "variable-order RIQUE layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/rique_pattern.dot" -riques=1 -verbose=1

run_expect_all "fixed-order RIQUE obstruction" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/rique_pattern.dot" -riques=1 -fixedOrder=true -verbose=1

run_expect_all "partial vertex order" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -stacks=1 \
  '-node-rel=0 1 2 3' -verbose=1

run_expect_all "admissible edge pages" "return code: 1 (UNSAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -stacks=2 -multi=true \
  -fixedOrder=true '-edge-pages=(0,2):0; (1,3):0' -verbose=1

run_expect_all "mixed-page layout" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/crossing.dot" -mixed-pages=1 -fixedOrder=true -verbose=1

run_expect_all "bounded solver call" "return code: 0 (SAT)" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/triangle.dot" -stacks=1 -timeout=1 -verbose=1

printf 'All %d tests passed.\n' "$PASS_COUNT"
