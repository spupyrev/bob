#!/usr/bin/env bash

set -uo pipefail

ROOT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BOB="${1:-$ROOT_DIR/build/bob}"
TIMEOUT_SECONDS="${BOB_TEST_TIMEOUT_SECONDS:-5}"
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

run_expect_all "three-stack layout" "solving SAT model" "order:" -- \
  "$BOB" -i="$ROOT_DIR/graphs/graph.dot" -stacks=3 -verbose=1

run_expect_all "two-stack obstruction" "solving SAT model" "layout does not exist" -- \
  "$BOB" -i="$ROOT_DIR/graphs/graph.dot" -stacks=2 -verbose=1

run_expect_all "two-queue layout" "solving SAT model" "order:" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/k33.dot" -queues=2 -verbose=1

run_expect_all "one-queue obstruction" "solving SAT model" "layout does not exist" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/k33.dot" -queues=1 -verbose=1

run_expect_all "six-track layout" "solving SAT model" "track 5:" -- \
  "$BOB" -i="$ROOT_DIR/graphs/weakly_6tracks.gml" -tracks=6 -verbose=1

run_expect_all "five-track obstruction" "solving SAT model" "layout does not exist" -- \
  "$BOB" -i="$ROOT_DIR/graphs/weakly_6tracks.gml" -tracks=5 -verbose=1

run_expect_all "tree page" "solving SAT model" "order:" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/tree.dot" -stacks=1 -trees=true -verbose=1

run_expect_all "cycle is not a tree page" "solving SAT model" "layout does not exist" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/cycle.dot" -stacks=1 -trees=true -verbose=1

run_expect_all "Satsuma preprocessing" "applying Satsuma" "order:" -- \
  "$BOB" -i="$ROOT_DIR/tests/data/k33.dot" -queues=2 -satsuma -verbose=1

printf 'All %d tests passed.\n' "$PASS_COUNT"
