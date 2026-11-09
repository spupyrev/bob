#!/usr/bin/env python3
"""Check 33- and 48-queue layouts, the 49 alias, and graph/layout I/O.

For each generated graph, check queue budgets by edge type and quotient
queue, and collect coverage of face ownership and auxiliary triangles.
The executable checks construction invariants and every assigned queue.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FAMILIES = (
    'max-planar', 'random-p3t', 'partial-p3t-2connected',
    'partial-p3t-connected', 'planar-cubic', 'outerplanar-max', '4connected',
    'complete-p3t',
)
BOUNDS = {48: (1, 2, 15, 15, 15), 33: (1, 2, 10, 10, 10)}
COVERAGE = re.compile(
    r'auxiliary triangles of K: designated-side=(\d+) wrap-reused=(\d+) wrap-added=(\d+)'
    r'.*?\n.*?owners of faces of K̂: triangles=(\d+) digons=(\d+) monogons=(\d+)'
)
EDGE_TYPES = ('intra-bag/intra-layer', 'intra-bag/inter-layer', 'inter-bag/intra-layer',
              'inter-bag/forward', 'inter-bag/backward')
ALLOCATION = re.compile(
    r'queue allocation: bound=(\d+) '
    + ' '.join(rf'{re.escape(name)}=(\d+)/(\d+)' for name in EDGE_TYPES)
    + r' total=(\d+)/(\d+)'
)
FAMILY = re.compile(
    r'queue family: bound=(\d+) type=(\S+) quotient=Q(\d+) '
    r'edges=(\d+) queues=(\d+) limit=(\d+)'
)


def check_io(binary, algorithms, timeout):
    """Check generated embeddings, both output routes, and disconnected input."""
    def run(*arguments, succeeds=True):
        result = subprocess.run([str(binary), *arguments, '-verbose=0'],
                                capture_output=True, text=True, timeout=timeout)
        if (result.returncode == 0) != succeeds:
            raise SystemExit(f'Unexpected I/O result for {arguments}:\n{result.stderr}')
        return result.stdout

    generated = run('-generate', '-graph-type=max-planar', '-n=4', '-o=-')
    rows = generated.splitlines()
    if rows[0] != '4 6' or len(rows) != 5:
        raise SystemExit('generate did not print a four-vertex plane triangulation')
    adjacency = {}
    for row in rows[1:]:
        vertex, neighbors = row.split()
        adjacency[int(vertex)] = list(map(int, neighbors.split(',')))
    if set(adjacency) != set(range(4)):
        raise SystemExit('generated vertex IDs are incorrect')
    for vertex, neighbors in adjacency.items():
        if set(neighbors) != set(range(4)) - {vertex} or len(neighbors) != 3:
            raise SystemExit('generated K4 adjacency is incorrect')

    # Two degree-three components plus an isolate exercise rotation-preserving
    # component copying, output restriction, and the trivial layout branch.
    expected_edges = set()
    input_rows = ['9 12']
    for offset in (0, 4):
        for vertex in range(4):
            neighbors = [offset + neighbor for neighbor in adjacency[vertex]]
            input_rows.append(f'{offset + vertex} ' + ','.join(map(str, neighbors)))
            for neighbor in neighbors:
                expected_edges.add(tuple(sorted((offset + vertex, neighbor))))
    input_rows.append('8 -')

    def check_layout(text, algorithm):
        lines = text.splitlines()
        if len(lines) != 14 or lines[0] != f'{algorithm} 9 12':
            raise SystemExit(f'Incorrect layout header/length from {algorithm}')
        parts = lines[1].split()
        order = list(map(int, parts[1:]))
        if parts[0] != 'order' or len(order) != 9 or set(order) != set(range(9)):
            raise SystemExit(f'Incorrect vertex order from {algorithm}')
        position = {vertex: rank for rank, vertex in enumerate(order)}
        edges = set()
        queues = {}
        for line in lines[2:]:
            tag, u, v, q = line.split()
            u, v, q = int(u), int(v), int(q)
            if tag != 'edge' or not (0 <= u < v < 9 and 0 <= q < int(algorithm[3:])):
                raise SystemExit(f'Incorrect edge record from {algorithm}')
            if (u, v) in edges:
                raise SystemExit(f'Duplicate output edge from {algorithm}')
            edges.add((u, v))
            queues.setdefault(q, []).append(tuple(sorted((position[u], position[v]))))
        if edges != expected_edges:
            raise SystemExit(f'Output did not preserve input edges for {algorithm}')
        for queue in queues.values():
            for a, b in queue:
                for c, d in queue:
                    if a < c < d < b:
                        raise SystemExit(f'Printed queue contains nesting for {algorithm}')

    with tempfile.TemporaryDirectory(prefix='pps-layout-io-') as temporary:
        directory = Path(temporary)
        graph_path = directory / 'disconnected.adj'
        graph_path.write_text('\n'.join(input_rows) + '\n')
        generated_path = directory / 'generated.adj'
        run('-generate', '-graph-type=max-planar', '-n=4',
            f'-o={generated_path}')
        if generated_path.read_text() != generated:
            raise SystemExit('file/stdout graph generation disagree for a fixed seed')
        for algorithm in algorithms:
            text = run(f'-queues={algorithm[3:]}', f'-i={graph_path}', '-o=-')
            check_layout(text, algorithm)
            screen = subprocess.run(
                [str(binary), f'-queues={algorithm[3:]}', f'-i={graph_path}', '-verbose=0'],
                capture_output=True, text=True, timeout=timeout, check=True)
            if screen.stdout:
                raise SystemExit('default layout display must use stderr, as Bob does')
            records = text.splitlines()
            expected = ['order: [' + ' '.join(records[1].split()[1:]) + ']']
            for page in range(int(algorithm[3:])):
                edges = []
                for record in records[2:]:
                    _, u, v, q = record.split()
                    if int(q) == page:
                        edges.append(f'({u}, {v})')
                expected.append(f'page {page}:' + ''.join(' ' + edge for edge in edges))
            if '\n'.join(expected) + '\n' not in screen.stderr:
                raise SystemExit('screen layout must use Bob order/page formatting')
            if not re.search(r'^max-rainbow: \d+$', screen.stderr, re.MULTILINE):
                raise SystemExit('screen layout is missing queue statistics')
            layout_path = directory / f'{algorithm}.layout'
            run(f'-queues={algorithm[3:]}', f'-i={graph_path}', f'-o={layout_path}')
            saved = layout_path.read_text()
            check_layout(saved, algorithm)
            run(f'-queues={algorithm[3:]}', f'-i={graph_path}',
                f'-o={layout_path}', succeeds=False)
            if layout_path.read_text() != saved:
                raise SystemExit('an existing layout file was overwritten')
        # Read the same disconnected graph through the shared GML parser.
        coordinates = [(0.0, 0.0), (0.3, 0.0), (0.0, 0.3), (0.1, 0.1)]
        gml = ['graph [']
        for vertex in range(9):
            x, y = coordinates[vertex % 4] if vertex < 8 else (2.0, 2.0)
            x += vertex // 4
            gml.append(f'node [\n id {vertex}\n graphics [\n x {x}\n y {y}\n ]\n ]')
        for u, v in sorted(expected_edges):
            gml.append(f'edge [\n source {u}\n target {v}\n ]')
        gml.append(']')
        gml_path = directory / 'disconnected.gml'
        gml_path.write_text('\n'.join(gml) + '\n')
        for algorithm in algorithms:
            check_layout(run(f'-queues={algorithm[3:]}', f'-i={gml_path}', '-o=-'), algorithm)
        invalid_gml = directory / 'no-coordinates.gml'
        invalid_gml.write_text('graph [\nnode [\nid 0\n]\n]\n')
        run(f'-i={invalid_gml}', succeeds=False)
        alias48 = run('-queues=48', f'-i={graph_path}', '-o=-')
        alias49 = run('-queues=49', f'-i={graph_path}', '-o=-')
        check_layout(alias49, 'pps49')
        if alias48.splitlines()[1:] != alias49.splitlines()[1:]:
            raise SystemExit('49 must use the same construction as 48')
        default = run(f'-i={graph_path}', '-o=-')
        if default != run('-queues=33', f'-i={graph_path}', '-o=-'):
            raise SystemExit('default queue bound must be 33')
        run('-queues=42', succeeds=False)
        run('-generate', '-test', succeeds=False)
        run('-action=pps33', succeeds=False)
        run('-generate', '-graph-type=path', '-n=0', succeeds=False)
        run('-generate', '-graph-type=matching', '-n=-1', succeeds=False)
        run('-generate', '-graph-type=4connected', '-n=6', succeeds=False)
    print('PASS generation, input, stdout/file layouts, disconnected graph, and overwrite protection',
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=ROOT / 'build' / 'planar_queues')
    parser.add_argument('--graphs', type=int, default=10)
    parser.add_argument('--vertices', type=int, default=300)
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--algorithms', nargs='+', default=['pps48', 'pps33'],
                        choices=['pps48', 'pps33'])
    parser.add_argument('--families', nargs='+', default=list(FAMILIES), choices=FAMILIES)
    parser.add_argument('--output-dir', type=Path, default=Path('/tmp/pps-layout-results'))
    parser.add_argument('--timeout', type=int, default=180,
                        help='seconds per algorithm/family batch')
    args = parser.parse_args()
    if args.graphs < 1 or args.vertices < 4 or args.vertices % 2:
        parser.error('use a positive graph count and an even vertex count at least 4')
    if args.vertices < 10 and '4connected' in args.families:
        parser.error('the 4connected generator requires a target of at least 10 vertices')
    args.output_dir.mkdir(parents=True, exist_ok=True)
    cases = []
    for algorithm in args.algorithms:
        cases += [(algorithm, family, args.graphs) for family in args.families]
        cases += [(algorithm, family, 1) for family in ('path', 'star', 'matching')]
    totals = [0] * 6
    report = []
    for algorithm, family, count in cases:
        bound = int(algorithm[3:])
        command = [str(args.binary.resolve()), f'-queues={algorithm[3:]}', f'-graph-type={family}',
                   f'-n={args.vertices}', f'-graphs={count}', f'-seed={args.seed}', '-verbose=1']
        log = args.output_dir / f'{algorithm}-{family}-n{args.vertices}-seed{args.seed}.log'
        with log.open('w') as stream:
            try:
                result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT,
                                        timeout=args.timeout, check=False)
            except subprocess.TimeoutExpired:
                raise SystemExit(f'TIMEOUT {algorithm}/{family}; log: {log}')
        output = log.read_text()
        if result.returncode:
            raise SystemExit(f'FAIL {algorithm}/{family}, exit={result.returncode}; log: {log}\n{output[-3000:]}')
        actual_sizes = [tuple(map(int, values)) for values in re.findall(
            r'processed graph \d+/\d+ with \|V\| = (\d+), \|E\| = (\d+)', output)]
        processed = len(actual_sizes)
        if family != '4connected' and any(n != args.vertices for n, _ in actual_sizes):
            raise SystemExit(f'Generator returned the wrong vertex count: {log}')
        rows = [tuple(map(int, row)) for row in COVERAGE.findall(output)]
        # Matching components have at most two vertices and bypass the
        # quotient construction; they exercise only the trivial layout.
        if processed != count or (not rows and family != 'matching'):
            raise SystemExit(f'Incomplete run or missing face-owner coverage: {log}')
        allocations = [tuple(map(int, row)) for row in ALLOCATION.findall(output)]
        expected_allocations = 0 if family == 'matching' else count
        if len(allocations) != expected_allocations:
            raise SystemExit(f'Missing per-type allocation checks: {log}')
        for allocation in allocations:
            actual_bound = allocation[0]
            used = allocation[1:11:2]
            limits = allocation[2:11:2]
            total, total_limit = allocation[11:]
            if (actual_bound != bound or limits != BOUNDS[bound]
                    or any(n > limit for n, limit in zip(used, limits))
                    or total != sum(used) or total_limit != bound or total > bound):
                raise SystemExit(f'Incorrect queue allocation {allocation}: {log}')
        families_checked = [(int(b), EDGE_TYPES.index(t) + 1, *map(int, rest))
                            for b, t, *rest in FAMILY.findall(output)]
        if len(families_checked) != 15 * expected_allocations:
            raise SystemExit(f'Missing individual quotient-queue checks: {log}')
        for start in range(0, len(families_checked), 15):
            group = families_checked[start:start + 15]
            if {(row[1], row[2]) for row in group} != {
                    (edge_type, q) for edge_type in (3, 4, 5) for q in range(5)}:
                raise SystemExit(f'Duplicate or omitted inter-bag family: {log}')
            for actual_bound, edge_type, q, edges, used, limit in group:
                if (actual_bound != bound or limit != (2 if bound == 33 else 3)
                        or used > limit or (used == 0) != (edges == 0)):
                    raise SystemExit(f'Incorrect inter-bag family: {log}')
        coverage = [sum(row[i] for row in rows) for i in range(6)]
        totals = [x + y for x, y in zip(totals, coverage)]
        report.append(dict(algorithm=algorithm, family=family, requested_vertices=args.vertices,
                           actual_sizes=actual_sizes,
                           graphs=count, seed=args.seed, coverage=coverage,
                           allocations=allocations, log=str(log)))
        print(f'PASS {algorithm}/{family}: {count} graphs; faces={sum(coverage[3:])}, '
              f'monogons={coverage[5]}, auxiliary={sum(coverage[:3])}', flush=True)
    payload = dict(cases=report, coverage_columns=['designated_side', 'wrap_reused', 'wrap_added',
                                                  'triangles', 'digons', 'monogons'],
                   coverage=totals)
    (args.output_dir / 'summary.json').write_text(json.dumps(payload, indent=2) + '\n')
    print(f'TOTAL graphs={sum(count for _, _, count in cases)} coverage={totals}', flush=True)
    check_io(args.binary.resolve(), args.algorithms, args.timeout)


if __name__ == '__main__':
    main()
