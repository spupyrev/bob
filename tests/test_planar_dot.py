#!/usr/bin/env python3
"""Check DOT-to-embedding-to-layout conversion independently of page assignment."""
import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    parser.add_argument('--mode', choices=['stacks', 'queues'], required=True)
    args = parser.parse_args()
    binary = str(args.binary.resolve())
    bound = 4 if args.mode == 'stacks' else 33
    options = ['-checkAll'] if args.mode == 'stacks' else ['-queues=33']

    def run(*flags, success=True):
        result = subprocess.run([binary, *flags], capture_output=True, text=True, timeout=120)
        assert (result.returncode == 0) == success, (flags, result.returncode, result.stderr[-5000:])
        return result

    def verify(text, n, expected):
        lines = text.splitlines()
        algorithm = 'yannakakis4' if args.mode == 'stacks' else 'pps33'
        assert lines[0] == f'{algorithm} {n} {len(expected)}'
        tag, *order = lines[1].split()
        order = list(map(int, order))
        assert tag == 'order' and sorted(order) == list(range(n))
        ranks = {v: i for i, v in enumerate(order)}
        found = set()
        pages = [[] for _ in range(bound)]
        for line in lines[2:]:
            tag, u, v, page = line.split()
            u, v, page = int(u), int(v), int(page)
            assert tag == 'edge' and 0 <= u < v < n and 0 <= page < bound
            assert (u, v) not in found
            found.add((u, v))
            pages[page].append(sorted((ranks[u], ranks[v])))
        assert found == expected
        for page in pages:
            for a, b in page:
                for c, d in page:
                    assert not (a < c < b < d if args.mode == 'stacks' else a < c < d < b)

    def dot(n, edges):
        return 'graph G {\n' + ''.join(f'"v{v}";\n' for v in range(n)) + ''.join(
            f'"v{u}" -- "v{v}";\n' for u, v in sorted(edges)) + '}\n'

    count = 0
    with tempfile.TemporaryDirectory(prefix='planar-dot-') as tmp:
        path = Path(tmp) / 'input.dot'
        def check(graph, n, edges):
            nonlocal count
            path.write_text(graph)
            result = run(f'-i={path}', '-o=-', *options)
            verify(result.stdout, n, edges)
            count += 1
            return result

        check('graph G { only; }', 1, set())
        check('graph G { a -- b }', 2, {(0, 1)})  # no final semicolon
        check('graph G { a -- b -- c; }', 3, {(0, 1), (1, 2)})
        check('graph G { "a--b" -- "c->d"; }', 2, {(0, 1)})
        check('digraph G { a -> b; b -> c; }', 3, {(0, 1), (1, 2)})
        result = check('graph G { a -- b; a [label="first {vertex}"]; b [label="second"]; }',
                       2, {(0, 1)})
        assert 'first {vertex}' in result.stderr and 'second' in result.stderr
        check(dot(9, {(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)}),
              9, {(0,1),(0,2),(1,2),(3,4),(3,5),(4,5),(5,6)})
        check(dot(5, {(0,1),(1,2),(2,3),(3,4),(0,4)}), 5,
              {(0,1),(1,2),(2,3),(3,4),(0,4)})
        for family in ('max-planar', 'random-p3t', 'planar-cubic', 'partial-p3t-connected', 'star'):
            for seed in range(5):
                text = run('-generate', f'-graph-type={family}', '-n=40', f'-seed={seed}').stdout
                rows = text.splitlines()
                n, m = map(int, rows[0].split())
                edges = set()
                for row in rows[1:]:
                    u, adj = row.split()
                    for v in ([] if adj == '-' else adj.split(',')):
                        edges.add(tuple(sorted((int(u), int(v)))))
                assert len(edges) == m
                check(dot(n, edges), n, edges)
        k5 = {(u,v) for u in range(5) for v in range(u+1,5)}
        k33 = {(u,v) for u in range(3) for v in range(3,6)}
        subdivided = set()
        for w, (u,v) in enumerate(sorted(k33), start=6):
            subdivided.update({(u,w),(v,w)})
        for n, edges in [(5,k5),(6,k33),(15,subdivided), (20,k33)]:
            path.write_text(dot(n, edges))
            result = run(f'-i={path}', '-o=-', success=False)
            assert 'nonplanar' in result.stderr and not result.stdout
        for invalid in ['graph G { a -- a; }', 'graph G { a -- b; b -- a; }',
                        'graph G { a -- b;', 'not a graph']:
            path.write_text(invalid)
            assert not run(f'-i={path}', '-o=-', success=False).stdout
    print(f'PASS {args.mode}: {count} DOT layouts, labels, disconnected inputs, nonplanar/invalid rejection')

if __name__ == '__main__':
    main()
