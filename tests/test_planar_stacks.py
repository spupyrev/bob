#!/usr/bin/env python3
"""Independent checks of the public four-page pipeline and its serialized output."""
import argparse
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

def run(binary, *args, succeeds=True):
    p = subprocess.run([str(binary), *args], text=True, capture_output=True, timeout=120)
    if (p.returncode == 0) != succeeds:
        raise AssertionError(f'{args}: exit {p.returncode}\n{p.stderr[-6000:]}')
    return p.stdout

def graph_data(text):
    lines = text.splitlines()
    n, m = map(int, lines[0].split())
    edges = set()
    for line in lines[1:]:
        v, adj = line.split()
        for w in ([] if adj == '-' else adj.split(',')):
            edges.add(tuple(sorted((int(v), int(w)))))
    assert len(edges) == m
    return n, edges

def check(text, n, expected):
    lines = text.splitlines()
    assert lines[0] == f'yannakakis4 {n} {len(expected)}'
    tag, *order = lines[1].split()
    order = list(map(int, order))
    assert tag == 'order' and sorted(order) == list(range(n))
    rank = {v: i for i, v in enumerate(order)}
    seen, pages = set(), [[] for _ in range(4)]
    for line in lines[2:]:
        tag, u, v, page = line.split()
        u, v, page = int(u), int(v), int(page)
        assert tag == 'edge' and 0 <= u < v < n and 0 <= page < 4
        assert (u, v) not in seen
        seen.add((u, v))
        pages[page].append(sorted((rank[u], rank[v])))
    assert seen == expected
    for page in pages:
        for a, b in page:
            for c, d in page:
                assert not a < c < b < d, f'crossing: {a,b,c,d}'

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, default=ROOT / 'build/planar_stacks')
    args = parser.parse_args()
    binary = args.binary.resolve()
    families = ['max-planar', 'random-p3t', 'complete-p3t', 'partial-p3t-connected',
                'partial-p3t-2connected', 'planar-cubic', '4connected', 'outerplanar-max',
                'path', 'star', 'matching']
    count = 0
    with tempfile.TemporaryDirectory(prefix='four-page-io-') as directory:
        path = Path(directory) / 'input.edges'
        for family in families:
            for seed in range(3):
                common = [f'-graph-type={family}', '-n=40', f'-seed={seed}']
                graph = run(binary, *common, '-generate')
                n, edges = graph_data(graph)
                path.write_text(graph)
                layout = run(binary, f'-i={path}', '-o=-')
                check(layout, n, edges)
                # Also check the generated route (it may designate a different outer face).
                check(run(binary, *common, '-o=-'), n, edges)
                count += 1
        # Triangulations exercising mirrored frames, turning points and recursive cases.
        regressions = [
            (3, 0), (4, 0), (6, 0), (8, 0), (8, 3), (8, 5),
            (8, 6), (8, 8), (8, 15), (8, 17), (10, 26), (10, 53),
            (10, 58), (12, 2), (12, 3), (12, 5), (12, 8), (12, 14),
            (12, 41), (14, 14), (14, 19), (14, 20), (16, 1), (16, 8),
            (16, 12), (16, 79), (18, 15), (20, 0), (20, 21), (20, 70),
            (24, 10), (24, 14), (24, 51), (24, 142), (30, 5), (30, 11),
            (30, 21), (30, 65), (30, 88), (30, 98), (40, 30), (60, 0),
            (60, 11), (60, 23), (60, 40), (100, 0), (100, 3), (100, 5),
            (100, 16), (100, 25), (100, 29), (100, 35), (100, 41), (100, 67),
            (100, 88), (100, 95), (300, 1),
        ]
        for size, seed in regressions:
            common = [f'-n={size}', f'-seed={seed}']
            n, edges = graph_data(run(binary, *common, '-generate'))
            layout = run(binary, *common, '-o=-')
            check(layout, n, edges)
        # Two nontrivial components with different local IDs, plus an isolate.
        base = run(binary, '-generate', '-n=12', '-seed=41')
        rows = base.splitlines()
        nbase, mbase = map(int, rows[0].split())
        merged = [f'{2*nbase+1} {2*mbase}']
        for offset in (0, nbase):
            for row in rows[1:]:
                v, adj = row.split()
                merged.append(f'{int(v)+offset} ' + ','.join(str(int(w)+offset) for w in adj.split(',')))
        merged.append(f'{2*nbase} -')
        graph = '\n'.join(merged) + '\n'
        path.write_text(graph)
        n, edges = graph_data(graph)
        check(run(binary, f'-i={path}', '-o=-'), n, edges)
        for graph in ['1 0\n0 -\n', '2 1\n0 1\n1 0\n',
                      '6 3\n0 1,2\n1 2,0\n2 0,1\n3 -\n4 -\n5 -\n']:
            path.write_text(graph)
            n, edges = graph_data(graph)
            check(run(binary, f'-i={path}', '-o=-'), n, edges)
        empty = Path(directory) / 'empty.edges'
        empty.write_text('0 0\n')
        run(binary, f'-i={empty}', succeeds=False)
        output = Path(directory) / 'saved.layout'
        run(binary, f'-i={path}', f'-o={output}')
        saved = output.read_text()
        run(binary, f'-i={path}', f'-o={output}', succeeds=False)
        assert output.read_text() == saved
        assert saved == run(binary, f'-i={path}', '-o=-')
        run(binary, '-queues=4', succeeds=False)
        run(binary, '-generate', '-test', succeeds=False)
        run(binary, '-action=unknown', succeeds=False)
        run(binary, '-n=0', succeeds=False)
        run(binary, '-test', succeeds=False)
        gml = Path(directory) / 'triangle.gml'
        gml.write_text('graph [\n' + ''.join(
            f'node [\nid {v}\ngraphics [\nx {x}\ny {y}\n]\n]\n'
            for v, x, y in [(0, 0, 0), (1, 1, 0), (2, 0, 1)]) + ''.join(
            f'edge [\nsource {u}\ntarget {v}\n]\n' for u, v in [(0, 1), (0, 2), (1, 2)]) + ']\n')
        check(run(binary, f'-i={gml}', '-o=-'), 3, {(0, 1), (0, 2), (1, 2)})
    print(f'PASS {count} generated/input pairs and {len(regressions)} regressions, tiny/disconnected graphs, GML and output validation')

if __name__ == '__main__':
    main()
