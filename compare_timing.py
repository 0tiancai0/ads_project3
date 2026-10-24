#!/usr/bin/env python3
"""Run both C solvers on identical deterministic inputs; parse their CPU timers."""
import argparse
import re
import statistics
import subprocess


def cases():
    yield 'single_odd', [[1]]
    yield 'capacity_failure', [[4, 4]]
    yield 'empty_20', [[0] * 20 for _ in range(20)]
    for size in (10, 30, 50):
        yield f'full_grid_{size}', [
            [int(r > 0) + int(r + 1 < size) + int(c > 0) + int(c + 1 < size)
             for c in range(size)] for r in range(size)]
    for size in (10, 30, 50):
        yield f'matching_{size}', [[1] * size for _ in range(size)]
    grid = [[0] * 50 for _ in range(50)]
    for r, c in ((0, 0), (0, 49), (49, 0), (49, 49)):
        grid[r][c] = 2
    yield 'sparse_corners_50', grid


def validate(grid, answer):
    if answer.strip() == 'No Solution':
        return False
    points = {(r + 1, c + 1): value for r, row in enumerate(grid)
              for c, value in enumerate(row) if value}
    rows = [list(map(int, line.split())) for line in answer.splitlines()]
    assert len(rows) == len(points), 'wrong answer length'
    selected = {}
    for row in rows:
        assert len(row) == 6
        r, c, *flags = row
        assert (r, c) in points and (r, c) not in selected
        assert all(f in (0, 1) for f in flags)
        assert sum(flags) == points[r, c], 'wrong degree'
        selected[r, c] = flags
    directions = ((-1, 0), (1, 0), (0, -1), (0, 1))
    occupied = [set(), set()]
    for (r, c), flags in selected.items():
        for d, flag in enumerate(flags):
            if not flag:
                continue
            dr, dc = directions[d]
            rr, cc = r + dr, c + dc
            interior = []
            while (rr, cc) not in points:
                assert 1 <= rr <= len(grid) and 1 <= cc <= len(grid[0])
                interior.append((rr, cc))
                rr, cc = rr + dr, cc + dc
            assert selected[rr, cc][d ^ 1], 'asymmetric edge'
            occupied[d // 2].update(interior)
    assert not occupied[0] & occupied[1], 'illegal crossing'
    return True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('prog')
    parser.add_argument('mrv')
    parser.add_argument('--repeat', type=int, default=5)
    parser.add_argument('--timeout', type=float, default=10)
    args = parser.parse_args()
    if args.repeat < 1:
        parser.error('--repeat must be positive')
    print('| case | prog total ms | MRV total ms | prog nodes | MRV nodes |')
    print('|---|---:|---:|---:|---:|')
    for name, grid in cases():
        data = f'{len(grid)} {len(grid[0])}\n' + '\n'.join(' '.join(map(str, row)) for row in grid) + '\n'
        results = []
        statuses = []
        for binary in (args.prog, args.mrv):
            times, nodes = [], '-'
            try:
                for _ in range(args.repeat):
                    run = subprocess.run([binary], input=data, text=True, capture_output=True,
                                         timeout=args.timeout, check=True)
                    statuses.append(validate(grid, run.stdout))
                    times.append(float(re.search(r'total_ms=([\d.]+)', run.stderr)[1]))
                    stat = re.search(r'nodes=(\d+)', run.stderr)
                    nodes = stat[1] if stat else '-'
                results.append((f'{statistics.median(times):.6f}', nodes))
            except subprocess.TimeoutExpired:
                results.append(('TIMEOUT', '-'))
        assert len(set(statuses)) <= 1, f'{name}: solver status mismatch'
        if statuses:
            assert statuses[0] == (name not in ('single_odd', 'capacity_failure'))
        print(f'| {name} | {results[0][0]} | {results[1][0]} | {results[0][1]} | {results[1][1]} |')


if __name__ == '__main__':
    main()
