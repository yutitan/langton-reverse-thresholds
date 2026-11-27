"""Finite checks for signed flux and first-read black requirements, Python 3.10+.

The reverse is an abstract template. A class of an older wake represents
arbitrary available ink on its whole line, not a promise of reachability.
"""
from collections import Counter, defaultdict
from itertools import product

from verify_ant_highway import Ant, inspect_block


def canonical():
    ant = Ant(set())
    for _ in range(9977):
        ant.step()
    okay, drift, reads, forward = inspect_block(ant)
    assert okay and drift == (-2, -2)
    return reads, forward


def rotate(q, n):
    x, y = q
    return ((x, y), (-y, x), (-x, -y), (y, -x))[n % 4]


def axis(a, b):
    assert abs(a[0]-b[0]) + abs(a[1]-b[1]) == 1
    return int(a[0] == b[0])


def reverse_profile(reads, word):
    r0 = min(x-y for x, y in reads)
    def lane(p):
        x, y = p
        return (x-y-r0, x % 2)

    wake_flux = Counter()
    for p, c in zip(reads, word):
        wake_flux[lane(p)] += 1 if c == 'R' else -1
    assert set(wake_flux.values()) == {0, 1}
    wake = {q for q, value in wake_flux.items() if value}

    # Actual positions on the bi-infinite forward template. Invariant checks
    # at all vertices pin down both wraparound edges without a phase choice.
    def vertex(j):
        k, t = divmod(j, 104)
        x, y = reads[t]
        return x-2*k, y-2*k

    for j, n, dx, dy in product(range(104), range(4), range(2), range(2)):
        p = vertex(j)
        inv = axis(vertex(j-1), p) ^ ((p[0]+p[1]) % 2)
        u, w = rotate(vertex(j+1), n), rotate(p, n)
        new = axis(u, w) ^ ((w[0]+w[1]+dx+dy) % 2)
        assert (inv == new) == ((dx+dy) % 2 == (1 ^ (n % 2)))

    profiles = []
    widths = Counter()
    end_gains = []
    for phase in range(104):
        sites = []
        for i in range(104):
            j = 103 - phase - i
            sites.append((vertex(j), 'L' if word[j % 104] == 'R' else 'R'))
        footprint = defaultdict(list)
        for p, c in sites:
            footprint[lane(p)].append(p[0] // 2)
        width = max(max(v)-min(v) for v in footprint.values())
        widths[width] += 1
        assert width <= 3
        observed = []
        for k in range(1, 6):
            first, last, net = {}, {}, Counter()
            for t in range(k):
                for (x, y), c in sites:
                    p = x+2*t, y+2*t
                    assert last.get(p) != c
                    first.setdefault(p, c)
                    last[p] = c
                    net[p] += 1 if c == 'R' else -1
            demand = Counter(lane(p) for p, c in first.items() if c == 'L')
            observed.append(demand)
            assert set(net.values()) <= {-1, 0, 1}
            end_gains.append(sum(n > 0 for n in net.values()))
            assert sum(net.values()) == -12*k
        # For K >= width+1 the only contribution from an additional period
        # is a full interior site, with first turn at the extreme x offset.
        interior = set()
        for z, offsets in footprint.items():
            extreme = max(offsets)
            c = next(c for p, c in sites if lane(p) == z and p[0]//2 == extreme)
            if c == 'L':
                interior.add(z)
        assert interior == wake and observed[4] == observed[3]+Counter(wake)
        profiles.append(observed[:4])
    assert max(end_gains) == 17
    return wake, widths, profiles


def perpendicular(wake):
    # Coordinates with the normal layer origin normalized to zero.
    reps = [(s, s-r) for r, s in wake]
    possible = set()
    for rotation in (1, 3):
        older = [rotate(p, rotation) for p in reps]
        for dx, dy in product(range(4), repeat=2):
            if (dx+dy) % 2:
                continue
            hits = 0
            for x, y in reps:
                for u, v in older:
                    a, b = x-u-dx, y-v-dy
                    hits += a%2 == b%2 == 0 and (a+b)%4 == 0
            possible.add(hits)
    assert possible == {18, 20, 22}
    return possible


def support_unions(wake, lanes, allow_half_turn):
    # Integer bits label the 22 classes read by the target, including those
    # with zero signed flux. Farther shifts miss every target class.
    shifts = {0}
    for half_turn in range(2 if allow_half_turn else 1):
        for k, parity in product(range(-9, 10, 2), range(2)):
            old = {((10-r if half_turn else r)+k, s ^ parity) for r, s in wake}
            shifts.add(sum(1 << i for i, z in enumerate(lanes) if z in old))
    choices = {0}
    for j in range(4):
        yield choices
        choices = {a | b for a in choices for b in shifts}


def weighted_sums(values):
    """Two small lookup tables for querying an arbitrary 22-bit subset."""
    def sums(part):
        result = [0]
        for n in part:
            result.extend(v+n for v in result[:])
        return result
    return sums(values[:11]), sums(values[11:])


def inventory(wake, profiles, both):
    lanes = sorted({(r, p) for r in range(11) for p in range(2)})
    full = (1 << len(lanes))-1
    wake_bits = sum(1 << i for i, z in enumerate(lanes) if z in wake)
    # Phase can change the required initial cells, even with the same flux.
    for j, masks in enumerate(support_unions(wake, lanes, both)):
        uncovered = [full ^ m for m in masks]
        slope = min((m & wake_bits).bit_count() for m in uncovered)
        best = [999] * 4
        best_at_min_slope = 999
        for demands in profiles:
            for k, d in enumerate(demands):
                assert set(d) <= set(lanes)
                lo, hi = weighted_sums([d[z] for z in lanes])
                for m in uncovered:
                    value = lo[m & 2047] + hi[m >> 11]
                    if value < best[k]:
                        best[k] = value
                    if k == 3 and (m & wake_bits).bit_count() == slope:
                        best_at_min_slope = min(best_at_min_slope, value)
        print('tracks', j, 'min slope', slope, 'min required outside for K=1..4',
              best, 'K=4 at min slope', best_at_min_slope)
        yield slope, best, best_at_min_slope


def main():
    wake, widths, profiles = reverse_profile(*canonical())
    print('wake', sorted(wake), 'phase widths', dict(widths),
          'maximum new black cells after a clean stretch', 17)
    print('perpendicular intersections', sorted(perpendicular(wake)))
    for both in (False, True):
        print('parallel orientations', 'both' if both else 'co-oriented')
        numbers = list(inventory(wake, profiles, both))
        if both:
            slopes = [12, 6, 2, 1]
            first_four = [[23,35,47,59], [11,18,25,31], [3,5,7,9], [1,2,3,4]]
        else:
            slopes = [12, 7, 3, 1]
            first_four = [[23,35,47,59], [11,18,25,32], [4,7,10,13], [2,3,4,5]]
        assert numbers == [(a, vals, vals[-1]) for a, vals in zip(slopes, first_four)]


if __name__ == '__main__':
    main()
