"""Independent checks for the reverse-play thresholds record.

This program does NOT import the delivered verification programs. It
re-implements the Langton step, the standard word H / reverse word V, the
first-read-colour construction of the 12K+2 family, and the witness checks.
Run from the verify/ directory (or with this file's directory as cwd); it
reads ../data/cases500_sample.txt and ../data/cases500_counts.txt.
"""
import os
import sys

VEC = [(0, 1), (1, 0), (0, -1), (-1, 0)]
FAILS = []


def check(name, cond, detail=""):
    print(("PASS " if cond else "FAIL ") + name + (("  " + str(detail)) if detail else ""))
    if not cond:
        FAILS.append(name)


def sim(cells, n):
    black = set(cells)
    x = y = d = 0
    reads = []
    poses = []
    for t in range(n):
        b = (x, y) in black
        reads.append(b)
        poses.append((x, y, d))
        if b:
            black.remove((x, y))
        else:
            black.add((x, y))
        d = (d + 3) % 4 if b else (d + 1) % 4
        dx, dy = VEC[d]
        x += dx
        y += dy
    return reads, poses, black, (x, y, d)


blank_reads, _, _, _ = sim((), 10085)
H = [bool(b) for b in blank_reads[9977:10081]]


def V(phase, n):
    return [not H[103 - ((phase + i) % 104)] for i in range(n)]


def match(reads, t, phase, n):
    v = V(phase, n)
    return all(reads[t + i] == v[i] for i in range(n))


def maxmatch(reads, cap=None):
    """Longest contiguous V-cyclic segment anywhere in reads (classic DP)."""
    N = len(reads) if cap is None else cap
    vb = [not H[103 - p] for p in range(104)]
    nxt = [0] * 104
    best = (-1, -1, -1)
    for t in range(N - 1, -1, -1):
        cur = [0] * 104
        r = reads[t]
        for p in range(104):
            if r == vb[p]:
                L = nxt[(p + 1) % 104] + 1
                cur[p] = L
                if L > best[0]:
                    best = (L, t, p)
        nxt = cur
    return best


# ---------- 0-cell / 1-cell exact witnesses ----------
r0, _, _, _ = sim((), 1041 + 40)
check("blank 32 at (1041, phase 4)", match(r0, 1041, 4, 32))
r1, _, _, _ = sim((( -30, -2),), 29393 + 70)
check("one cell 58 at (29393, phase 6)", match(r1, 29393, 6, 58))

# ---------- 14-cell ordered witness ----------
S14 = [(-86, -46), (-63, -43), (-36, 0), (-36, 3), (-35, -1), (-35, 0),
       (-35, 1), (-34, 2), (-34, 3), (-33, 0), (-33, 3), (-32, 2),
       (-31, 1), (-31, 2)]
r14, _, _, _ = sim(S14, 174341 + 130)
check("14-cell forward 2453 from 9977", all(r14[9977 + i] == H[i % 104] for i in range(2453)))
check("14-cell forward diverges at 2454", r14[9977 + 2453] != H[2453 % 104])
check("14-cell reverse 119 at 174341 phase 89", match(r14, 174341, 89, 119))
check("14-cell reverse fails at 120", not match(r14, 174341, 89, 120))

# ---------- re-implementation of the first-read-colour construction ----------
PARENT = ((-63, -43), (-86, -46))
T = 174341
PHASE = 89
pread, pposes, _, pstate = sim(PARENT, T)
pre_pairs = [((pposes[i][0], pposes[i][1]), pread[i]) for i in range(T)]
px, py, pd = pstate
bx, by, dd = px, py, pd
block = []
for b in V(PHASE, 104):
    block.append(((bx, by), b))
    dd = (dd + 3) % 4 if b else (dd + 1) % 4
    dx, dy = VEC[dd]
    bx += dx
    by += dy
drift = (bx - px, by - py)
check("target drift is (-2,2)", drift == (-2, 2), drift)


def first_reads(blk, v, k):
    first, last = {}, {}
    for j in range(k):
        for (x, y), b in blk:
            p = (x + j * v[0], y + j * v[1])
            if last.get(p) == b:
                raise RuntimeError("repeated first-read colour")
            first.setdefault(p, b)
            last[p] = b
    return first


def minimal_seed(k):
    req = first_reads(block, drift, k)
    for p, b in reversed(pre_pairs):
        if req.get(p) == b:
            raise RuntimeError("incompatible preamble read")
        req[p] = b
    return {p for p, b in req.items() if b}


seeds = {k: minimal_seed(k) for k in (1, 2, 3)}
check("construction K=1 gives the listed 14 cells", seeds[1] == set(S14))
check("construction sizes 14/26/38", [len(seeds[k]) for k in (1, 2, 3)] == [14, 26, 38],
      [len(seeds[k]) for k in (1, 2, 3)])
r2, _, _, _ = sim(seeds[2], T + 209)
check("K=2 reproduces the 174,341-step preamble", all(r2[t] == pread[t] for t in range(T)))
check("K=2 matches at least 208 reverse steps", match(r2, T, 89, 208))
r3, _, _, _ = sim(seeds[3], T + 313)
check("K=3 matches at least 312 reverse steps", match(r3, T, 89, 312))

# ---------- 88-step diagnosis table ----------
S3 = ((-86, -46), (-63, -43), (-22, -14))


def diagnose(seed, t, phase):
    reads, poses, black, st = sim(seed, t)
    pre = [((poses[i][0], poses[i][1]), reads[i]) for i in range(t)]
    visits = {}
    for i, (q, b) in enumerate(pre):
        visits.setdefault(q, []).append(i)
    x, y, d = st
    demanded = {}
    blk = []
    for b in V(phase, 104):
        q = (x, y)
        blk.append((q, b))
        demanded.setdefault(q, (len(blk) - 1, b))
        d = (d + 3) % 4 if b else (d + 1) % 4
        dx, dy = VEC[d]
        x += dx
        y += dy
    wrong = []
    for q, (i, req) in demanded.items():
        if (q in black) != req:
            vs = visits.get(q, [])
            wrong.append((i, q, req, len(vs), vs[-1] if vs else None))
    return len(demanded), wrong


nd, wrong = diagnose(S3, 214688, 90)
expected = [(88, (-48, -32), True, 38, 177676), (92, (-48, -30), True, 34, 179132),
            (93, (-49, -30), False, 37, 145153), (94, (-49, -29), False, 31, 177714),
            (97, (-49, -28), True, 32, 177713), (102, (-49, -31), True, 38, 177678)]
check("88 witness reads 41 distinct target cells", nd == 41, nd)
check("88 witness has exactly the six listed mismatches", wrong == expected, wrong)
r88, _, _, _ = sim(S3, 214688 + 100)
check("3-cell 88 witness matches 88 (phase 90)", match(r88, 214688, 90, 88))
check("3-cell 88 witness fails at 89", not match(r88, 214688, 90, 89))

# ---------- 11-cell witness ----------
S11 = ((1, -1), (-3, -3), (-3, -1), (-4, -8), (-4, -1), (-6, -8),
       (-6, -5), (-6, -3), (-6, -2), (-6, -1), (-7, -6))
nd11, wrong11 = diagnose(S11, 221, 77)
check("11-cell witness has 38 target cells", nd11 == 38, nd11)
check("11-cell single mismatch (-7,-5) never read",
      wrong11 == [(101, (-7, -5), True, 0, None)], wrong11)
r11, _, _, _ = sim(S11, 221 + 115)
check("11-cell matches 101 and fails 102", match(r11, 221, 77, 101) and not match(r11, 221, 77, 102))
r11b, _, _, _ = sim(S11 + ((-7, -5),), 221 + 120)
check("12-cell (11 + (-7,-5)) matches 110", match(r11b, 221, 77, 110))
check("12-cell fails at 111", not match(r11b, 221, 77, 111))

# ---------- two-cell 87 ----------
G = ((24, -14), (-11, 6))
rg, _, _, _ = sim(G, 14770 + 95)
check("two-cell 87 at (14770, phase 92)", match(rg, 14770, 92, 87))
check("two-cell fails at 88", not match(rg, 14770, 92, 88))

# ---------- horizon witnesses ----------
for name, seed, cap in (("h78", ((3, 5), (-3, 4), (-7, 4)), 2600),
                        ("h86", ((2, 4), (5, 4), (6, 3)), 9200)):
    reads, _, _, _ = sim(seed, cap)
    best = maxmatch(reads)
    if name == "h78":
        check("horizon-2000 witness has max 78 ending at 1894",
              best == (78, 1816, 34), best)
    else:
        check("horizon-500 witness has max 86 starting at 7897",
              best == (86, 7897, 92), best)


def first_read_times(seed, cap):
    black = set(seed)
    x = y = d = 0
    fr = {}
    for t in range(cap):
        if (x, y) in black and (x, y) not in fr:
            fr[(x, y)] = t
        b = (x, y) in black
        if b:
            black.remove((x, y))
        else:
            black.add((x, y))
        d = (d + 3) % 4 if b else (d + 1) % 4
        dx, dy = VEC[d]
        x += dx
        y += dy
    return fr


seed86 = ((2, 4), (5, 4), (6, 3))
fr86 = first_read_times(seed86, 500)
fr86_times = sorted(fr86[c] for c in seed86 if c in fr86)
check("86 witness: all three cells first read before 500",
      fr86_times == [301, 332, 343], fr86_times)

# ---------- 413,982 manifest ----------
here = os.path.dirname(os.path.abspath(__file__))
sample = os.path.join(here, "..", "data", "cases500_sample.txt")
counts = os.path.join(here, "..", "data", "cases500_counts.txt")
if os.path.exists(sample):
    lines = open(sample, encoding="utf-8").read().splitlines()
    bad = 0
    for ln in lines:
        a = ln.split()
        if a[0] != "T":
            bad += 1
            continue
        vals = list(map(int, a[1:]))
        cells = [(vals[0], vals[1]), (vals[2], vals[3]), (vals[4], vals[5])]
        fr = first_read_times(cells, 500)
        if len(set(cells)) != 3 or any(c not in fr for c in cells) \
           or max(fr[c] for c in cells) >= 500:
            bad += 1
    check("cases500 sample: 200 triples all read before 500", len(lines) == 200 and bad == 0,
          "lines=%d bad=%d" % (len(lines), bad))
else:
    check("cases500 sample available", False, sample)
if os.path.exists(counts):
    txt = open(counts, encoding="utf-8").read()
    check("manifest line count is 413,982", "413982" in txt, txt.strip())
else:
    check("cases500 count file available", False, counts)

print()
if FAILS:
    print("FAILED:", ", ".join(FAILS))
    sys.exit(1)
print("ALL INDEPENDENT CHECKS PASSED")
