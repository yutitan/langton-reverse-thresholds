"""Exact finite checks for the short-factor thresholds on the 22 one-cell rays.

Usage: python ant_ray_thresholds.py path/to/TwoBlack/Level1Data.lean
The all-depth trace identity is proved by AntPrepared.lean and AntSplice.lean.
This script verifies its concrete word data and excludes the distinguishing
words for all time using a permanent-highway certificate at depth 41.
"""
import argparse
from hashlib import sha256
from pathlib import Path
import re

from verify_ant_highway import Ant, inspect_block

P = 104

def simulate(cell, stop):
    a = Ant(set() if cell is None else {cell})
    return a, ''.join(a.step() for _ in range(stop))

def certified_word(cell, stop, standard):
    ant, prefix = simulate(cell, stop)
    permanent, drift, _, block = inspect_block(ant)
    assert permanent and sorted(map(abs, drift)) == [2, 2]
    assert block in standard+standard
    return prefix, block

def word_at(prefix, period, stop):
    return (prefix + period*((max(0,stop-len(prefix))+P-1)//P))[:stop]

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('level1_data',type=Path)
    args = ap.parse_args()
    data = args.level1_data.read_text(encoding='utf-8-sig')
    entries = re.findall(r'\.mm, \[\], \[⟨(-?\d+), (-?\d+)⟩\]⟩, ⟨40, \d+, \d+, \[([\d, ]+)\], (\d+),',data)
    assert len(entries)==22
    _, standard = simulate(None,9977+P)
    standard = standard[-P:]
    print('x y  switches  unchanged_through  first_lost  start_at_depth40  largest_other_gap')
    levels=[]
    other_gaps=[]
    for xs,ys,ms,ss in entries:
        x,y,s = int(xs),int(ys),int(ss)
        cuts = list(map(int,ms.split(',')))
        f, tail = certified_word((x-80,y-80),s,standard)
        g, tail_g = certified_word((x-82,y-82),s+P*len(cuts),standard)
        # Independent consecutive-member replay, including their two infinite tails.
        stretched = f
        for cut in reversed(cuts):
            stretched=stretched[:cut]+stretched[cut:cut+P]+stretched[cut:]
        assert stretched==g and tail==tail_g
        intervals=[]
        for cut in cuts:
            l=r=cut
            while l>0 and f[l-1]==f[l-1+P]:
                l-=1
            while r+P<len(f) and f[r]==f[r+P]:
                r+=1
            assert 0<l<=cut<=r and r+P<len(f)
            assert f[cut:cut+P] in standard+standard
            assert all(f[i]==f[i+P] for i in range(l,r))
            intervals.append((l,r+P))
        assert all(b<c for (_,b),(c,_) in zip(intervals,intervals[1:]))
        l,end=min(intervals,key=lambda ab:ab[1]-ab[0])
        # After time s the trace is P-periodic. These are all mismatch indices.
        padded=f+tail
        marks=[i for i in range(s) if padded[i]!=padded[i+P]]
        pairs=set(zip(marks,marks[1:]))
        pumped={(a-1,b-P) for a,b in intervals}
        assert len(pumped)==len(cuts) and pumped<=pairs
        others=max(v-u for u,v in pairs-pumped)
        assert others < min(v-u for u,v in pumped)
        other_gaps.append(others)
        limit=end-l+1
        lost=f[l-1:end+1]
        # Every start after len(g) has a representative in [len(g),len(g)+P).
        universe=word_at(g,tail_g,len(g)+P+len(lost)-1)
        assert len(lost)==limit+1 and lost not in universe
        pre,suf=universe.find(lost[:-1]),universe.find(lost[1:])
        assert pre>=0 and suf>=0
        print(x,y,','.join(map(str,cuts)),limit,len(lost),l-1,others)
        levels.append(limit)
        if len(cuts)==2:
            print('exceptional 40-cell', (x-80,y-80), '41-cell',(x-82,y-82),
                  'periodic intervals',intervals,'prefix/suffix starts', pre,suf,
                  'permanent tail at depth 41',len(g),'SHA256(LR ASCII)',sha256(lost.encode()).hexdigest())
    assert min(levels)==4978 and max(levels)==5082
    assert max(other_gaps)==71
    print('minimum',min(levels),'maximum',max(levels),'rays',len(levels),'max other gap',max(other_gaps))
if __name__=='__main__':
    main()
