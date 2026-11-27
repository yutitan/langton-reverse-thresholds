"""Replay the ordered H,V witness; certify the fixed preparation for every K."""
from ant208_extend import model, first_reads, minimal_seed, anchor
from ant3_reverse_inventory import canonical
from verify_ant_highway import Ant

PARENT=((-63,-43),(-86,-46))
T=174341
PHASE=89
def run():
    h=canonical()[1];v=h[::-1].translate(str.maketrans('LR','RL'))
    pre,block,drift=model(PARENT,T,PHASE)
    prefix=''.join('L' if c else 'R' for _,c in pre)
    assert prefix[9977:12430]==(h*24)[:2453] and prefix[12430]!=h[2453%104]
    # Classes modulo the primitive time-period displacement, including sign.
    classes={}
    dx,dy=drift
    for (x,y),bit in block:
        key=(x*dy-y*dx,x%abs(dx))
        classes.setdefault(key,{}).setdefault(x//dx,bit)
    assert len(classes)==22
    assert max(max(row)-min(row) for row in classes.values())<=3
    assert sum(row[max(row)] for row in classes.values())==12
    contact_k=anchor(pre,block,drift)
    assert contact_k==4
    # For K>=4 the prefix override is constant: all overlaps with the prefix
    # have already appeared, and their first required colours cannot change.
    # The longitudinal clusters from block offsets are contiguous by then;
    # extending each side leaves one new bulk first colour at its maximum offset.
    for k in (1,2,3,4,5,10,40):
        seeds=minimal_seed(pre,block,drift,k)
        assert len(seeds)==12*k+2
        a=Ant(set(seeds))
        for q,bit in pre:
            assert q==(a.x,a.y) and (a.step()=='L')==bit
        for j in range(104*k):assert a.step()==v[(PHASE+j)%104]
        if k==1:
            print('14-cell ordered witness',sorted(seeds))
            extra=0
            while a.step()==v[(PHASE+104+extra)%104]:extra+=1
            assert extra==15
        print('K',k,'initial cells',len(seeds))
    print('H starts 9977, length 2453; V starts 174341, phase 89; K=1 matches 119 steps')
    print('last possible prep-block intersection before index',contact_k,
          'class count',len(classes),'newly required black per block',12)
if __name__=='__main__':run()
