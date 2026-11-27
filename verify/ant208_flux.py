"""Bound signed colour supply to any contiguous slab needed for an eraser.

Columns are floor(x/2), r=x-y+28. Every signed footprint is computed from
chronological R (+1) and L (-1) turns of a real standard block.
"""
from collections import Counter
from itertools import product
from ant3_reverse_inventory import canonical,reverse_profile,rotate
from ant208_extend import first_reads


POS={(0,0),(0,1),(6,1),(8,0),(10,0),(10,1)}
POS_SAME=POS|{(2,1),(3,1),(4,0)}


def max_interval(columns):
    best=partial=0
    for l in sorted(columns):
        partial=max(0,partial+columns[l])
        best=max(best,partial)
    return best


def bounds(pos, only_same=False):
    reads,word=canonical()
    wake,_,_=reverse_profile(reads,word)
    r0=min(x-y for x,y in reads)
    assert r0==-28 and pos<=wake
    def weight(x,y):
        r=x-y-r0
        if not 0<=r<=10:return 0
        z=(r,x%2)
        return int(z in pos)-int(z not in wake)

    cap_parallel=cap_cross=width=0
    # Phase cycles move read vertices by the physical forward drift.
    for phase in range(104):
        events=[]
        for k in range(104):
            j=(phase+k)%104;carry=(phase+k)//104;x,y=reads[j]
            events.append(((x-2*carry,y-2*carry),1 if word[j]=='R' else -1))
        for turns in range(4):
            if only_same and turns==2:continue
            v=rotate((-2,-2),turns)
            transformed=[(*rotate(q,turns),b) for q,b in events]
            if turns%2==0:
                for k,e in product(range(-9,10,2),range(2)):
                    dx=e; dy=e-k+(46 if turns==2 else 0)
                    # One extra period only lengthens a constant, nonpositive
                    # middle once the two ends are separated.
                    net=Counter()
                    for x,y,b in transformed:
                        net[(x+dx)//2]+=b*weight(x+dx,y+dy)
                    assert sum(net.values())<=0
                    span=max(net)-min(net)
                    width=max(width,span)
                    series=Counter()
                    for n in range(span+1):
                        for l,b in net.items():series[l+n*(v[0]//2)]+=b
                        cap_parallel=max(cap_parallel,max_interval(series))
            else:
                for dx,dy in product(range(4),repeat=2):
                    if (dx+dy)%2:continue
                    blocks={}
                    for x,y,b in transformed:
                        r=x+dx-y-dy-r0
                        # |change of transverse layer per period| is four.
                        for layer in range(11):
                            j,rem=divmod(layer-r,v[0]-v[1])
                            if rem:continue
                            xx=x+dx+j*v[0];yy=y+dy+j*v[1]
                            block=blocks.setdefault(j,Counter())
                            block[xx//2]+=b*weight(xx,yy)
                    ids=sorted(blocks)
                    for start in range(len(ids)):
                        section=Counter()
                        for j in ids[start:]:
                            section.update(blocks[j])
                            cap_cross=max(cap_cross,max_interval(section))
    return len(pos),width,cap_parallel,cap_cross


def demand_slack(pos):
    reads,h=canonical()
    wake,_,_=reverse_profile(reads,h)
    negative=set(product(range(11),range(2)))-wake
    slack=0
    for phase in range(104):
        block=[]
        for j in range(104):
            index,i=divmod(103-phase-j,104)
            x,y=reads[i]
            block.append(((x-2*index,y-2*index),h[i]=='R'))
        anchor=max(p[0]//2 for p,_ in block)
        for k in range(1,6):
            req=first_reads(block,(2,2),k)
            columns=sorted({x//2 for x,y in req})
            low={}
            for l in columns:
                def get(z):
                    r,s=z;x=2*l+s
                    return req.get((x,x+28-r))
                low[l]=sum(get(z) is True for z in pos)-sum(get(z) is not False for z in negative)
            if k==5:
                # Inserting one complete column here leaves the two end
                # profiles unchanged. Use an interval containing that column.
                assert low[anchor]==len(pos)
                guarantee=max(sum(low.get(z,0) for z in range(a,b+1))
                              for a in columns for b in columns if a<=anchor<=b)
            else:
                guarantee=max_interval(low)
            slack=max(slack,k*len(pos)-guarantee)
    return slack


def main():
    for weights,same,expected in ((POS,False,(6,4,9,15,12)),(POS_SAME,True,(9,4,7,14,15))):
        values=bounds(weights,same)
        result=(*values,demand_slack(weights))
        assert result==expected
        print('demand, width, parallel supply, perpendicular supply, target end loss:',result)


if __name__=='__main__':
    main()
