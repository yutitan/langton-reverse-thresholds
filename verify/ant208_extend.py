"""Certify a fixed preparation word for arbitrarily many inverse periods."""
from ant3_reverse_inventory import canonical
from verify_ant_highway import Ant,VECTORS

SEED20=((1,-1),(-2,-5),(-3,-5),(-3,-4),(-3,-3),(-3,-1),(-4,-4),(-4,-1),(-4,0),
        (-5,-6),(-6,-8),(-6,-5),(-6,-3),(-6,-2),(-6,-1),(-7,1),(-8,-4),(-8,-1),
        (-8,0),(-8,1))
PREPARATION_SEED=((-6,-4),(-6,-3),(-5,0),(-4,-8),(-4,-6),(-4,-5),(-4,-4),(-4,-3),
                  (-3,-7),(-2,-8),(-2,-3),(-2,-2),(-2,0),(-1,-8),(-1,-5),(-1,-3),
                  (0,-6),(0,-4),(1,-8),(1,-5),(2,-6),(3,-6))

def model(seed,lead,phase):
    h=canonical()[1]
    inverse=h[::-1].translate(str.maketrans('RL','LR'))
    target=(inverse*2)[phase:phase+104]
    a=Ant(set(seed));pref=[]
    for _ in range(lead):
        q=(a.x,a.y)
        pref.append((q,a.step()=='L'))
    place=a.x,a.y
    x,y,d=a.x,a.y,a.heading
    block=[]
    for c in target:
        block.append(((x,y),c=='L'))
        d=(d+(1 if c=='R' else -1))%4
        dx,dy=VECTORS[d];x+=dx;y+=dy
    v=x-place[0],y-place[1]
    assert d==a.heading and abs(v[0])==abs(v[1])==2
    return pref,block,v

def anchor(pref,block,v):
    # No period of index >= k0 can read a preparation site. K>=4 also
    # guarantees stationary first-read end effects of the pure inverse.
    k0=4
    for (x,y),_ in pref:
        for (u,w),_ in block:
            j,rem=divmod(x-u,v[0])
            if not rem and w+j*v[1]==y:
                k0=max(k0,j+1)
    return k0

def first_reads(block,v,k):
    first,last={},{}
    for j in range(k):
        for (x,y),b in block:
            p=x+j*v[0],y+j*v[1]
            assert last.get(p)!=b
            first.setdefault(p,b)
            last[p]=b
    return first

def best_preparation(pref,block,v):
    k=anchor(pref,block,v)
    needs=first_reads(block,v,k)
    count=sum(needs.values())
    best=count-12*k,len(pref)
    for t in reversed(range(len(pref))):
        p,b=pref[t]
        if needs.get(p)==b:break
        count+=int(b)-int(needs.get(p) is True)
        needs[p]=b
        best=min(best,(count-12*k,t))
    return best,k

def minimal_seed(pref,block,v,k):
    req=first_reads(block,v,k)
    for p,b in reversed(pref):
        if req.get(p)==b:raise ValueError('incompatible read')
        req[p]=b
    return {p for p,b in req.items() if b}

if __name__=='__main__':
    p,b,v=model(SEED20,209,73)
    a=Ant(set(SEED20))
    for _ in range(209):a.step()
    assert len(a.black)==63
    for _ in range(2):
        assert [a.step()=='L' for _ in b]==[bit for q,bit in b]
    assert len(a.black)==39
    print('20-cell witness + 209 preparation steps + 208 inverse turns; 63 -> 39 black')
    pre,b,v=model(PREPARATION_SEED,218,76)
    assert best_preparation(pre,b,v)==((-5,0),4)
    # Along each class, once every longitudinal offset fits, one extra
    # period adds just the first colour at the extreme template offset.
    classes={}
    for (x,y),bit in b:
        key=x*v[1]-y*v[0],x%2
        offset=x//v[0]
        classes.setdefault(key,{}).setdefault(offset,bit)
    assert max(max(d)-min(d) for d in classes.values())<=3
    assert sum(d[max(d)] for d in classes.values())==12
    for k in (3,4,5,12,50):
        seed=minimal_seed(pre,b,v,k)
        assert len(seed)==12*k-5
        a=Ant(set(seed))
        for q,bit in pre:
            assert (a.x,a.y)==q and (a.step()=='L')==bit
        for j in range(k):
            for (x,y),bit in b:
                assert (a.x,a.y)==(x+j*v[0],y+j*v[1]) and (a.step()=='L')==bit
    print('fixed 218-step preparation, 12*K-5 initial cells for every K>=3')
