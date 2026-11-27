from pathlib import Path
from itertools import combinations,product
from ant_gate_diagnosis import seed3,seed11
def cases():
    bank={}
    def add(seed,cap):
        pts=tuple(sorted(seed))
        if len(set(pts))!=len(pts):return
        bank[pts]=max(cap,bank.get(pts,0))
    # Include the complete preparation for both near misses as controls.
    add(seed3,215000); add(seed11,1000); add(seed11+((-7,-5),),1000)
    early=((1,-1),(-3,-1),(-4,-1),(-6,-3),(-6,-5),(-7,-6),(-6,-8),(-4,-8))
    for n in range(9):
        for group in combinations(early,n):add(group,700 if n>3 else 1800)
    # Vary the two independent diagonal offsets at the first two observed contacts.
    for i,j in product(range(-3,4),repeat=2):
        a=(-63-2*i,-43-2*i); b=(-86-2*i-2*j,-46-2*i+2*j)
        add((a,b),46000)
    # Couple a local two-cell parent or a translated short preparation to a free
    # new set of far cells chosen by the 104 required readings at every pose.
    for group in combinations(early,2):
        for dx,dy in product(range(-1,2),repeat=2):
            add([(x+dx,y+dy) for x,y in group],3500)
    for p in combinations(seed3,2):add(p,110000)
    add(((24,-14),(-11,6)),36000)
    for pts,cap in bank.items():yield (cap,*sum(pts,()))
if __name__=='__main__':
    for row in cases():print(*row)
