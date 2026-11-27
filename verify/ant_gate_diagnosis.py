"""Recover all forced colours for a completed or interrupted inverse block."""
from collections import defaultdict
from ant208_extend import model
from verify_ant_highway import Ant
seed3=((-86,-46),(-63,-43),(-22,-14))
seed11=((1,-1),(-3,-3),(-3,-1),(-4,-8),(-4,-1),(-6,-8),(-6,-5),(-6,-3),(-6,-2),(-6,-1),(-7,-6))
def diagnose(seed,t,phase):
    pre,block,_=model(seed,t,phase)
    visits=defaultdict(list)
    ant=Ant(set(seed))
    for i,(q,b) in enumerate(pre):
        assert (ant.x,ant.y)==q and (ant.step()=='L')==b
        visits[q].append(i)
    demanded={}
    for i,(q,black) in enumerate(block):
        demanded.setdefault(q,(i,black))
    wrong=[(i,q,'black' if black else 'white',len(visits[q]),visits[q][0] if visits[q] else None,
            visits[q][-1] if visits[q] else None) for q,(i,black) in demanded.items() if (q in ant.black)!=black]
    return len(demanded),wrong,sorted((times[0],q) for q,times in visits.items() if times and q in seed)
if __name__=='__main__':
    for seed,t,p in ((seed3,214688,90),(seed11,221,77),(seed11+((-7,-5),),221,77),(((24,-14),(-11,6)),14770,92)):
        size,wrong,contacts=diagnose(seed,t,p)
        print(len(seed),'initial, start',t,'phase',p,'first-read sites',size,'wrong',len(wrong))
        for w in wrong:print(' ',*w)
        print('seed contacts',contacts)
