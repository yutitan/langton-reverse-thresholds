"""Make canonical reverse search starting positions from the published two-period anchors."""
import sys
from pathlib import Path
from ant208_extend import SEED20, PREPARATION_SEED, model
from verify_ant_highway import Ant

def anchor(seed, lead, phase):
    ant=Ant(set(seed)); events=[]
    for _ in range(lead):
        p=ant.x,ant.y
        b=ant.step()=='L'
        events.append((p,b))
    path,block,drift=model(seed,lead,phase)
    required={p for p,b in block}|{(p[0]+drift[0],p[1]+drift[1]) for p,b in block}
    choices=[]
    for p,b in reversed(events):
        if p not in required:
            required.add(p)
            if b:
                x,y=p[0]-ant.x,p[1]-ant.y
                for _ in range(ant.heading): x,y=-y,x
                choices.append((x,y))
    return tuple(sorted(choices))

def main():
    root=Path(__file__).parent
    known={(73,209,SEED20),(76,218,PREPARATION_SEED)}
    for line in (root/'ant208_restart_2.txt').read_text().splitlines():
        phase,lead,cut,*coords=map(int,line.split())
        known.add((phase,lead,tuple(zip(coords[::2],coords[1::2]))))
    for phase,lead,seed in sorted(known):
        print(phase,*[i for p in anchor(seed,lead,phase) for i in p])

if __name__=='__main__': main()
