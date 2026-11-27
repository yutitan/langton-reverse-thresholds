"""All-K continuation of the exhaustive 30-step preparation bounds.
Run the C++ ant_gate_bg_short target for the finite minima first.
"""
from pathlib import Path
from ant208_extend import model, first_reads

def main():
    source=Path(__file__).resolve().parent
    max_block=0
    for phase in range(104):
        _,block,(dx,dy)=model((),0,phase)
        lanes={}
        for (x,y),bit in block:
            # Times j>=0 satisfying |x+j*dx|<=15 and |y+j*dy|<=15
            # must lie below both directed endpoint bounds.
            last_x=((15 if dx>0 else -15)-x)//dx
            last_y=((15 if dy>0 else -15)-y)//dy
            max_block=max(max_block,min(last_x,last_y)+1)
            lane=(x*dy-y*dx,x%abs(dx))
            lanes.setdefault(lane,{}).setdefault(x//dx,bit)
        assert len(lanes)==22
        assert max(max(r)-min(r) for r in lanes.values())<=3
        assert sum(r[max(r)] for r in lanes.values())==12
    assert max_block==10
    for k in range(1,12):
        name={1:'104',2:'208'}.get(k,'_K'+str(k))
        row=list(map(int,(source/f'ant_gate_bg_short{name}.txt').read_text(encoding='utf-8-sig').splitlines()[-1].split()))
        assert row[0]==30 and row[2]==12*k+6
    print('104 phases, block indices >=10 miss the entire 30-step preparation square')
    print('22 lanes, width <=3, exactly 12 new initial black cells per period for K>=10')
    print('exhausted K=1..11: minimum with <=30 preparatory steps is 12*K+6, for all K>=1 by induction')
if __name__=='__main__':main()
