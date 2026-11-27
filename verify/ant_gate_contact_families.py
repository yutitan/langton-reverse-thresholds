"""Two independent displacements of the first two contacts of the 88-step seed.
For each fixed pair, let the third cell vary on the entire integer lattice."""
import argparse
from pathlib import Path
from subprocess import run,PIPE

def families(radius,base):
    (x,y),(u,v)=base
    for i in range(-radius,radius+1):
        for j in range(-radius,radius+1):
            yield i,j,(x-2*i,y-2*i),(u-2*i-2*j,v-2*i+2*j)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('tail',type=Path)
    ap.add_argument('scan',type=Path)
    ap.add_argument('directory',type=Path)
    ap.add_argument('--radius',type=int,default=4)
    ap.add_argument('--record',action='store_true',help='use the first two contacts of the anomaly witness')
    args=ap.parse_args()
    assert args.radius>=0
    args.directory.mkdir(exist_ok=True,parents=True)
    base=((-36,-11),(-2,-58)) if args.record else ((-63,-43),(-86,-46))
    for i,j,a,b in families(args.radius,base):
        if a==b:continue
        coords=(*a,*b)
        tag=f'{i}_{j}'
        # The extra point is an arbitrary anchor for the translation of the third cell.
        p=run([str(args.tail.resolve()),*map(str,coords),'0','0','4'],capture_output=True,text=True)
        if p.returncode:
            raise RuntimeError(f'uncertified pair {i,j}: {p.stderr}')
        lines=[r.split() for r in p.stdout.splitlines()]
        parent=lines.pop()
        assert parent[0]=='parent' and int(parent[3])==len(lines)
        vx,vy,cut=map(int,(parent[5],parent[6],parent[8]))
        cases=[('B',*coords),('P',*coords,cut)]
        for ray in lines:
            assert ray[0]=='ray' and ray[3]=='depth'
            x,y,k=map(int,(ray[1],ray[2],ray[4]))
            cases.append(('T',*coords,x+k*vx,y+k*vy))
        manifest=args.directory/(tag+'.in')
        manifest.write_text(''.join(' '.join(map(str,c))+'\n' for c in cases),encoding='ascii')
        rows=run([str(args.scan.resolve()),str(manifest),'1','--208'],stdout=PIPE,text=True,check=True).stdout
        rows=sorted((list(map(int,r.split())) for r in rows.splitlines()),key=lambda r:r[0])
        assert [r[0] for r in rows]==list(range(len(cases)))
        assert all(len(r)==20 for r in rows)
        winner=max(rows,key=lambda r:r[3])
        rec=max(rows,key=lambda r:r[11])
        print(i,j,*coords,rows[1][1],len(lines),winner[3],winner[4],*winner[5:11],
              sum(r[2] for r in rows),rec[11],*rec[13:19],flush=True)
        if winner[3]>=104 or rec[11]>285176:
            (args.directory/(tag+'.hit')).write_text(str(winner)+'\n'+str(rec)+'\n')
if __name__=='__main__':main()
