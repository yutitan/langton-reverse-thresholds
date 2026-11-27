#define ANT_GATE11_LIBRARY
#include "ant_gate11_search.cpp"
#undef main
// For each fixed suffix, exhaust both colours at each newly constrained
// predecessor cell. Pose and cell states are restored by a reversible trail.
using namespace predecessor;
static constexpr int wide=160;static constexpr int origin=wide*(wide/2)+wide/2;
static int dirs[]={wide,1,-wide,-1};
struct Search{
    array<signed char,wide*wide> board;
    long long nodes=0,finished=0,walked=0,clipped=0;
    int best=99,ph=0,limit=0;
    vector<pair<int,signed char>> trail;
    array<int,65> byFree;
    void record(int p,int h,int mass,int t,int used){
        byFree[used]=min(byFree[used],mass);
        if(mass>=best)return;
        best=mass;
        if(mass>11)return;
        cout<<"mass "<<mass<<" phase "<<ph<<" depth "<<t<<" seed";
        for(int j=0;j<wide*wide;j++)if(board[j]==1){
            int x=j%wide-p%wide,y=j/wide-p/wide;
            for(int i=0;i<h;i++){int u=x;x=-y;y=u;}
            cout<<" "<<x<<" "<<y;
        }
        cout<<endl;
    }
    void dfs(int p,int h,int mass,int t,int left){
        size_t mark=trail.size();
        ++nodes;
        while(true){
            record(p,h,mass,t,limit-left);
            int q=p-dirs[h];
            if(q%wide<2||q%wide>=wide-2||q/wide<2||q/wide>=wide-2||t>=5000){
                ++clipped;break;
            }
            int v=board[q];
            if(v<0){
                if(!left){++finished;break;}
                for(int after: {1,0}){
                    board[q]=1-after;
                    dfs(q,(h+(after?3:1))&3,mass+1-after,t+1,left-1);
                    board[q]=-1;
                }
                break;
            }
            trail.push_back({q,(signed char)v});
            board[q]=1-v;mass+=1-2*v;p=q;h=(h+(v?3:1))&3;t++;++walked;
        }
        while(trail.size()>mark){
            auto [z,b]=trail.back();trail.pop_back();board[z]=b;
        }
    }
    void run(const Entry&e,int phase,int free){
        board.fill(-1);ph=phase;best=99;limit=free;
        for(int i=0;i<area;i++)if(e.board.known[i]){
            int q=origin+i%width-e.board.pos%width+wide*(i/width-e.board.pos/width);
            board[q]=e.board.black[i];
        }
        dfs(origin,e.board.h,e.board.count,e.elapsed,free);
    }
};
int main(int argc,char**argv){
    require(argc==5); init_words();ifstream f(argv[1]);string row;
    int free=stoi(argv[2]),lo=stoi(argv[3]),hi=stoi(argv[4]),i=0,bm=999;
    Search s;s.byFree.fill(999);
    if(string(argv[1])=="phase"){
        for(int ph=lo;ph<hi;ph++){
            s.run(Entry{predecessor::root(ph)},ph,free);bm=min(s.best,bm);
            cout<<"phase "<<ph<<" radius "<<free<<" minimum "<<s.best<<" clipped_cumulative "<<s.clipped<<endl;
        }
    }else require(f.good());
    while(getline(f,row)){
        int id=i++;if(id<lo||id>=hi)continue;
        istringstream in(row);int ph,lead,start,x,y;in>>ph>>lead>>start;
        vector<pair<int,int>> pts;while(in>>x>>y)pts.emplace_back(x,y);
        auto e=macrosearch::restart(pts,start,lead,ph,1);
        s.run(e,ph,free);bm=min(s.best,bm);
        cout<<"anchor "<<id<<" phase "<<ph<<" lead "<<lead<<" checkpoint "<<start<<" free "<<free<<" minimum "<<s.best<<" clipped_cumulative "<<s.clipped<<endl;
    }
    int value=999; cout<<"staircase";
    for(int r=0;r<=free;r++){value=min(value,s.byFree[r]);cout<<" "<<value;}
    cout<<endl;
    cout<<"nodes "<<s.nodes<<" leaves "<<s.finished<<" forced "<<s.walked<<" minimum "<<bm<<" clipped "<<s.clipped<<endl;
}
