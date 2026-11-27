#define BG_LIB
#include "ant_gate_bg_evolve.cpp"
#undef main
#include <chrono>
// Freeze partial board at a known reverse prefix, then exhaust every
// assignment over a bounded number of previously unconstrained first reads.
struct Search {
 array<int8_t,W*W> b;
 vector<int> visited;
 int ph;
 long long nodes=0,steps=0,targets=0;
 void report(int m,int t,int p,int h){
   if(m>=best)return;
   best=m;cout<<"mass "<<m<<" phase "<<ph<<" time "<<t<<" seed";
   for(int q:visited)if(b[q]==1){
     int x=q%W-p%W,y=q/W-p/W;for(int j=0;j<h;j++){int v=x;x=-y;y=v;}
     cout<<" "<<x<<" "<<y;
   }
   cout<<endl;
 }
 void apply(int after,int q,int &p,int &h,int &m){
   bool seen=b[q]>=0;if(!seen)visited.push_back(q);
   m+=1-after-int(seen && after);b[q]=1-after;
   p=q; h=(h+(after?-1:1))&3;
 }
 struct Edit{int q;int8_t previous;};
 void dfs(int p,int h,int m,int t,int left){
   nodes++;
   vector<Edit> undo;
   while(t<2500 && m<best+32){
     report(m,t,p,h);
     int q=p-dirs[h];if(q%W<3 || q%W>W-4 || q/W<3 || q/W>W-4)break;
     if(b[q]<0){
       if(left==0)break;
       for(int after=1;after>=0;after--){
         int pos=p,head=h,mass=m;apply(after,q,pos,head,mass);steps++;
         dfs(pos,head,mass,t+1,left-1);visited.pop_back();b[q]=-1;
       }
       break;
     }
     int after=b[q];undo.push_back({q,(int8_t)after});apply(after,q,p,h,m);t++;steps++;
   }
   for(auto u=undo.rbegin();u!=undo.rend();++u)b[u->q]=u->previous;
 }
 void run(int phase,int T,const set<int>& white,int left,int salt,int minink){
   b.fill(-1);visited.clear();ph=phase;int m=0;
   for(auto [q,c]:templ[phase]){b[q]=c;m+=c;visited.push_back(q);}
   int p=O,h=0;
   for(int t=0;t<=T;t++){
     report(m,t,p,h);
     int q=p-dirs[h];if(q%W<3 || q%W>W-4 || q/W<3 || q/W>W-4)break;
     if(b[q]<0 && t+1>=salt && m<=minink){
       uint64_t code=(unsigned)t+1;
       for(int a:visited){code=(code^uint64_t(a*4+b[a]+2))*1099511628211ULL;}
       if(done.insert(code).second){targets++;dfs(p,h,m,t,left);}
     }
     if(t==T)break;
     int after=(b[q]>=0)?b[q]:!white.count(q);apply(after,q,p,h,m);
   }
 }
 unordered_set<uint64_t> done;
};
int main(int argc,char**argv){
 require(argc==7);init_words();objective=stoi(argv[6]);make_templates();
 ifstream in(argv[1]);int budget=stoi(argv[2]),minDepth=stoi(argv[3]),maxInk=stoi(argv[4]);
 vector<string> rows;string line;while(getline(in,line))rows.push_back(line);
 gen.seed(stoul(argv[5]));shuffle(rows.begin(),rows.end(),gen);
 Search search;
 for(const string& row:rows){
   istringstream r(row);int p,t,x,y;r>>p>>t;set<int> chosen;
   while(r>>x>>y)chosen.insert(O+x+y*W);
   search.run(p,t,chosen,budget,minDepth,maxInk);
 }
 cerr<<"anchors "<<rows.size()<<" checkpoints "<<search.targets
     <<" nodes "<<search.nodes<<" actions "<<search.steps<<" best "<<best<<endl;
}
