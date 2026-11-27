// Graft a suffix of a recorded preparatory history onto any endpoint of a
// different donor history. Backward first reads compute the least full seed.
#include "ant_gate_detector.hpp"
using Seed=vector<pair<int,int>>;
constexpr int W=384,O=(W/2)*(W+1);
const int ds[]={W,1,-W,-1};
struct A {int pos=O,h=0,ink=0; vector<int8_t>b=vector<int8_t>(W*W,-1);};
struct Edge {int q;int8_t old;};
bool retreat(A& a,int bit,vector<Edge>& undo){
  int q=a.pos-ds[a.h];
  if(q%W<=1||q%W>=W-2||q/W<=1||q/W>=W-2)throw runtime_error("coordinate guard");
  if(a.b[q]>=0 && a.b[q]==bit)return false;
  undo.push_back({q,a.b[q]});a.ink+=bit-int(a.b[q]==1);a.b[q]=bit;
  a.pos=q;a.h=(a.h+(bit?1:3))&3;return true;
}
A target(int phase){
  A a;int q=O,h=0;map<int,int> last;
  for(int i=0;i<104;i++){
    int bit=1-doubled[103-(phase+i)%104];
    if(a.b[q]<0){a.b[q]=bit;a.ink+=bit;}
    else require(last[q]!=bit);
    last[q]=bit;h=(h+1-2*bit)&3;q+=ds[h];
  }return a;
}
vector<int> history(const Seed& seed,int limit){
  set<pair<int,int>> b(seed.begin(),seed.end());vector<int> w;
  int x=0,y=0,h=0;for(int t=0;t<limit;t++){
    pair<int,int> q{x,y};int bit=b.count(q);if(bit)b.erase(q);else b.insert(q);w.push_back(bit);
    h=(h+1-2*bit)&3;x+=(h==1)-(h==3);y+=(h==0)-(h==2);
  }return w;
}
void report(A&a,int phase,int depth,int checkpoint,int donor,int end){
  cout<<"record "<<a.ink<<" phase "<<phase<<" depth "<<depth<<" checkpoint "<<checkpoint<<" donor "<<donor<<" end "<<end<<" seed";
  for(int q=0;q<W*W;q++)if(a.b[q]==1){
    int x=q%W-a.pos%W,y=q/W-a.pos/W;
    for(int i=0;i<a.h;i++){int z=x;x=-y;y=z;}
    cout<<" "<<x<<" "<<y;
  }cout<<endl;
}
int main(int argc,char**argv){
  require(argc==2);init_words();ifstream in(argv[1]);require(in.good());string ln;
  vector<vector<int>> donors;
  while(getline(in,ln)){istringstream s(ln);int cap,x,y;Seed seed;require(bool(s>>cap));
    while(s>>x){require(bool(s>>y));seed.emplace_back(x,y);}
    donors.push_back(history(seed,cap));}
  Seed three{{-86,-46},{-63,-43},{-22,-14}},twelve{{1,-1},{-3,-3},{-3,-1},{-4,-8},{-4,-1},{-6,-8},{-6,-5},{-6,-3},{-6,-2},{-6,-1},{-7,-6},{-7,-5}};
  vector<Edge> temp,undo;uint64_t checked=0,valid=0;int best=40,anchors=0;
  for(int which=0;which<2;which++){
    int lead=which?214688:221;auto pre=history(which?three:twelve,lead);
    for(int shift=0;shift<(which?1:7);shift++){
      int ph=(which?90:77)+shift,time=lead+shift;
      if(shift)pre=history(twelve,time);
      A a=target(ph);int compatible=0,minmass=a.ink;
      for(int d=0;d<=time;d++){
        minmass=min(minmass,a.ink);
        if(d==0||(a.ink<=32 && ((d%4==0 && d<320)||d%24==0))){
          const int pos=a.pos,h=a.h,mass=a.ink; ++anchors;
          if(mass<best){best=mass;report(a,ph,d,d,-1,-1);}
          for(int id=0;id<int(donors.size());id++){
            auto& w=donors[id];
            for(int e=0;e<int(w.size());e++){
              ++checked;undo.clear();
              for(int z=e;z>=0 && e-z<320;z--){
                if(!retreat(a,w[z],undo))break;
                ++valid;
                if(a.ink<best){best=a.ink;report(a,ph,d+e-z+1,d,id,e);}
              }
              for(auto it=undo.rbegin();it!=undo.rend();++it)a.b[it->q]=it->old;
              a.pos=pos;a.h=h;a.ink=mass;
            }
          }
        }
        if(d==time)break;
        temp.clear();if(!retreat(a,pre[time-d-1],temp))break;
        ++compatible;
      }
      cout<<"source "<<which<<" phase "<<ph<<" max_compatible_suffix "<<compatible<<" minimum "<<minmass<<endl;
    }
  }cout<<"done anchors "<<anchors<<" endpoints "<<checked<<" feasible_steps "<<valid<<" minimum "<<best<<endl;
}
