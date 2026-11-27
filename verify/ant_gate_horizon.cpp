// Enumerate the exact decision tree of first-read colours, through a fixed end time.
#include "ant_gate_detector.hpp"
namespace gate {
ostream *manifest=nullptr;
struct Walker {
  int horizon, budget, best=0, bestEnd=0;
  vector<unsigned char> ink=vector<unsigned char>(side*side);
  vector<int> visits=vector<int>(side*side);
  vector<int> path, seeds, witness;
  array<uint64_t,4> leaves{};
  explicit Walker(int h,int m):horizon(h),budget(m),path(h) {}
  void note(int n,int t){
    if(n>best){best=n;bestEnd=t;witness=seeds;}
  }
  void check(int p){
    if(abs(xof(p))>=half-2||abs(yof(p))>=half-2)throw runtime_error("coordinate guard");
  }
  void complete(int t,int p,int hd,int node){
    ++leaves[seeds.size()];
    if(manifest){
      *manifest<<"T";for(int q:seeds)*manifest<<" "<<xof(q)<<" "<<yof(q);*manifest<<"\n";
      return;
    }
    for(int i=t;i<horizon;i++){
      check(p);path[i]=p;
      int bit=ink[p];ink[p]^=1;hd=(hd+1-2*bit)&3;p+=delta[hd];
      node=trie[node].next[bit];note(trie[node].depth,i+1);
    }
    for(int i=t;i<horizon;i++)ink[path[i]]^=1;
  }
  void enumerate(int t,int p,int hd,int node){
    if(int(seeds.size())==budget){complete(t,p,hd,node);return;}
    for(int i=t;i<horizon;i++){
      check(p);
      if(!visits[p]){
        require(!ink[p]);
        seeds.push_back(p);
        // First-read black flips to white, the board currently is already white.
        ++visits[p];int nh=(hd+3)&3,nn=trie[node].next[1];
        note(trie[nn].depth,i+1);enumerate(i+1,p+delta[nh],nh,nn);
        --visits[p];seeds.pop_back();
      }
      path[i]=p;++visits[p];
      int b=ink[p];ink[p]^=1;hd=(hd+1-2*b)&3;p+=delta[hd];
      node=trie[node].next[b];note(trie[node].depth,i+1);
    }
    ++leaves[seeds.size()];
    for(int i=t;i<horizon;i++){int q=path[i];ink[q]^=1;--visits[q];}
  }
};
}
int main(int argc,char**argv){
  require(argc==3||argc==4);int horizon=stoi(argv[1]),budget=stoi(argv[2]);
  require(horizon>0 && budget>=0 && budget<=3);init_words();init_detector();
  ofstream out; if(argc==4){require(budget==3);out.open(argv[3]);require(out.good());gate::manifest=&out;}
  gate::Walker w(horizon,budget);w.enumerate(0,cell(0,0),0,0);
  cout<<"horizon "<<horizon<<" budget "<<budget;
  if(!gate::manifest){
    cout<<" maximum "<<w.best<<" end "<<w.bestEnd<<" witness";
    for(auto p:w.witness)cout<<" "<<xof(p)<<" "<<yof(p);
  }
  cout<<" leaves";for(auto k:w.leaves)cout<<" "<<k;cout<<endl;
}
