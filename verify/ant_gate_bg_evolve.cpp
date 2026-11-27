// Find sparse initial states that generate V^2. Complete the backwards
// unknown board with black by default, mutating the first-read exceptions.
// Only first-read constraints, not the arbitrary completion, enter the answer.
#define main ext_main
#include "ant2_extremum.cpp"
#undef main
#include <random>
#include <unordered_set>
using PointSet=vector<int>;
const int W=512, O=(W/2)*(W+1), dirs[]={W,1,-W,-1};
struct Agent {int phase=0,mass=999,depth=0; PointSet white,front; };
array<vector<pair<int,int>>,104> templ;
mt19937 gen;
int coin(int n){return int(gen()%n);}
int best=99,stepsLimit=1800, objective=208;
void make_templates(){
  for(int ph=0;ph<104;ph++){
    set<int> read; int p=O,h=0;
    for(int j=0;j<objective;j++){
      int b=1-doubled[103-(j+ph)%104];
      if(read.insert(p).second)templ[ph].push_back({p,b});
      h=(h+1-2*b)&3; p+=dirs[h];
    }
  }
}
Agent simulate(int ph,const PointSet&white){
  static vector<int> known(W*W),ink(W*W),hint(W*W);
  static int tag=0; tag++;
  for(int p:white)hint[p]=tag;
  PointSet visited,front,choices;
  int p=O,h=0,m=0;
  for(auto [q,b]:templ[ph]){
    known[q]=tag;ink[q]=b;m+=b;visited.push_back(q);
  }
  int local=999, depth=0, cut=0, cutFront=0;
  for(int t=0;t<stepsLimit;t++){
    if(m<local || (m==local && t>depth+200)){
      local=m;depth=t;cut=int(choices.size());cutFront=int(front.size());
      if(m<best){
        best=m;
        cout<<"mass "<<best<<" phase "<<ph<<" time "<<t<<" seed";
        for(int a:visited)if(ink[a]){
          int x=a%W-p%W,y=a/W-p/W;
          for(int j=0;j<h;j++){int u=x;x=-y;y=u;}
          cout<<" "<<x<<" "<<y;
        }
        cout<<endl;
      }
    }
    int q=p-dirs[h];
    if(q%W<=1 || q%W>=W-2 || q/W<=1 || q/W>=W-2 || m>local+85)break;
    bool seen=known[q]==tag;
    bool after=seen?ink[q]:(hint[q]!=tag);
    if(!seen){
      known[q]=tag;visited.push_back(q);front.push_back(q);
      if(!after)choices.push_back(q);
    }
    m+=int(!after)-int(seen && after);
    ink[q]=!after; h=(h+(after?-1:1))&3;p=q;
  }
  // Retain a few post-minimum sites to branch from the same local minimum.
  front.resize(min(front.size(),size_t(cutFront+18)));
  choices.resize(cut);sort(choices.begin(),choices.end());
  return Agent{ph,local,depth,choices,front};
}
#ifndef BG_LIB
int main(int argc,char**argv){
  require(argc==6);init_words(); objective=stoi(argv[5]);make_templates();
  gen.seed(stoul(argv[2])); int rounds=stoi(argv[3]);stepsLimit=stoi(argv[4]);
  ifstream f(argv[1]);string row;vector<Agent> starters;
  while(getline(f,row)){istringstream r(row);int ph,x,y;r>>ph;PointSet pts;
    while(r>>x>>y)pts.push_back(O+x+y*W);
    starters.push_back(simulate(ph,pts));}
  for(int p=0;p<104;p++)starters.push_back(simulate(p,{}));
  map<pair<int,PointSet>,int> unique;
  vector<Agent> pop=starters;
  for(int g=0;g<rounds;g++){
    vector<Agent> next;
    for(unsigned rep=0;rep<14000;rep++){
      const Agent &a=(coin(10)?pop[coin(pop.size())]:starters[coin(starters.size())]);
      PointSet mod=a.white;
      if(a.front.empty())continue;
      int n=1+coin(coin(4)?6:18);
      for(int i=0;i<n;i++){
        int q=a.front[coin(a.front.size())];
        auto it=find(mod.begin(),mod.end(),q);
        if(it==mod.end())mod.push_back(q);else mod.erase(it);
      }
      sort(mod.begin(),mod.end());
      if(!unique.emplace(make_pair(a.phase,mod),1).second)continue;
      auto b=simulate(a.phase,mod);
      if(b.mass<=best+9 && !b.front.empty())next.push_back(move(b));
    }
    next.insert(next.end(),pop.begin(),pop.end());
    shuffle(next.begin(),next.end(),gen);
    stable_sort(next.begin(),next.end(),[](const Agent&a,const Agent&b){return a.mass<b.mass;});
    pop.clear();
    map<pair<int,int>,int> groups;set<pair<int,PointSet>> keep;
    for(auto &a:next){
      if(!keep.emplace(a.phase,a.white).second)continue;
      auto &c=groups[{a.phase,a.mass}];
      if(c++<8)pop.push_back(move(a));
      if(pop.size()>=160)break;
    }
    if(unique.size()>200000)unique.clear();
  }
}

#endif
