/* At a fixed pose after a real prefix, test the first colour demanded at each
   distinct offset of V. A previously read cell is fixed. Every previously
   unread cell can be chosen independently at the origin of time. */
#include "ant_gate_detector.hpp"
using Point=pair<int,int>;
struct Need {int off,time,black;};
array<array<vector<Need>,104>,4> pattern;
array<int,65536> phase16;
void templates(){
  phase16.fill(-1);
  for(int p=0;p<104;p++){
    int key=0;for(int i=0;i<16;i++)key=2*key+doubled[(p+i)%104];
    // Some short words occur at multiple phases. The road detector below
    // checks the entire 104-letter block when its suffix has a valid key.
    phase16[key]=p;
    for(int hd=0;hd<4;hd++){
      int d=hd,q=0;set<int> seen;map<int,int> last;
      for(int i=0;i<104;i++){
        int b=1-doubled[103-(p+i)%104];
        if(seen.insert(q).second)pattern[hd][p].push_back({q,i,b});
        else require(last[q]!=b);
        last[q]=b;d=(d+1-2*b)&3;q+=delta[d];
      }
    }
  }
}
struct Result {
  int prefix=-1,roadPrefix=-1,ink=200,roadInk=200;
  uint64_t starts=0,afterRoad=0,edgeStops=0;
};
void emit(const char* tag,int metric,int id,int t,int phase,bool h,const vector<int>&fixed,const vector<int>&added,int used){
  cout<<tag<<" "<<metric<<" "<<id<<" "<<t<<" "<<phase<<" "<<int(h)<<" "<<(fixed.size()+used);
  for(auto q:fixed)cout<<" "<<xof(q)<<" "<<yof(q);
  for(int i=0;i<used;i++)cout<<" "<<xof(added[i])<<" "<<yof(added[i]);cout<<endl;
}
void evaluate(int id,const vector<Point>&source,int cap,Result&r){
  static vector<unsigned char> black(side*side),seen(side*side),given(side*side);
  vector<int> fixed,touched,added;added.reserve(48);
  for(auto [x,y]:source){int q=cell(x,y);require(!given[q]);given[q]=black[q]=1;}
  int pos=cell(0,0),hd=0,key=0,firstRoad=-1;string history;history.reserve(cap);
  for(int t=0;t<cap;t++){
    if(abs(xof(pos))>half-20||abs(yof(pos))>half-20){++r.edgeStops;break;}
    ++r.starts;if(firstRoad>=0)++r.afterRoad;
    for(int ph=0;ph<104;ph++){
      int len=104,three=104,save=0;
      added.clear();
      for(auto [off,i,b]:pattern[hd][ph]){
        int q=pos+off;
        if(seen[q]){
          if(black[q]!=b){len=i;break;}
        }else if(b){
          if(fixed.size()+added.size()==3){three=i;save=added.size();}
          added.push_back(q);
          if(int(fixed.size()+added.size())>min(18,max(r.ink,r.roadInk))){len=i;break;}
        }
      }
      if(fixed.size()<=3){
        int m=min(three,len);
        int use=(three<len||int(added.size()+fixed.size())>3)?save:int(added.size());
        if(m>r.prefix){r.prefix=m;emit("prefix",m,id,t,ph,firstRoad>=0,fixed,added,use);}
        if(firstRoad>=0&&m>r.roadPrefix){r.roadPrefix=m;emit("road_prefix",m,id,t,ph,true,fixed,added,use);}
      }
      int m=int(fixed.size()+added.size());
      if(len==104){
        if(m<r.ink){r.ink=m;emit("full",m,id,t,ph,firstRoad>=0,fixed,added,added.size());}
        if(firstRoad>=0&&m<r.roadInk){r.roadInk=m;emit("road_full",m,id,t,ph,true,fixed,added,added.size());}
      }
    }
    if(!seen[pos]){
      seen[pos]=1;touched.push_back(pos);if(given[pos])fixed.push_back(pos);
    }
    int b=black[pos];black[pos]^=1;history.push_back(char(b));
    key=(2*key+b)&65535;hd=(hd+1-2*b)&3;pos+=delta[hd];
    if(t>=103 && firstRoad<0 && phase16[key]>=0 && doubled.find(history.substr(t-103,104))<104)firstRoad=t+1;
  }
  for(int q:touched){black[q]=seen[q]=0;}
  for(auto [x,y]:source){int q=cell(x,y);given[q]=black[q]=0;}
}
int main(int argc,char**argv){
  require(argc==2);init_words();templates();ifstream src(argv[1]);require(src.good());string line;
  Result r;int id=0;
  while(getline(src,line)){
    istringstream in(line);int cap,x,y;require(bool(in>>cap));vector<Point> seed;
    while(in>>x){require(bool(in>>y));seed.emplace_back(x,y);}
    evaluate(id++,seed,cap,r);
  }
  cout<<"done "<<id<<" "<<r.starts<<" "<<r.afterRoad<<" "<<r.prefix<<" "<<r.roadPrefix<<" "<<r.ink<<" "<<r.roadInk<<" edge_stops "<<r.edgeStops<<endl;
}
