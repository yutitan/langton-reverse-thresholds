// Every unknown first read branches both ways; fixed cells force their values.
// At each depth the cheapest partial board is exactly the cheapest full seed,
// since all unread, unconstrained cells can be set white.
#define BG_LIB
#include "ant_gate_bg_evolve.cpp"
struct Audit {
  int8_t val[W*W];vector<int> minimum;vector<uint64_t> count;
  int cap;
  void run(int p,int h,int ink,int t){
    count[t]++;minimum[t]=min(minimum[t],ink);
    if(t==cap)return;
    int q=p-dirs[h],old=val[q];require(q>=W && q<W*(W-1) && q%W>0 && q%W<W-1);
    for(int after=0;after<2;after++){
      if(old>=0 && after!=old)continue;
      val[q]=1-after;
      run(q,(h+(after?-1:1))&3,ink+1-after-int(old==1),t+1);
    }
    val[q]=old;
  }
};
int main(int argc,char**argv){
 require(argc==3);init_words();objective=stoi(argv[1]);make_templates();
 Audit a;a.cap=stoi(argv[2]);a.minimum.assign(a.cap+1,999);a.count.assign(a.cap+1,0);
 for(int ph=0;ph<104;ph++){
   memset(a.val,-1,sizeof(a.val));int ink=0;
   for(auto [q,b]:templ[ph]){a.val[q]=b;ink+=b;}
   a.run(O,0,ink,0);
 }
 int minimum=999;for(int t=0;t<=a.cap;t++){
   minimum=min(minimum,a.minimum[t]);cout<<t<<" "<<a.minimum[t]<<" "<<minimum<<" "<<a.count[t]<<endl;
 }
}
