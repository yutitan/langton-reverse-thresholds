#pragma once
// Longest suffix that is also a prefix of a rotation of the inverse highway.
#define main ant_gate_legacy_main
#include "ant2_extremum.cpp"
#undef main
struct GateNode {array<int,2> next{-1,-1};int fail=0,depth=0;};
vector<GateNode> trie(1);
void init_detector(){
  for(int p=0;p<104;p++){
    int u=0;
    for(int j=0;j<104;j++){
      int b=1-doubled[103-(p+j)%104];
      if(trie[u].next[b]<0){
        int v=trie.size();trie[u].next[b]=v;int d=trie[u].depth;
        trie.emplace_back();trie.back().depth=d+1;
      }
      u=trie[u].next[b];
    }
  }
  vector<int> todo{trie[0].next[0],trie[0].next[1]};
  for(size_t i=0;i<todo.size();i++){
    int u=todo[i];
    for(int b:{0,1}){
      int v=trie[u].next[b],f=trie[trie[u].fail].next[b];
      if(v<0)trie[u].next[b]=f;
      else {trie[v].fail=f;todo.push_back(v);}
    }
  }
}
