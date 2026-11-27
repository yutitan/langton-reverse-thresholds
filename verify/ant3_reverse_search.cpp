// C++17. Read tasks from a text manifest. P x y u v cutoff forks a third
// black cell at every first visit before cutoff. T x y u v i j runs a triple.
// Every branch is followed to the existing geometric infinite-tail test.
#define main previous_scan_main
#include "ant2_extremum.cpp"
#undef main
using Triple = array<int, 6>;
struct Node {
  array<int, 2> next{-1, -1};
  int link = 0, depth = 0;
};
vector<Node> trie(1);
int inverse_limit = period;
void init_detector() {
  string inverse = doubled.substr(0, 104);
  reverse(inverse.begin(), inverse.end());
  for (char &c : inverse)
    c ^= 1;
  const string single = inverse;
  inverse += single + single;
  for (int phase = 0; phase < 104; ++phase) {
    int u = 0;
    for (int i = 0; i < inverse_limit; ++i) {
      int b = inverse[phase + i];
      if (trie[u].next[b] < 0) {
        trie[u].next[b] = int(trie.size());
        Node n;
        n.depth = trie[u].depth + 1;
        trie.push_back(n);
      }
      u = trie[u].next[b];
    }
  }
  vector<int> queue;
  for (int b : {0, 1})
    queue.push_back(trie[0].next[b]);
  for (size_t k = 0; k < queue.size(); k++) {
    int u = queue[k];
    for (int b : {0, 1}) {
      int v = trie[u].next[b], f = trie[trie[u].link].next[b];
      if (v < 0)
        trie[u].next[b] = f;
      else {
        trie[v].link = f;
        queue.push_back(v);
      }
    }
  }
}
struct Match {
  int node = 0, best = 0, end = 0;
  void step(int b, int t) {
    node = trie[node].next[b];
    if (trie[node].depth > best) {
      best = trie[node].depth;
      end = t;
    }
  }
};
struct Rank {
  int score = -1, end = 0;
  Triple seed{};
  void put(int n, int t, Triple p) {
    if (n > score || (n == score && p < seed)) {
      score = n;
      end = t;
      seed = p;
    }
  }
};
struct Stats {
  Rank reversals, anomalies;
  long long runs = 0, hits = 0, double_hits = 0;
};
void record(Board &board, State a, Match m, Triple seed, Stats &stats) {
  string block;
  block.reserve(104);
  int check = 0;
  for (; a.time < 1200000;) {
    int start = a.pos, heading = a.heading;
    block.clear();
    bool probe = (++check % 8) == 0;
    int x = xof(a.pos), y = yof(a.pos);
    require(abs(x) + 104 < half && abs(y) + 104 < half);
    board.box.add(x, y, 104);
    for (int i = 0; i < 104; i++) {
      int b = board.ink[a.pos];
      board.ink[a.pos] ^= 1;
      a.heading = (a.heading + 1 - 2 * b) & 3;
      a.pos += delta[a.heading];
      a.mask = (2 * a.mask + b) & 1023;
      if (++a.time >= 10)
        a.count += bad[a.mask];
      m.step(b, a.time);
      if (probe)
        block.push_back(char(b));
    }
    if (probe && permanent(board, start, heading, block)) {
      // Any later 104-window is fully canonical. Also include the
      // maximal shorter inverse substring inside the infinite highway.
      for (int k = 0; k < inverse_limit; k++)
        m.step(block[k % period], a.time + k + 1);
      stats.anomalies.put(a.count, 0, seed);
      stats.reversals.put(m.best, m.end, seed);
      ++stats.runs;
      if (m.best >= period)
        ++stats.hits;
      if (m.best == 2*period)
        ++stats.double_hits;
      return;
    }
  }
  throw runtime_error("uncertified tail");
}
struct SearchJob {
  char kind;
  Triple p;
  int cutoff = 0;
  int moving_mask = 7;
  vector<pair<int,int>> arbitrary;
  vector<pair<int,int>> fixed_group, shifted_group;
};
void parent(const SearchJob &j, Board &source, Board &child, vector<int> &seen,
            int id, Stats &st) {
  vector<pair<int, int>> fixed, moving;
  if(j.kind=='S'){
    fixed=j.fixed_group; moving=j.shifted_group;
  }else if (j.kind == 'G' || j.kind == 'M') {
    for (int i = 0; i < 6; i += 2)
      ((j.moving_mask & (1 << (i/2))) ? moving : fixed).emplace_back(j.p[i], j.p[i + 1]);
  } else if (j.kind == 'F') {
    fixed = {{j.p[0], j.p[1]}};
    moving = {{0, 0}};
  } else {
    fixed = {{j.p[0], j.p[1]}, {j.p[2], j.p[3]}};
    moving = {{0, 0}};
  }
  for (auto [x, y] : fixed)
    source.seed(x, y);
  set<pair<int, int>> tried;
  State a;
  Match m;
  bool first_seen = false;
  for (int i = 0; i < j.cutoff; i++) {
    int p = a.pos, px = xof(p), py = yof(p);
    require(abs(px) < half - 1 && abs(py) < half - 1);
    source.box.add(px, py);
    if (j.kind == 'F' && seen[p] != id && px == j.p[0] && py == j.p[1]) {
      require(i == j.p[2]);
      first_seen = true;
    }
    if (seen[p] != id && (j.kind != 'F' || i > j.p[2])) {
      for (auto [bx, by] : moving) {
        int dx = px - bx, dy = py - by;
        if (!tried.insert({dx, dy}).second)
          continue;
        vector<pair<int, int>> seed = fixed;
        for (auto [x, y] : moving)
          seed.emplace_back(x + dx, y + dy);
        if (set<pair<int, int>>(seed.begin(), seed.end()).size() != seed.size())
          continue;
        child.copy_from(source);
        for (auto [x, y] : moving) {
          int q = cell(x + dx, y + dy);
          require(seen[q] != id && !source.ink[q]);
          child.seed(x + dx, y + dy);
        }
        Triple coords{};
        if(j.kind=='S'){
          coords[0]=dx;coords[1]=dy;
        }else {
          for (size_t n = 0; n < seed.size(); n++) {
            coords[2 * n] = seed[n].first;
            coords[2 * n + 1] = seed[n].second;
          }
        }
        record(child, a, m, coords, st);
        child.clear();
      }
    }
    seen[p] = id;
    int b = source.ink[p];
    source.ink[p] ^= 1;
    a.heading = (a.heading + 1 - 2 * b) & 3;
    a.pos += delta[a.heading];
    a.mask = (2 * a.mask + b) & 1023;
    if (++a.time >= 10)
      a.count += bad[a.mask];
    m.step(b, a.time);
  }
  if (j.kind == 'F')
    require(first_seen);
  source.clear();
}
int main(int argc, char **argv) {
  require(argc == 3 || (argc == 4 && string(argv[3]) == "--208"));
  if (argc == 4) inverse_limit = 2*period;
  init_words();
  init_detector();
  ifstream input(argv[1]);
  require(input.good());
  vector<SearchJob> jobs;
  string line;
  while (getline(input, line)) {
    if (line.empty() || line[0] == '#')
      continue;
    istringstream ss(line);
    SearchJob j{};
    ss >> j.kind;
    if(j.kind=='S'){
      int nfix,nmove,x,y;require(bool(ss>>j.cutoff>>nfix>>nmove) && nfix>=0 && nmove>=1 && j.cutoff>0);
      for(int i=0;i<nfix+nmove;i++){require(bool(ss>>x>>y));(i<nfix?j.fixed_group:j.shifted_group).emplace_back(x,y);}
      jobs.push_back(move(j));continue;
    }
    if(j.kind=='N'){
      int n,x,y; require(bool(ss>>n) && n>=0);
      for(int i=0;i<n;i++){require(bool(ss>>x>>y));j.arbitrary.emplace_back(x,y);}
      require(set<pair<int,int>>(j.arbitrary.begin(),j.arbitrary.end()).size()==j.arbitrary.size());
      jobs.push_back(move(j)); continue;
    }
    const map<char, int> fields{{'M',6},{'P', 4}, {'T', 6}, {'B', 4}, {'G', 6},
                                {'Z', 0}, {'U', 2}, {'F', 3}};
    int coordinates = fields.at(j.kind);
    for (int i = 0; i < coordinates; i++)
      require(bool(ss >> j.p[i]));
    if (j.kind == 'M') require(bool(ss >> j.moving_mask) && j.moving_mask>0 && j.moving_mask<8);
    if (j.kind == 'P' || j.kind == 'G' || j.kind == 'F' || j.kind == 'M')
      require(bool(ss >> j.cutoff) && j.cutoff > 0);
    jobs.push_back(j);
  }
  require(!jobs.empty());
  int nt = stoi(argv[2]);
  require(nt > 0);
  atomic<size_t> index{0};
  mutex out;
  vector<thread> pool;
  for (int i = 0; i < nt; i++)
    pool.emplace_back([&] {
      Board source, child;
      vector<int> seen(side * side, -1);
      for (;;) {
        size_t k = index++;
        if (k >= jobs.size())
          break;
        auto j = jobs[k];
        Stats st;
        if (j.kind == 'P' || j.kind == 'G' || j.kind == 'F' || j.kind == 'M' || j.kind=='S')
          parent(j, source, child, seen, int(k), st);
        else if(j.kind=='N'){
          for(auto [x,y]:j.arbitrary)child.seed(x,y);
          record(child,State(),Match(),{},st);
          child.clear();
        }else {
          set<pair<int, int>> cells;
          int seed_size =
              j.kind == 'U' ? 1 : (j.kind == 'Z' ? 0 : (j.kind == 'B' ? 2 : 3));
          for (int h = 0; h < 2 * seed_size; h += 2) {
            cells.insert({j.p[h], j.p[h + 1]});
            child.seed(j.p[h], j.p[h + 1]);
          }
          require(int(cells.size()) == seed_size);
          record(child, State(), Match(), j.p, st);
          child.clear();
        }
        lock_guard<mutex> lock(out);
        cout << k << " " << st.runs << " " << st.hits;
        for (const Rank &r : {st.reversals, st.anomalies}) {
          cout << " " << r.score << " " << r.end;
          for (int z : r.seed)
            cout << " " << z;
        }
        if (inverse_limit == 2*period) cout << " " << st.double_hits;
        cout << '\n';
      }
    });
  for (auto &t : pool)
    t.join();
}
