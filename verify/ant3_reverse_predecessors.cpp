// Beam search over finite partial boards that force one exact inverse block.
// For every retained predecessor, setting all unspecified cells white gives an
// actual finite witness. Pruning affects discovery only.
#define main earlier_scan_main
#include "ant2_extremum.cpp"
#undef main
#include <bitset>
#include <unordered_set>

namespace predecessor {
constexpr int width = 96, area = width * width,
              center = (width / 2) * (width + 1);
constexpr int step[] = {width, 1, -width, -1};
using Bits = bitset<area>;
struct Partial {
  Bits known, black;
  int pos = center, h = 0, count = 0;
  uint64_t hash = 0;
};
uint64_t mix(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}
Partial root(int phase, int periods=1) {
  Partial a;
  int p = center, h = 0;
  string inverse = doubled.substr(0, 104);
  reverse(inverse.begin(), inverse.end());
  Bits visited_parity;
  for (int j = 0; j < period*periods; j++) {
    int b = 1 - inverse[(phase + j) % 104];
    if (!a.known[p]) {
      a.known.set(p);
      a.black[p] = b;
      a.count += b;
    }
    require((int(a.black[p]) ^ int(visited_parity[p])) == b);
    visited_parity.flip(p);
    h = (h + 1 - 2 * b) & 3;
    p += step[h];
  }
  return a;
}
mutex print_lock;
void report(const Partial &a, int phase, int depth) {
  lock_guard<mutex> lock(print_lock);
  cout << "mass " << a.count << " phase " << phase << " depth " << depth
       << " seed";
  for (int p = 0; p < area; p++)
    if (a.black[p]) {
      int x = p % width - a.pos % width, y = p / width - a.pos / width;
      // Rotate initial heading back to north.
      for (int j = 0; j < a.h; j++) {
        int u = x;
        x = -y;
        y = u;
      }
      cout << " " << x << " " << y;
    }
  cout << endl;
}
struct Choice {
  int score, parent, black_after, q;
  uint64_t hash;
};
void run(int phase, int beam, int levels, int variant) {
  vector<Partial> current{root(phase)}, next;
  int best = current[0].count;
  report(current[0], phase, 0);
  uint64_t salt = mix(phase + variant * 104);
  for (int depth = 1; depth <= levels && !current.empty(); depth++) {
    vector<Choice> choices;
    unordered_set<uint64_t> seen;
    for (size_t i = 0; i < current.size(); i++) {
      const auto &a = current[i];
      int q = a.pos - step[a.h];
      int x = q % width, y = q / width;
      if (x < 4 || y < 4 || x >= width - 4 || y >= width - 4)
        continue;
      bool known = a.known[q];
      for (int after = 0; after < 2; after++) {
        if (known && after != a.black[q])
          continue;
        int before = 1 - after, count = a.count + before - (known && after);
        int h = (a.h + (after ? -1 : 1)) & 3;
        uint64_t hash = a.hash;
        if (!known)
          hash ^= mix(2 * q);
        if (bool(before) != a.black[q])
          hash ^= mix(2 * q + 1);
        uint64_t key = hash ^ mix(2 * area + 4 * q + h);
        if (!seen.insert(key).second)
          continue;
        int nearby = 0;
        for (int dy = -3; dy <= 3; dy++)
          for (int dx = -3; dx <= 3; dx++)
            if (dx || dy)
              nearby +=
                  (4 - max(abs(dx), abs(dy))) * a.black[q + dx + width * dy];
        int ahead = q - step[h];
        int score = count * (100 + (variant % 3) * 55) -
                    nearby * (3 + (variant % 2)) - 32 * a.black[ahead] +
                    int(mix(key ^ salt ^ depth) % 137);
        choices.push_back({score, int(i), after, q, hash});
      }
    }
    if (int(choices.size()) > beam) {
      nth_element(
          choices.begin(), choices.begin() + beam, choices.end(),
          [](const Choice &a, const Choice &b) { return a.score < b.score; });
      choices.resize(beam);
    }
    next.clear();
    for (auto c : choices) {
      next.push_back(current[c.parent]);
      auto &a = next.back();
      a.count += (1 - c.black_after) - (a.known[c.q] && c.black_after);
      a.known.set(c.q);
      a.black[c.q] = 1 - c.black_after;
      a.pos = c.q;
      a.h = (a.h + (c.black_after ? -1 : 1)) & 3;
      a.hash = c.hash;
      if (a.count < best) {
        best = a.count;
        report(a, phase, depth);
      }
      if (best <= 3)
        return;
    }
    current.swap(next);
  }
}
} // namespace predecessor
#ifndef ANT_PREDECESSOR_LIBRARY
int main(int argc, char **argv) {
  require(argc == 7);
  init_words();
  int beam = stoi(argv[1]), levels = stoi(argv[2]), variant = stoi(argv[3]);
  int begin = stoi(argv[4]), end = stoi(argv[5]), jobs = stoi(argv[6]);
  require(begin >= 0 && end <= 104 && jobs > 0 && beam > 0);
  atomic<int> index{begin};
  vector<thread> pool;
  for (int t = 0; t < jobs; t++)
    pool.emplace_back([&] {
      for (;;) {
        int phase = index++;
        if (phase >= end)
          break;
        predecessor::run(phase, beam, levels, variant);
      }
    });
  for (auto &t : pool)
    t.join();
}
#endif
