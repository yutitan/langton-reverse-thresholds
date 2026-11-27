// Compile with -I/path/to/langton-two-black/code at revision
// 95e896e3035e992e48ce9d28a5ded8568c86e835. Each output row certifies a whole ray of translations
// of the moving group.
#define main upstream_calculus_main
#include "calculus.cpp"
#undef main
#include "ant3_groups.hpp"

int check_families(const vector<Groups::Point> &fixed, const vector<Groups::Point> &moving) {
    for (auto p : fixed)
        if (!Board::inb(p.first, p.second))
            return 2;
    auto blank = RU.certify({}, 0, CAP);
    if (!blank.ok)
        return 3;
    CW = canon(blank.word);
    set<string> legal;
    auto twice = CW + CW;
    for (int j = 0; j < 104; ++j)
        legal.insert(twice.substr(j, 10));
    if (legal.size() != 84)
        return 3;
    auto cert = RU.certify(fixed, 0, CAP);
    if (!cert.ok || canon(cert.word) != CW || abs(cert.ux) != 2 || abs(cert.uy) != 2)
        return 3;
    const int vx = cert.ux, vy = cert.uy;
    set<pair<int, int>> support;
    for (ll j = cert.s; j < cert.s + 104; ++j)
        for (auto [bx, by] : moving)
            support.insert({RU.X[j] - bx, RU.Y[j] - by});
    int heads = 0, maxDepth = 0;
    for (auto [x, y] : support) {
        if (support.count({x + vx, y + vy}))
            continue;
        ++heads;
        Fam F;
        F.v.push_back({vx, vy});
        for (auto [u, v] : fixed)
            F.blk.push_back({u, v, 0});
        for (auto [bx, by] : moving)
            F.blk.push_back({bx + x, by + y, 1});
        bool covered = false;
        string reason;
        for (int n = 40; n <= 400; n += 4) {
            for (auto [bx, by] : moving)
                if (!Board::inb(bx + x + n * vx, by + y + n * vy))
                    return 4;
            Info replay = verify(F, {n});
            if (!replay.ok) {
                reason = replay.why;
                continue;
            }
            auto &cross = replay.P.at(0).tr;
            string trace;
            for (ll t = 0; t < replay.T; t++)
                trace += char('0' + RU.R[t]);
            int last = -105;
            for (auto tr : cross) {
                int m = tr[3];
                if (m <= last + 104 || m < 0 || m + 104 > replay.T)
                    return 5;
                if (canon(trace.substr(m, 104)) != CW) {
                    cerr << "nonstandard inserted word " << x << " " << y << " " << n << " " << m
                         << "\n";
                    return 6;
                }
                last = m;
            }
            if (canon(trace.substr(replay.c.s, 104)) != CW)
                return 5;
            int defects = 0;
            for (size_t i = 0; i + 10 <= trace.size(); i++)
                defects += !legal.count(trace.substr(i, 10));
            cout << "ray " << x << " " << y << " depth " << n << " switches " << cross.size()
                 << " defects " << defects << "\n";
            maxDepth = max(maxDepth, n);
            covered = true;
            break;
        }
        if (!covered) {
            cerr << "unresolved " << x << " " << y << " " << reason << "\n";
            return 7;
        }
    }
    if (!heads)
        return 8;
    cout << "parent " << cert.s << " heads " << heads << " drift " << vx << " " << vy
         << " finite_cutoff " << cert.s + 104 * (maxDepth + 1) << "\n";
    return 0;
}

int main(int argc, char **argv) {
    if (argc == 2 && string(argv[1]) == "--one")
        return check_families({}, {{0,0}});
    Groups groups(argc, argv, 8);
    return check_families(groups.fixed, groups.moving);
}
