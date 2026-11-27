# 复现与验证

本文件给出每一层证据的最短命令。所有命令在仓库根目录或对应子目录运行；
Python 3.10+，Lean 4.30.0，g++（C++17）。

## 0. 快速检查（不需要 Lean、不需要上游仓库）

    cd verify
    bash run_all.sh

run_all.sh 会运行：88 诊断与 11 格诊断、14 格 + 12K+2 重放、有界前奏、
供应常数、倒放 208 见证、独立自检脚本，并把输出同时写入 results.txt。

## 1. 自包含独立复核

    cd verify
    python3 dsh_independent_checks.py

该脚本不 import 交付的验证程序；它自己实现 Langton 模拟、H/V 定义与
首读颜色构造，重算 14 格见证、12K+2 的 K=1..3、88 诊断表、11 格到 110、
两格 87、三格 88、78/86 两个必要条件见证，并抽样检查 413,982 清单。
详细说明与结果见 REPORT.md。

## 2. 22 条射线的精确阈值表

需要上游仓库（固定提交 95e896e…）：

    python3 verify/ant_ray_thresholds.py <upstream>/lean/TwoBlack/Level1Data.lean

输出 22 行 A 值与特殊射线信息；对照 data/ant_ray_thresholds.txt。

## 3. 三格必要条件与有界前奏（C++ 穷举）

    cd verify
    g++ -O3 -std=c++17 -pthread ant_gate_horizon.cpp -o horizon
    ./horizon 104 3
    ./horizon 400 3
    ./horizon 1000 3
    ./horizon 2000 3

输出应与 data/ant_gate_horizon.txt 一致：最长 33/43/58/78，最后一行
leaves 1 390 75985 10246877。要生成 413,982 条清单：

    ./horizon 500 3 cases500.in

再重放并审计需要 ant3_reverse_search.cpp 与 ant_gate_early_audit.py，
命令见 data/README.md 与工件包内 REPRODUCE.txt。

    g++ -O3 -std=c++17 -pthread ant_gate_bg_short.cpp -o short
    for k in 3 4 5 6 7 8 9 10 11; do ./short $((104*k)) 30 > ant_gate_bg_short_K$k.txt; done
    python3 ant_gate_bounded.py

## 4. 通道家族与定向搜索

    g++ -O3 -std=c++17 -I<upstream>/code ant3_tail_families.cpp -o tail
    g++ -O3 -std=c++17 -pthread ant3_reverse_search.cpp -o replay
    python3 ant_gate_contact_families.py ./tail ./replay tmp-contact --radius 4 > contact.log
    python3 ant_gate_contact_families.py ./tail ./replay tmp-record --radius 3 --record > record.log

结果对照 data/ant_gate_contact_families.log 与 data/ant_gate_record_families.log。

## 5. Lean 构建与公理检查

见 lean/README.md。要点：复制 lean/*.lean 到上游工程 lean/ 根目录，
先 lake build TwoBlack.Level1 TwoBlack.Parent0，再按依赖顺序编译，最后

    lake env lean check_axioms.lean

输出应只含 propext、Classical.choice、Quot.sound 与 native_decide
归约公理，不含 sorryAx。

## 6. 完整工件

release v1.0.0 的资产 langton_reverse_thresholds_verification.zip（https://github.com/yutitan/langton-reverse-thresholds/releases/tag/v1.0.0）是交付时的完整验证包，
包含全部 Lean 源码、C++/Python 程序、413,982 条首读清单及逐条结果、
SHA256SUMS.txt 与 REPRODUCE.txt。
