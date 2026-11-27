# Provenance and AI disclosure

[Back to the README](README.md)

本仓库是“大模型的小练习”系列的第四篇，是一份个人 AI 辅助探索的公开记录。
它不作优先权主张；AI 系统不是法律作者。

## 系列

* （一）[Counterexamples to Written on the Wall II conjecture #138](https://github.com/yutitan/wowii-conjecture-138)
  — DOI 10.5281/zenodo.24540807
* （二）[Exact escape time of Langton's ant on three-row boards](https://github.com/yutitan/langton-ant-three-rows)
  — DOI 10.5281/zenodo.24540968
* （三）[Explicit escape-time bound for Langton's ant on n x n boards](https://github.com/yutitan/langton-ant-square-bound)
  — DOI 10.5281/zenodo.24541703
* （四）本仓库：朗顿蚂蚁的倒放门槛

## 时间线（2026-11-27，本地时间 UTC+8）

| 时间 | 事件 | 证据 |
| --- | --- | --- |
| 09:52–10:12 | GPT 续接被中断的工作：覆盖、全局与间距数据模块（AntPrepared、AntCoverage、AntSplice、AntRays、AntGlobal、AntMarkers、AntGapData、AntLong、AntLost） | 文件时间戳 |
| 14:49–15:44 | AntSharp 系列与 AntGateWitness；22 条射线阈值的最后归纳接入 Lean | 文件时间戳 |
| 15:39–16:00 | 三格定向搜索（horizon、gate、graft、first-read）、14 格见证、稿件与验证包 | data/、工件包 |
| 16:04–16:58 | DeepSeek Harness 独立复核：自写模拟器重算见证、重跑搜索、从源码重建 Lean、修正稿件非数学表述并组装仓库 | verify/REPORT.md |
| 17:00 前后 | GitHub 发布 release v1.0.0 | 本仓库 release |
| 17:48 | Zenodo 归档 release v1.0.0：DOI 10.5281/zenodo.24583889 | zenodo.org/records/24583889 |

该 Codex 线程（UUID 01a212d0-4743-7213-8b9e-22a59d508eac）在 2026-11-26 23:29
曾因用量上限中断，2026-11-27 04:02 由 lead 按用户指示恢复；本记录使用
2026-11-27 的后续产出。更早的同线程工作（D(2)/D(3) 与 ant208）不属于本记录。

## What the AI systems did

* **GPT 6.2 Astra**（OpenAI Codex，模型 gpt-6.2-astra）：推导了全部数学结果，
  写出 Lean/C++/Python 程序与稿件，并生成验证包；最终回答保存于
  [provenance/gpt-6.2-astra-answer.md](provenance/gpt-6.2-astra-answer.md)。
* **DeepSeek Harness**：独立复核——用自写模拟器重算全部见证，重编译并复跑
  C++/Python 检查器，从源码重建 5 个 Lean 模块并打印公理；修正稿件中两处
  时间/命名表述并补充外部枚举口径说明；组装并发布本仓库。复核记录见
  [verify/REPORT.md](verify/REPORT.md)，独立检查脚本
  [verify/dsh_independent_checks.py](verify/dsh_independent_checks.py)。
* **人类作者**（[@yutitan](https://github.com/yutitan)）：发起并指导整个过程，
  审阅结果，发布仓库，对内容负责。

## 依赖、信任边界与披露

* 上游 [imfinn/langton-two-black](https://github.com/imfinn/langton-two-black)
  固定提交 95e896e3035e992e48ce9d28a5ded8568c86e835：22 条射线的
  TwoBlack.Level1Data、level1_checks、TwoBlack.Parent0。本仓库只包含新增或
  改动的 Ant*.lean 模块，不包含上游源码。
* Hao Ke 的单黑格定理提供 22 通道归约；本记录不重新证明该定理。
* 两格 87 的全局上界依赖该工程的首次接触覆盖加外部穷举
  （data/ant3_reverse_findings.txt）；这部分没有 Lean 化。
* Lean 的有限布尔判定使用 native_decide（编译执行），属于本工程声明的
  信任边界。
* 三格的两个必要条件是对全平面初态的 C++ 穷举得到的必要条件，不是三格
  全局上界；12K+2 家族的单例已 Lean 化，通用构造是纸面归纳加有限核验。
* 未解决的公开问题：三格能否倒放一个完整周期；M_104、M_208 的精确值；
  D(3) 的有限性。

## Release and Zenodo

GitHub release: https://github.com/yutitan/langton-reverse-thresholds/releases/tag/v1.0.0 （2026-11-27，资产 langton_reverse_thresholds_verification.zip）。Zenodo 已归档该 release：记录 https://zenodo.org/records/24583889 ，版本 DOI 10.5281/zenodo.24583889（概念 DOI 10.5281/zenodo.24583888）。
DOI 只指向归档快照，之后的提交不属于该版本。

## Hashes

    README.md                                            7ae53692a2fcac010166c2db154b592d832f715530acc519fd8b4d76c660b670
    note/note.md                                         517210177b252708b8e7600ff10445a84482a57ada1f2342a8ac2ed5297cccb5
    note/note.html                                       05574b0c314e0b7ab4fd69997404cb148fa3bab4fc6b455bb05ed29d3bb2ba24
    note/note.pdf                                        7d4cfca898b741c5f580032a1d83362144b7ba177fb5c49fdd2e07822b5ef89c
    verify/run_all.sh                                    9c28fd5cc36d923993ff68278ddbf5554546335227cea7dc1b65ed47fee5900f
    verify/results.txt                                   3192359c757f3c2bfcdd834db7cf63a2de613d2fc5e5dfc7af692d85bf0b4a0f
    verify/dsh_independent_checks.py                     cfcb588f863f71e305cbb1b0be837fb4c4d5b40db2df83769c28fbeb8fc5d60d
    verify/REPORT.md                                     3869b44d400c0b58c75b1bb8b2a844cbe12fc1cd6629630b387cde30bfd9cfb1
    lean/AntSharp.lean                                   2925e4e43a933f9b4d32e2ac601d9b4a639dacf36b01926eddeedc0aef55d546
    lean/AntSharpBase.lean                               ee0aa1afb2e260f9702c587be2e3d8428cddc9517092b7f67cdab1441645c5a6
    lean/AntSharpInduction.lean                          45dc2a5703abe41b1b951471e2d818e9e9c019ad345f0ce9ed3f555088f3e8da
    lean/AntSharpWords.lean                              7d0f1dd06b1fb6ebb98c327ddc6ccd2533bf1516d194fccce957ad8997e36ba8
    lean/AntGateWitness.lean                             64e8db028ccef21780b0cb06aecf2864f8fdd24c54fc5b444b9cf6d10f55eb0a
    lean/AntGlobal.lean                                  435f1dc468b9fe6fdadfc74fa95ae605fce7c7561b9afcced5d4379e2b37d018
    data/ant_ray_thresholds.txt                          3e165bea0724141e8cbee043f6317e5d9945c1ca9218f40aa3ec974b6e681945
    data/ant_gate_horizon.txt                            129d8db9f1cdecf3f56d2fd0d4f73f07be5efef29dff1b8da21c6e30e5d4811f
    release asset langton_reverse_thresholds_verification.zip  910ca08c5636cf916e2a1b9af826ab7e678e539e64844dc0c9db35d486622227
