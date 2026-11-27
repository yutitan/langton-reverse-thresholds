# 大模型的小练习（四）：朗顿蚂蚁的倒放门槛

**LLM Exercises IV — reverse-play thresholds for Langton's ant**

**Author:** [@yutitan](https://github.com/yutitan) · **Date:** 2026-11-27
· **Derived with:** GPT 6.2 Astra (OpenAI Codex, model gpt-6.2-astra),
independently verified with DeepSeek Harness — see [Provenance](#provenance)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24583889.svg)](https://doi.org/10.5281/zenodo.24583889) · **Archived release:** v1.0.0 (2026-11-27)

> 本仓库是“大模型的小练习”系列的第四篇，是一份个人 AI 使用记录，不是论文，
> 不作优先权主张。系列第一篇：
> [Counterexamples to *Written on the Wall II* conjecture #138](https://github.com/yutitan/wowii-conjecture-138)
> — [DOI 10.5281/zenodo.24540807](https://doi.org/10.5281/zenodo.24540807)；
> 第二篇：
> [Exact escape time of Langton's ant on three-row boards](https://github.com/yutitan/langton-ant-three-rows)
> — [DOI 10.5281/zenodo.24540968](https://doi.org/10.5281/zenodo.24540968)；
> 第三篇：
> [Explicit escape-time bound for Langton's ant on n×n boards](https://github.com/yutitan/langton-ant-square-bound)
> — [DOI 10.5281/zenodo.24541703](https://doi.org/10.5281/zenodo.24541703)。

## 摘要

朗顿蚂蚁：白格右转、黑格左转，翻色后前进一格。允许蚂蚁先在平面任意处放置
至多 m 个初始黑格，自由运行任意久，问它能让转向词连续匹配一段“倒放高速公路”
多久。把空白轨迹从时刻 9,977 开始的 104 个转向记为正词 H，把 H 逆序并交换左右
得到 V；L_m 是至多 m 个初始黑格能实现的连续 V 循环词长度的上确界。

本记录给出：

| 初始预算 | 最长倒放 | 取到的时刻 / 相位 | 证据 |
| ---: | ---: | :---: | --- |
| 0 格 | **32** | 1,041 / 4 | 全时间 Lean 定理 |
| 1 格 | **58** | 29,393 / 6 | 全平面、全时间 Lean 定理 |
| 2 格 | **87** | 14,770 / 92 | 上游两格覆盖 + 完整外部枚举 |
| 3 格 | **至少 88** | 214,688 / 90 | 88 的见证已由 Lean 重放；全局最大值未知 |

    3 <= M_104 <= 12        3 <= M_208 <= 20

其中 M_N 是能实现连续 N 步倒放的最少初始黑格数。11 格已有 101 步；
立即（时刻 0、无前奏）倒放 104 步恰需 23 格，而保留前奏可把需求降到 12 格。

其余结果（详细陈述与证明见 [note](note/note.md)）：

1. **单黑格射线的精确可分辨阈值。** 上游分类给出 22 条射线，深度每增加一级
   相当于沿 (−2,−2) 再移远一格。对每条射线 j，存在精确常数 A_j（22 个值介于
   4,978 与 5,082），使深度 40+k 与同射线任意更深位置之间，长度不超过
   A_j+104k 的转向词集合完全相同，而长度 A_j+104k+1 时第一次有词消失。
   最后的组合归纳已整体通过 Lean（AntSharp.ray_threshold_exact）。
2. **一条 14 格见证把正向与倒放接在一起。** 同一只蚂蚁从时刻 9,977 起连续
   走出 2,453 步标准正向词，又从时刻 174,341 起按相位 89 倒放 119 步，第 120
   步分岔。保留这段 2,453 步前奏，12K+2 个初始黑格足以倒放 K 个完整周期
   （K ≥ 1）。单例由 Lean 核验；一般构造由首读颜色计数、有限核验与归纳给出。
3. **三格的两个必要条件。** 若三格能倒放一个完整周期，那么（i）该周期必须在
   第 2,000 步之后才完成——截止第 2,000 步的最长倒放为 78（见证 (3,5)、
   (−3,4)、(−7,4)）；（ii）至少一个初始黑格在头 500 步内尚未读到——三格全在
   前 500 步读到的 413,982 个初态，任意晚的倒放最长也只有 86（见证 (2,4)、
   (5,4)、(6,3)）。
4. **有界前奏的精确值。** 前奏至多 30 步时，倒放 104K 步恰需 12K+6 格；
   前奏任意长但至多读 24 个目标路径外的不同格时，倒放 104 步恰需 13 格。
5. **供应不等式。** 对将要连续倒放 K 个周期的轨迹，
   6K ≤ m+u+9n+15h+12；若所有平行路段都与被倒放的前向模板同向，则
   9K ≤ m+u+7n+14h+15（m 初始黑格数；n/u/h 为前奏中平行标准段、剩余单步、
   垂直标准段的数量）。

三格能否倒放完整周期，本记录没有判定；这也与异常计数问题
D(3) ≥ 285,176（有限性未判定）是不同命题。

## 证明与文稿

完整推导、记号与证据分级见 [note/note.md](note/note.md)（同版
[HTML](note/note.html)、[PDF](note/note.pdf)）。结构：

* 单格 58：把单黑格位置归约到空白轨迹前 14,768 步的 2,388 个位置、44 个
  衔接位置与 22 条无限射线，再用上游通道耦合与 Lean 有限证书排除 59。
* 22 射线阈值：复制一个 104 步块时，标记（相邻相隔 104 的不同字母）的插入
  恒等式把“只有包住切点的那对标记被拉开”变成精确的间距记账；22 行有限数据
  由 Lean 重算（AntGapData.gap_table_checked），通用引理与归纳由
  AntSharp.ray_threshold_exact 收口。
* 88 见证的差距：按原位姿补完 104 步需要改正 6 个格子，每格此前被读过
  31 至 38 次；把完整目标逆接原前奏最多保留 35,555 步，最低仍需 21 个初始
  黑格。11 格的 101 步见证只差一个此前从未读过的格子，补黑后达到 110 步。
* 14 格构造：给定目标词，按几何路径求各格首读所需的黑白；只有前奏中从未
  读取的格子可自由补色。对 535 条源轨迹的 3,837,226 个起始位姿逐相位检查，
  得到上述见证；沿倒放位移分出的 22 个类给出 12K+2。
* 两个必要条件：用首读颜色决策树穷举全平面至多三格初态到给定时限；以及
  对 413,982 个“三格全读”初态逐个跟踪到带证书的永久高速公路。

## 验证

本记录的关键声称分三层证据：

1. **Lean 4.30 形式化**（单格 58 全平面定理、22 射线阈值、88 见证、
   立即 104 的 23 格下界、加权翻格恒等式等）。构建方法见
   [lean/README.md](lean/README.md)，公理打印见 lean/axioms.txt。
2. **外部穷举与 C++ 检查器**（两格 87 的全局上界、三格的两个必要条件、
   有界前奏精确值、通道家族实验）。程序在 [verify/](verify/)，运行日志与
   数据在 [data/](data/)；完整命令见 [VERIFY.md](VERIFY.md)。
3. **独立复核**：DeepSeek Harness 用自写模拟器重算全部见证，重跑搜索程序，
   从源码重建 Lean 模块并打印公理；报告在
   [verify/REPORT.md](verify/REPORT.md)，自包含检查脚本
   [verify/dsh_independent_checks.py](verify/dsh_independent_checks.py)。

快速检查（Python 3.10+）：

    cd verify
    bash run_all.sh

## 本记录是什么，不是什么

* 由 GPT 6.2 Astra（OpenAI Codex）在 2026-11-27 的桌面端会话中推导，写出
  Lean/C++/Python；由 DeepSeek Harness 独立复核；人类作者（@yutitan）发起、
  指导并发布。AI 不是法律作者。
* 不是同行评审论文；不作优先权主张；“倒放阈值”这一提法不声称新颖。
* 依赖：imfinn 两黑格工程固定提交 95e896e…（22 条射线、通道检查、
  TwoBlack.Parent0 与两格覆盖）与 Hao Ke 的单黑格定理（22 通道）。
* 信任边界：Lean 的有限布尔判定使用 native_decide；两格 87 的整套外部
  枚举没有 Lean 化；三格两个必要条件是基于 C++ 穷举的必要条件，不是三格
  全局上界；12K+2 家族的单例已 Lean 化，通用构造是纸面归纳加有限核验。
* 未解决：三格能否完成一次完整 104 倒放；M_104、M_208 的精确值；
  D(3) 的有限性。

## 定位

* 系列第（四）篇。与（二）（三）同属朗顿蚂蚁，但问题不同：这里问“倒放高速
  公路能走多长”，不涉及出界时间与棋盘形状。
* 上游：结构（22 条射线、深度 40 参数化、首次接触覆盖）来自 imfinn 的两格
  工程；本记录的增量是倒放因子、精确阈值、两个三格必要条件与相应 Lean 化。
* 与异常计数问题无关：D(3) 是另一套度量（长度 10 的非标准窗口总数），本记录
  只报告其已知下界 285,176，不声称推进其有限性。

## Citation

见 [CITATION.cff](CITATION.cff)。发布记录：v1.0.0（2026-11-27），Zenodo
归档 DOI [10.5281/zenodo.24583889](https://doi.org/10.5281/zenodo.24583889)
（概念 DOI [10.5281/zenodo.24583888](https://doi.org/10.5281/zenodo.24583888)）；
DOI 只指向归档快照，之后的提交不属于该版本。

    @software{yutitan_llm_exercises_iv,
      author  = {yutitan},
      title   = {大模型的小练习（四）：朗顿蚂蚁的倒放门槛},
      year    = {2026},
      doi     = {10.5281/zenodo.24583889},
      note    = {Series: 大模型的小练习 (LLM Exercises IV); derived with GPT 6.2 Astra,
                 independently verified with DeepSeek Harness},
      url     = {https://github.com/yutitan/langton-reverse-thresholds}
    }

## Provenance

见 [PROVENANCE.md](PROVENANCE.md)：时间线、AI 分工、依赖、信任边界与文件哈希。
