# 数据与运行日志

本目录保存本记录用到的主要数据表与运行日志。完整原始工件（含 413,982 条
首读清单与逐条跟踪结果，约 30 MB 解压）在
release v1.0.0 的资产 langton_reverse_thresholds_verification.zip 中。

## 射线与全平面

* ant_ray_thresholds.txt — 22 条射线的表：基点、开关数、unchanged_through
  （即 A）、first_lost（A+1）、start_at_depth40、largest_other_gap。
  由 verify/ant_ray_thresholds.py 从上游 TwoBlack/Level1Data.lean 生成。
* ant208_results.txt — 倒放 208 步、三格搜索、供应不等式与 12K−5 构造的
  数值记录。
* ant3_reverse_findings.txt — 两格 87 外部枚举的来源与分类计数
  （4,451,091 直接子项、32,824 补项、100,034 可伸长族、114,722 插入块等）。

## 14 格见证与 12K+2

* ant_gate_ordered.txt — 14 格有序见证的重放输出：K=1..40 的初始黑格数
  （14、26、38、50、62、122、482）以及 H/V 的起点与相位。
* ant_gate_first_results.txt — 首读颜色搜索的覆盖统计（535 条源轨迹、
  3,837,226 个起始位姿）。

## 三格的定向实验

* ant_gate_diagnosis.py 的输出（见 verify/results.txt）：88 步见证的 41 个
  首读格、6 处不符及其读取次数与最近读取时刻；11 格 101 步见证的唯一不符格。
* ant_gate_graft_results.txt — 把完整目标逆接到原前奏的定向搜索：
  416 个锚点、132,392,000 个供体端点；最长相容后缀 35,555 步，最低 21 格。
* ant_gate_contact_families.log — 固定 88 见证前两格的局部家族：81 个父对，
  合计 530,496 个直接分叉与 1,857 条无限射线；最长匹配分布
  70 个 58、2 个 59、8 个 68、1 个 88，均无完整周期。
* ant_gate_record_families.log — 围绕异常记录父对的 49 组父对：
  221,916 个直接分叉、1,084 条远端射线，最大异常计数仍为 285,176。

## 必要条件与有界前奏

* ant_gate_horizon.txt — 首读决策树穷举到 104/400/1000/2000 步的输出版本：
  最长倒放 33/43/58/78，见证与叶节点计数。
* cases500_sample.txt — 413,982 条“三格全在前 500 步读到”的初态清单的前
  200 行；cases500_counts.txt 记录总行数。
* ant_gate11_phases_0_51.txt、ant_gate11_phases_52_103.txt — 104 个相位的
  外读格预算阶梯；最后一行给出至多 24 个外读格时的最小值 13。
* ant_gate_bg_short*.txt — 前奏至多 30 步时 104K 步倒放的最小初始黑格数
  （K=1..11 与 104、208），用于 verify/ant_gate_bounded.py 的归纳检查。
* ant_gate_bg_startbank.txt、ant_gate_bg_dfs*.log — 无界前奏下 V² 的探索
  日志（最优仍为 20 格，无全局排除意义）。

## Lean 公理打印

* ant_gate_sharp_axioms.txt — AntSharp.ray_threshold_exact 与
  AntSharp.threshold_table 的公理依赖。
* ant_gate_ordered_axioms.txt — AntGate.ordered14 的公理依赖。
