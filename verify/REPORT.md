# 独立复核报告（DeepSeek Harness）

日期：2026-11-27。复核对象：本仓库的稿件、Lean 模块、C++/Python 检查器与
工件包 langton_reverse_thresholds_verification.zip。复核人：DeepSeek Harness
（lead，独立于生成该结果的 GPT 6.2 Astra 会话）。

## 0. 结论

关键声称全部独立复现或复跑通过，未发现数学错误。具体地：

* 所有见证（14 格、12K+2、88 诊断、11 格到 110、两格 87、三格 88、78/86、
  0/1 格阶梯）用本报告作者自写的 Python 模拟器重算，数字逐项一致。
* 三个 C++ 穷举/定向搜索（首读决策树、通道家族、逐条跟踪）由本报告作者
  重新编译并复跑：horizon 到 104/400/1000/2000 的输出与交付日志逐字一致；
  413,982 条清单的行数、抽样与审计结果一致；通道家族日志的求和与极值一致。
* Lean 源码与工件包内源码 SHA-256 相同；5 个新增模块从源码重建成功
  （0 error），关键定理公理打印只含 propext、Classical.choice、Quot.sound
  与 native_decide 归约公理，无 sorryAx。
* 未独立复核：两格 87 的 4.45M 条外部枚举（只核对文档计数、见证与极值；
  2026-11-26 的另一轮复核曾复跑该流水线并得到 87）、35,555 步嫁接搜索、
  以及“启发式失败无全局意义”的说明。这些均已在 README 与 PROVENANCE 中
  声明为外部枚举或非全局证据。

## 1. 环境与方法

* 环境：WSL Ubuntu；Lean 4.30.0；Python 3.10+；g++（C++17）；4 核。
* 独立模拟器：白右黑左、翻色前进；从全白空白轨迹时刻 9,977 起读取 104 个
  转向得到 H；V 为 H 逆序并交换左右；匹配允许任意循环相位。
* 独立构造：按稿件描述重写“首读颜色”构造（给定目标词沿几何路径求首读
  所需颜色，只有前奏中从未读取的格子可自由补色），不 import 交付的构造程序。

## 2. 逐项独立重算

| 检查项 | 方法 | 结果 |
| --- | --- | --- |
| 0 格 32 步 @ (1041, 相位 4) | 自写模拟 | PASS |
| 1 格 58 步 @ (29393, 相位 6) | 自写模拟 | PASS |
| 14 格：t=9977 起 2,453 步标准正向词 | 自写模拟；第 2,454 步分岔 | PASS |
| 14 格：t=174341 相位 89 倒放 119 步 | 自写模拟；120 步失败 | PASS |
| 14 格 = 首读构造 K=1 的种子 | 自写构造 | PASS（14 格逐点相同） |
| 12K+2：K=1..3 的格数 14/26/38 | 自写构造 | PASS |
| K=2 种子复现 174,341 步前奏并匹配 208 步 | 自写模拟（实际匹配 223 步） | PASS |
| K=3 种子匹配 312 步 | 自写模拟（实际匹配 327 步） | PASS |
| 88 步见证：41 个首读格、6 处不符 | 自写诊断；对照稿件表格 | PASS（偏移/颜色/读取次数/最近时刻全部相同） |
| 三格 88 见证 88 步，89 步失败 | 自写模拟 | PASS |
| 11 格 101 步，102 步失败 | 自写模拟 | PASS |
| 11 格唯一不符格 (−7,−5) 从未读过；补黑后 110 步 | 自写诊断 + 模拟 | PASS |
| 两格 87 步 @ (14770, 相位 92)，88 步失败 | 自写模拟 | PASS |
| 三格必要条件 I：78 步见证结束于 1,894 | 自写 DP 求最长匹配 | PASS（起点 1,816、相位 34） |
| 三格必要条件 II：86 步见证起点 7,897 | 自写 DP | PASS（结束 7,983；三格首读 301/332/343，均 <500） |
| 413,982 条清单 | 行数精确 413,982；随机 200 条抽样 | PASS（三格互异且首读均 <500） |
| horizon 104/400/1000/2000 | 重新编译交付源码并运行 | PASS（最长 33/43/58/78，叶节点计数与日志逐字一致） |
| 413,982 条逐一跟踪审计 | 重跑交付审计脚本 | PASS（无完整周期；最大倒放 86，起点 7,897、相位 92、(2,4),(5,4),(6,3)） |
| 通道家族（半径 4） | 解析交付日志 | PASS（81 行；直接分叉 530,496，射线 1,857；极值分布 70×58、2×59、8×68、1×88；无完整周期） |
| 记录父对家族 | 解析交付日志 | PASS（49 行；直接分叉 221,916，射线 1,084；最大异常仍 285,176） |
| 有界前奏 12K+6（K=1..11） | 重跑交付程序 | PASS（18、30、…、138） |
| 24 个外读格的极小值 13 | 解析交付阶梯日志 | PASS（clipped 0） |
| 供应常数 | 重跑交付程序 | PASS（(6,4,9,15,12) 与 (9,4,7,14,15)） |

## 3. Lean 复核

* 源码一致性：lean/ 下 16 个模块与工件包内同名文件 SHA-256 全部相同。
* 从源码重建（上游 TwoBlack 依赖为已编译的 .olean）：

    AntSharpWords 3.4 s；AntSharpInduction 3.8 s；AntSharpBase 1.5 s；
    AntSharp 49.4 s；AntGateWitness 4.9 s（4 核，0 error）

* 公理依赖（lean/check_axioms.lean 的实际输出）：

    AntSharp.ray_threshold_exact: propext, Classical.choice, Quot.sound,
      AntSharp.rays_checked 的 native_decide 公理, TwoBlack.level1_checks 的
      native_decide 公理
    AntSharp.threshold_table: propext, Quot.sound, 本定理 native_decide 公理
    AntGate.ordered14: propext, Classical.choice, Quot.sound, 3 条 native_decide 公理
    AntPlane.one_black_exact: propext, Classical.choice, Quot.sound, 其中含
      AntInverse.one58、AntInverse.representatives_checked、TwoBlack.level1_checks
      与 8 条 AntPlane native_decide 公理

* 关键陈述（Lean 原文）：

    AntPlane.one_black_exact :
      (exists z t p, matchAt [z] t p 58) /\
      forall (z : Pt) (t : Nat) (p : Fin 104), not (matchAt [z] t p 59)

    AntSharp.ray_threshold_exact (p : Fam1 x Hint1) (hp : p in level1Families)
      (k d : Nat) (hd : 0 < d) :
      (forall n, n <= width p + 104 + 104*k -> forall w,
          occurs (trace (X p (k+d))) w n <-> occurs (trace (X p k)) w n) /\
      (exists w, occurs (trace (X p k)) w (width p + 104 + 104*k + 1) /\
          not (occurs (trace (X p (k+d))) w (width p + 104 + 104*k + 1)))

* 源码中没有 sorry 或 axiom 声明；所有 key 定理的有限判定都落在
  native_decide 的编译执行上（与上游工程同一信任类别）。

## 4. 定稿时对稿件做的非数学修改

1. 86 步见证的时间表述：原稿“在时刻 7,897 达到 86”改为“从时刻 7,897 起
   匹配 86 步（到 7,983）”，与 78 步那条“匹配终于时刻 1,894”的写法统一。
2. 增加文件与命名空间的对照：AntGlobal.lean → AntPlane，
   AntGateWitness.lean → AntGate，AntFinite.lean → AntInverse，
   AntSharp*.lean → AntSharp。
3. 在两格 87 的外部枚举处注明计数以 data/ant3_reverse_findings.txt 的枚举
   口径为准，本记录未重跑该完整外部枚举。
4. 增加一句 DeepSeek Harness 独立复核的说明（指向本报告）。

## 5. 边界

* 两格 87 的全局上界来自上游两格覆盖加外部穷举，本仓库没有把它 Lean 化。
* 三格的两个必要条件是对全平面初态的 C++ 穷举得到的必要条件，不是三格
  全局上界，也没有给出完整周期的排除。
* 12K+2 家族的单例已 Lean 化，通用构造是纸面归纳加有限核验。
* native_decide 的有限布尔判定按编译执行可信，属于本工程声明的信任边界。
* 本复核没有重写 horizon/contact/replay 的枚举逻辑；只重编译、复跑并对照
  日志与抽样。
