# Lean 4.30 形式化（新增模块）

本目录只包含本记录新增或改动的 Ant*.lean 模块；底层依赖来自
imfinn/langton-two-black 的固定提交 95e896e3035e992e48ce9d28a5ded8568c86e835。

## 模块与命名空间

| 文件 | 命名空间 | 内容 |
| --- | --- | --- |
| AntInverse.lean | AntInverse | 倒放词的模拟、重放与上界通用引理；witness 定理（zero32、one58、two87、three88、eleven101、twelve110、twenty208、sharp23、immediate23） |
| AntFinite.lean | AntInverse | 单格 2,388 个代表位置的有限证书（finite_one_upper） |
| AntCoverage.lean | AntPlane | 空白轨迹首次接触覆盖：2,388 + 44 位置 + 22 射线 |
| AntPrepared.lean | AntPlane | 上游有限通道检查的相邻深度耦合 |
| AntSplice.lean | AntPlane | 一处或两处切点复制 104 块的整条轨迹恒等式 |
| AntRays.lean | AntPlane | 22 条射线的因子归约 |
| AntGlobal.lean | AntPlane | 单格 58 全平面定理 one_black_exact |
| AntMarkers.lean | AntPlane | 标记恒等式与 witness_forces_gap |
| AntGapData.lean | AntPlane | 22 行间距表 gap_table_checked |
| AntLong.lean | AntPlane | 保守稳定界（无预设词长） |
| AntLost.lean | AntPlane | 4,979 步具体见证 lost_4979 |
| AntSharpWords.lean | AntSharp | Zone 语言引理、标记像与 gap 像 |
| AntSharpInduction.lean | AntSharp | Plan、逐深度归纳与 exact_of_plan |
| AntSharpBase.lean | AntSharp | wholeB 检查、22 行数据接通 |
| AntSharp.lean | AntSharp | ray_threshold_exact：22 条射线、任意深度对的精确阈值 |
| AntGateWitness.lean | AntGate | ordered14：14 格有序见证（2453 步正向 + 119 步倒放） |

## 构建

把本目录的 .lean 文件复制到上游工程 lean/ 根目录，然后在该目录运行：

    lake build TwoBlack.Level1 TwoBlack.Parent0
    for mod in AntInverse AntFinite AntCoverage AntPrepared AntSplice AntRays \
      AntGlobal AntMarkers AntGapData AntLong AntLost \
      AntSharpWords AntSharpInduction AntSharpBase AntSharp AntGateWitness; do
      lake env lean -o .lake/build/lib/lean/$mod.olean $mod.lean || exit 1
    done
    lake env lean check_axioms.lean

注意：AntFinite 的有限证书较大（约 14 分钟）；AntSharpWords 约 3 秒、
AntSharpInduction 约 4 秒、AntSharpBase 约 2 秒、AntSharp 约 50 秒、
AntGateWitness 约 5 秒（在一台 4 核机器上实测）。上游源码与 .lake 不在本
仓库内；也可以直接用 release 资产里的验证包（https://github.com/yutitan/langton-reverse-thresholds/releases/tag/v1.0.0），其中包含全部 Ant*.lean 与数据。

## 公理与信任边界

* 源码中没有 sorry 或 axiom 声明；关键定理的公理依赖只有 propext、
  Classical.choice、Quot.sound 与 native_decide 生成的归约公理。
* native_decide 的有限布尔判定由编译执行完成，属于本工程的信任边界；
  二格 87 的整套外部枚举没有 Lean 化（见 README 与 PROVENANCE.md）。
* 公理打印样例见 check_axioms.lean 以及 data/ant_gate_sharp_axioms.txt、
  data/ant_gate_ordered_axioms.txt。
