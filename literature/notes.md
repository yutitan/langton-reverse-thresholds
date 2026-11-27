# 文献笔记与依赖

本记录不声称重新发现或优先任何结构；以下两个来源是本记录直接依赖的对象。
这里只是使用记录，不是完整的文献调研。

## Hao Ke：单黑格定理

* Hao Ke, *Every One-Black-Cell Langton Ant Reaches the Period-104 Highway*,
  <https://www.kehao.me/papers/langtons-ant-one-black/>。
* 本记录使用其中给出的 22 条通道（单黑格首次接触后的归约）。
* 本记录的新增结论（倒放因子、精确阈值、58 的全平面定理、14 格见证等）
  不重新证明该定理。

## imfinn：两黑格工程

* imfinn, *Every Langton's ant start with at most two black cells reaches a
  translating period-104 highway*（修订稿 5，2026-10-05），
  <https://github.com/imfinn/langton-two-black>。
* 固定提交：95e896e3035e992e48ce9d28a5ded8568c86e835。
* 本记录使用该工程的 TwoBlack.Level1Data（22 条射线的基点、切点）、
  level1_checks（有限通道检查）与 TwoBlack.Parent0（蚂蚁模拟与证书）。
* 两格 87 的全局上界依赖该工程的首次接触覆盖加外部穷举（见
  data/ant3_reverse_findings.txt）；这部分没有在本记录中形式化为 Lean 定理。

## 没有做的事

* 没有对“倒放阈值”做独立文献检索，也不主张这是新问题。
* 上游论文与 Ke 定理的引用按题述与工程源码转述，未重新审阅其证明。
