# 3-SAT 证明中的翻面

**模型：GPT 6.2-Astra**（本项目的研究、实现与整理）

绕一圈回到同一位置，符号却换了面。如果把这种现象放进 3-SAT 的证明，什么条件会迫使它出现？这个 Lean 4 工程沿两条线研究这个问题：一条跟踪普通 3-SAT 验证中的回路，另一条研究精确计数算法为了让错误项相消，必须怎样给四角方形选符号。

目前最清楚的必要性来自后者。四比特模型允许两张独立的符号表任意取值。**只要失败数达到最小值，所有失败就必定集中在唯一方向。** 这里起作用的假设是局部抵消达到了最优。一般 SAT 判定器只须在时限内正确回答，它是否需要产生相应的结构，仍是开放问题。[定理与验证范围](docs/RigidityKernel.md) · [固定翻转图上的 3-SAT 定向命题](docs/FixedGraphConjecture.md)

## 成果

| 问题 | 结论 | 验证与依据 |
|---|---|---|
| 普通 3-SAT 能否写成翻面回路问题 | 给定紧凑编码的公式，存在奇翻转回路当且仅当公式可满足。该语言在计时单带机模型中 NP 完全。每个满足赋值恰贡献一条从一个端口到另一端口的规范回路。 | [Lean：判定](Mobius/SATSeam.lean) · [Lean：计数](Mobius/TourCount.lean) |
| 四比特最优双表会留下什么 | 3,840 个带起点条件中最少失败 256 个，即 1/15。每对最优表只在唯一一个方向上失败。对每个最优解，归一化残差都能通过分别重标张量各腿、改变边界符号，还原为完整交叉。 | [Lean 定理、最优解计数与残差等价](docs/RigidityKernel.md) |
| 什么时候能让两种切割的残差秩都下降 | 失败数的第二小值恰为 **282**。最优解的两个残差矩阵都具有秩 256。翻转行表一个格子，可以在 282 次失败时达到秩 (255,254)。 | [全局排除的书面证明与精确计算证书](docs/SecondWeight.md) · [Lean：达到 282 的见证](Mobius/LockedGap.lean) |
| 五比特与多块交叉 | 五比特任意双表的最少失败数在 2,342 与 3,072 之间，总计 31,744 个条件。一张表取特定结构、另一张任意时，最少恰为 3,072。另一个精确交叉构造使用 Breuer 的算子，在指定三比特分组中得到秩乘积的渐近底数 1,521。 | [五比特一般界](docs/FiveCollisions.md) · [结构化表](docs/FiveRowAffine.md) · [分组的上下界与上游比较](docs/RankTrade.md) |

1/15 可以从已有平方恒等式和极化拉丁方证明推出。四比特双表中间重量的排除，以及对**全部**最优解的分类，是本项目独立得到、在已核文献中尚未找到完整先例的两个结论。Singh 的三切片下界可用于这里的残差，在允许混用两种切割时，具体的 256、282 和 304 构造仍至少需要 22 个秩一项。[文献优先权核查](docs/Priority.md) · [Singh 定理如何适用](docs/Naslund.md)

## 复现

需要项目固定的 Lean 4 工具链 `v4.35.0-rc2`、Python 3.10 或以上、POSIX shell 和 tar。使用 elan 时，项目目录下的 `lean-toolchain` 会选择对应版本。运行：

```sh
./scripts/check.sh
```

在 Apple Silicon Mac 上，也可以先用 `python3 scripts/bootstrap.py --local-lean` 将固定版本的编译器下载到项目内。Cook–Levin 源码归档随仓库提供，启动脚本先校验 SHA-256 再解包。已装好工具链时，主检查可离线运行。[启动脚本及固定版本](scripts/bootstrap.py)

`check.sh` 构建全部 Lean 模块，审计 `Mobius` 和所导入 `Complexity` 声明的传递公理，再运行标准库 Python 实验。公理审计允许 `propext`、`Classical.choice`、`Quot.sound`。一般双表的 **282 全局下界**由书面论证和精确有限计算共同支持，它的完整证明尚未全部移入 Lean。上游 ETH 算法和 Singh 的 Mathlib 工程有各自的验证入口。[主检查](scripts/check.sh) · [Lean 模块入口](Mobius.lean) · [公理审计](Audit.lean)

## 下一步

**从真实机器的运行中提取一个可计费的接口。** 已有 Lean 构件将两个串编码成一个普通 3-CNF，公式可满足恰当两个串相等。下一项拟验证的引理是：若同一台确定性单带机在两个正例上穿越同一带格边界时留下相同的状态序列，就能拼出对混合输入的接受运行。这样，区分输入所需的信息量便能和机器实际花费的步数挂钩。验收目标与这个模型的边界见[研究计划](docs/NextStep.md)。

## 文件与来源

- [完整研究记录](docs/ResearchNotes.md) 保留了从证明回路、受限模型到 ETH 构造的原始推导。[结果摘要](docs/HourResults.md) 汇总了定量结论。
- [Lean 模块](Mobius/) 与[有限实验](experiments/) 分别提供内核定理和可重验的计算证书。
- 计时图灵机和 Cook–Levin 基础取自 Robert D. Barish 的项目，固定到提交 `3e603e79`。随附归档保留上游 Apache-2.0 许可证。[上游固定源码](https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925)
