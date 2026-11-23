# Mobius：四比特符号表障碍与计算复杂度的 Lean 4 实验

[English](README.md) | **中文**

> 我不是专业的数学工作者，但是AI证明了黎曼猜想使我既欣喜又害怕。正好我的订阅额度要用不完了，我就决定在计算复杂度这个领域抽卡试试。不幸的是我对这个领域几乎一窍不通，所以只能凭一些简单的直觉推进工作。至于做出来的东西有没有意义，这个我倒不是觉得很重要。

本项目的研究、代码实现与初始文档由 GPT 6.2-Astra 协助完成。

## 省流 / 实测情况

**没有做什么：** 本项目**没有**证明 $\mathrm{P} \ne \mathrm{NP}$，没有改善上游已有 ETH 构造的总体时间上界（仓库里算出的 1,521 只是特定三比特分组下的局部对照常数），也没有突破任何通用计算模型的时间下界。

**最后做出来了什么：**

1. **四比特独立双表的组合刚性、间隙与局部/全局冲突**：把经典的单表 $1/15$ 障碍推到任意两张独立符号表，证明 3,840 个条件中最少失败 256 次且所有失败集中在唯一方向，精确数出全部 $15\cdot 2^{62}$ 对最优解并分类其残差；给出次小失败数 **282**（排除 257–281），并造出共享表项下“局部最优必须给全局最优让步”的具体例子（$K_4$ 的 78 面上 2 对 3 的分离、双扇结构 $p\ge 14$ 时被迫牺牲中央板）。
2. **完整四维板 / 方形约束的 NP 完全归约与 3-SAT 边界接口**：用 15 方形矛盾证书造出“反相线”和“恰一真”门，把图三着色、正文字 1-in-3 SAT 和 Max-Cut 编进同一对全局符号表，证明“仅给四维板基向量、判定能否逐板同时最优”是 NP 完全的；并在普通 3-CNF 上证明固定双表边界求和“1 次必有真假碰撞、2 次恰好够恢复精确 `#SAT`”，7,680 项测试集的阈值判错数精确等于抵消失败数。
3. **一套零 `sorry`、可一键复现的 Lean 4 形式化库**：[Mobius/](Mobius/) 下共 114 个 Lean 4 模块（23,362 行），外加仅依赖 Python 标准库的组合检验脚本。[Audit.lean](Audit.lean) 对 5,974 个 `Mobius` 声明和 3,933 个上游 `Complexity` 声明做了传递公理审计：零 `sorry`、零自定义公理、零 `native_decide`，所有定理仅依赖 Lean 4 标准三公理（`propext`、`Classical.choice`、`Quot.sound`）。

**顺带做的对照与复现（不算新下界）：** 仓库还把几类文献里已有的受限计算模型下界（单带图灵机 $\Omega_M(N^{3/2})$、无减法 $\min,+$ 热带电路 $2^{\Omega(b)}$、nFBDD/DNNF、读 $r$ 次分支程序、两方通信）复现或搬运到了这套板输入编码上，并配了双带线性时间、带减法多项式最大流电路等反面对照——主要用来测这套障碍在加了哪些算法手段后会被绕开。

## 主要结果

下表按主题汇总主要结论，并明确区分 **Lean 4 形式化定理** 与 **书面推导 + Python 精确证书**。

| 方向 / 问题 | 主要结论 | 验证形式与对应文件 |
|---|---|---|
| 四比特双表最优失败率与刚性 | 3,840 个带起点非零方向测试（1,920 个无向方形）中，任意独立双表最少失败 256 次（$1/15$），所有失败集中于唯一方向；有序最优双表精确为 $15\cdot 2^{62}$ 对（单表 $15\cdot 2^{42}$）；归一化残差经逐腿重标与边界变号可还原为完整交叉 $W_{16}$。 | **Lean 4**：[DirectionLaws.lean](Mobius/DirectionLaws.lean)、[TwoPhases.lean](Mobius/TwoPhases.lean)、[RigidityEnumeration.lean](Mobius/RigidityEnumeration.lean)、[RigidityResidual.lean](Mobius/RigidityResidual.lean) · 详述见 [docs/RigidityKernel.md](docs/RigidityKernel.md) |
| 四比特次小失败数（282）与降秩阈值 | 带起点失败数的第二小值恰为 **282**（排除 257–281），这也是行、列两切残差秩同时降至 256 以下的最小代价（可达 $(255,254)$）；另给出双表改两格的 304 构造（秩 $(253,253)$）。固定一张可延拓为最优解的表时，两秩均至少降 $j$（$0\le j\le 16$）精确需 $256+26j$。 | **混合**：282 见证及其零行、固定单表计数间隙与单块非奇异为 **Lean 4**（[LockedGap.lean](Mobius/LockedGap.lean)、[LockedRank.lean](Mobius/LockedRank.lean)）；完整的 $256+26j$ 降秩曲线与**一般独立双表的 282 全局下界尚未全进 Lean**，目前为书面证明与 Python 整数证书（[docs/LockedRankCurve.md](docs/LockedRankCurve.md)、[docs/SecondWeight.md](docs/SecondWeight.md)、[experiments/second_weight.py](experiments/second_weight.py)） |
| 五比特双表与多块交叉分解 | 五比特 31,744 个条件下，任意双表最少失败数介于 2,342 与 3,072 之间；限第一张表在 404 维结构化空间（含全部次数 $\le 3$ 的布尔函数）、另一张任意时，最小值精确为 3,072（$3/31$）。使用 Breuer 算子对 $t$ 个三比特块作 $2t+1$ 分组，两切因子乘积底数精确为 1,521（局部对照，未改写普通 SAT 上界）；对最优及 282/304 残差应用 Singh 三切片不等式，混合切割至少需 22 个秩一项。 | **混合**：五比特逐切片四行仿射/显式族 3,072 界与达到例、Breuer 分组上下界及 Singh 残差切片条件为 **Lean 4**（[FiveRowAffine.lean](Mobius/FiveRowAffine.lean)、[RankTradeLower.lean](Mobius/RankTradeLower.lean)、[NaslundRestriction.lean](Mobius/NaslundRestriction.lean)）；404 维空间分类与五比特一般 2,342 下界为书面推导与脚本（[docs/FiveRowAffine.md](docs/FiveRowAffine.md)、[docs/FiveCollisions.md](docs/FiveCollisions.md)、[experiments/five_collisions.py](experiments/five_collisions.py)、[docs/RankTrade.md](docs/RankTrade.md)、[docs/Naslund.md](docs/Naslund.md)） |
| 3-SAT 翻面回路与带符号边界求和 | 紧凑二进制 3-CNF 与“奇翻转验证回路”存在性双向等价并在计时单带机上 NP 完全，每个满足赋值恰对应一条规范回路。固定双表对未知公式只读一次边界总和必有真假碰撞，两次固定测量恰好够恢复精确 `#SAT`；在 7,680 项测试清单上，阈值判错总数等于抵消失败数（最少 256 次），错题分布唯一暴露失败方向。 | **Lean 4**：[SATSeam.lean](Mobius/SATSeam.lean)、[TourCount.lean](Mobius/TourCount.lean)、[BoundaryDecision.lean](Mobius/BoundaryDecision.lean)、[BoundaryTwoSums.lean](Mobius/BoundaryTwoSums.lean)、[BoundaryBooleanRate.lean](Mobius/BoundaryBooleanRate.lean) · 详述见 [docs/BoundarySAT.md](docs/BoundarySAT.md) |
| 1-in-3 SAT、Max-Cut 与 $K_4$ 局部/整板冲突 | 任意有限简单图每边接一根 13 面反相线后，全局表上的最少失败数精确等于 $\lvert E\rvert-\operatorname{MaxCut}(G)$；正文字 1-in-3 编为 $417m$ 个互异等权方形（阈值 $m$）；表项最多读 2 次多项式可解，允许读 3 次即 NP 完全。在同一套 $16\times 16$ 表上嵌入 $K_4$ 的 78 面时，局部最少坏 2 个，但任何整板最优解（坏 256）在该 78 面上至少坏 3 个，两集合最小编辑距离为 2 格（翻转后整板坏 304）。 | **混合**：有限图 Max-Cut 等式、局部 1-in-3 与读次数分界代价、$K_4$ 78 面分离与最小编辑距离为 **Lean 4**（[PortGraph.lean](Mobius/PortGraph.lean)、[OneInThree.lean](Mobius/OneInThree.lean)、[FourBitPortCut.lean](Mobius/FourBitPortCut.lean)、[PortCutEdits.lean](Mobius/PortCutEdits.lean)）；一般规模 $417m$ 归约见书面推导与脚本（[docs/PortEmbedding.md](docs/PortEmbedding.md)、[experiments/one_in_three_geometry.py](experiments/one_in_three_geometry.py)） |
| 完整四维板同时最优与公共面牺牲 | 仅给各四维板的四个独立二元基向量，判定是否存在同一对全局表使每块板同时坏 128 个：共用同一二维芯时总可同时最优；附带 7 块法诺线板即可编码图三着色（$n+7m+7$ 块板），判定为 NP 完全。共享轴双扇结构（$p\ge 14$ 块叶板）中任何全局最优解都必须牺牲中央板（3,682 vs 3,684）；平行三维面成环能否同时最优取决于切向分量异或为零。 | **混合**：有限图三着色等价、7 板法诺约束、双扇让步阈值（$p\ge 14$）与平行面异或判据为 **Lean 4**（[ThreeFaceRealization.lean](Mobius/ThreeFaceRealization.lean)、[ThreeFaceBoards.lean](Mobius/ThreeFaceBoards.lean)、[DoubleFan.lean](Mobius/DoubleFan.lean)、[ParallelSignature.lean](Mobius/ParallelSignature.lean)）；NP 完全性推论与脚本检查见 [docs/FreeDirections.md](docs/FreeDirections.md)、[docs/SharedOptima.md](docs/SharedOptima.md)、[experiments/free_direction_coloring.py](experiments/free_direction_coloring.py) |
| 单带机时间下界与双带对照 | 在一元变量编号 3-CNF 布局上，任何正确判定 3-SAT 的确定性双向单带机在无穷多长度上至少需 $\Omega_M(N^{3/2})$ 步；同编码跨切口不相容正例的信息计数已达 $O(N^{3/2})$ 上限。同一批公式在“只读输入带 + 独立工作带”的双带机上可在 $O(N)$ 时间判定。 | **混合**：单带 $\Omega_M(N^{3/2})$ 真实时钟定理与稀疏证书切口上限为 **Lean 4**（[CrossingMachine.lean](Mobius/CrossingMachine.lean)、[WitnessPacking.lean](Mobius/WitnessPacking.lean)、[WitnessStream.lean](Mobius/WitnessStream.lean)）；双带线性时间构造与差分测试见 [docs/NextStep.md](docs/NextStep.md)、[experiments/crossing_controls.py](experiments/crossing_controls.py)、[experiments/recognized_gadgets.py](experiments/recognized_gadgets.py) |
| 热带电路下界与减法上界 | 在边长 $b$ 的方格与三角网格全顶点一元价格问题上，精确的 $\min,+$（及含非负整数常数乘法）可复用 DAG 至少需 $2^{\Omega(b)}$ 个门；同在方格上允许减法，即可通过最大流电路得到 $O(b^8)$ 多项式规模上界。 | **混合**：四角目标到 MWIS 窗口的有理数编译及含乘法归一化为 **Lean 4**（[TropicalPort.lean](Mobius/TropicalPort.lean)、[TropicalProduct.lean](Mobius/TropicalProduct.lean)、[UnaryCut.lean](Mobius/UnaryCut.lean)）；MWIS 平面下界与最大流带减法上界引用前人定理并附脚本检查（[docs/ReusableCircuits.md](docs/ReusableCircuits.md)、[experiments/tropical_controls.py](experiments/tropical_controls.py)） |
| 自由读序分支程序、DNNF 与两方通信 | 将扩展图顶点覆盖或 BRS 模 3 双线性函数投影到完整板输入串的单个物理位上，可把 nFBDD、DNNF（$2^{\Omega(n)}$）和句法读 $r$ 次分支程序指数下界搬到板列表上；宽接口两方合并与完整板非边查询分别需 $k^2$ 位（多轮交互）与 $\binom{k}{2}$ 位（单向记忆）。 | **混合**：位投影、给定 `Gap266` 假设下的阈值等价与 nFBDD/DNNF 限制、两方合并与非边查询记忆界为 **Lean 4**（[BoardProgramRestriction.lean](Mobius/BoardProgramRestriction.lean)、[MatrixPromise.lean](Mobius/MatrixPromise.lean)、[FullBoardMerge.lean](Mobius/FullBoardMerge.lean)、[ThreeFaceMemory.lean](Mobius/ThreeFaceMemory.lean)）；`Gap266`、BRS 蝶形编译、树张量网络切口与原文献下界见 [docs/BoardInputModels.md](docs/BoardInputModels.md)、[docs/ReadBoundedSource.md](docs/ReadBoundedSource.md)、[experiments/read_bounded_boards.py](experiments/read_bounded_boards.py) |

## 前人工作与文献归属

项目中的核心下界技巧、标准归约构件与上游基础形式化均来自已有文献，仓库主要完成这些结论在“四维板 / 双符号表 / 3-CNF 翻面”接口上的对接与 Lean 4 形式化：

- **四角方程与四比特 $1/15$**：单表四角奇偶判据及 $1/15$ 显式构造来自 Lenzhen、Morier-Genoud 与 Ovsienko；16 阶棋盘型拉丁方不可极化的 15 方形矛盾结构来自 Yagunov。本仓库将其改写为独立双表计分并给出最优解分类、残差等价及 282 次重量证明。
- **交叉分解、Breuer 算子与三切片下界**：ETH 次指数计数构造对照了 Anthropic 与 OpenAI 的 2026 年公开工作；三比特分组用的辛单态算子出自 Breuer（2006）；混合切割下的线性秩下界来自 Arth Singh 的三切片定理。
- **图三着色与 1-in-3 构件**：布尔异或桥取自 Tyson Williams，法诺七线恰一真障碍取自 Porschen 等，三态顶点与异色边三着色归约取自 Arends、Ouaknine 与 Wampler，正文字 1-in-3 与有界度 Max-Cut 分别取自 Schaefer 与 Alimonti–Kann。
- **受限模型与 Cook–Levin 基础**：单带机 crossing sequence 取自 Hennie（1965）及 Viola 的归约习题；热带电路下界与有符号最大流上界分别采用 Laurent–Poljak–Rendl、Grochow–Mulmuley–Qiao、Korhonen 与 Hertrich–Sering 的定理；nFBDD/DNNF 与读 $r$ 次下界取自 Amarilli 等、Bova 等及 Borodin–Razborov–Smolensky；计时单带图灵机与 Cook–Levin 形式化直接依赖 Robert D. Barish 的项目。

各步骤对应的原论文页码、命题编号与本仓库 Lean 定理的映射关系，集中在 [docs/Priority.md](docs/Priority.md)。

## 如何复现

环境要求：项目固定的 Lean 4 工具链 `v4.35.0-rc2`（见 [lean-toolchain](lean-toolchain)）、Python 3.10+、POSIX shell 与 `tar`。使用 `elan` 时会自动切换到对应 Lean 版本。在仓库根目录运行：

```sh
./scripts/check.sh
```

- **Apple Silicon Mac**：可先运行 `python3 scripts/bootstrap.py --local-lean`，脚本会把固定版本的 Lean 编译器下载并校验后安装到项目局部的 `.toolchain/` 目录中。
- **离线运行**：随仓已提供上游 Cook–Levin 源码归档，[bootstrap.py](scripts/bootstrap.py) 会在解包前校验 SHA-256。工具链安装完成后，主检查可全程离线执行。
- **检查流程说明**：[check.sh](scripts/check.sh) 依次执行 `bootstrap.py`、`lake build`、公理审计 `lake env lean Audit.lean`、输入拼接检查 `lake env lean experiments/EncodedCuts.lean`，以及 [experiments/](experiments/) 下的全部标准库 Python 检验脚本。
- **公理审计说明**：[Audit.lean](Audit.lean) 仅导入实现模块（见 [Mobius.lean](Mobius.lean)），只允许 Lean 标准三公理（`propext`、`Classical.choice`、`Quot.sound`）。如前所述，四比特一般独立双表的 **282 全局下界**及 `Gap266` 仍依赖书面证明与精确 Python 证书，尚未全部进入 Lean。

## 目录与来源

- [Mobius/](Mobius/) 与 [Mobius.lean](Mobius.lean)、[Audit.lean](Audit.lean)：全部 114 个 Lean 4 形式化模块、总入口与传递公理审计。
- [experiments/](experiments/)：包含 [EncodedCuts.lean](experiments/EncodedCuts.lean) 及只用 Python 标准库的可复算组合检验、整数证书与模拟器脚本。
- [docs/](docs/)：各子课题的详细推导与核查笔记，建议从以下几篇读起：
  - [docs/2026-11-23.md](docs/2026-11-23.md)：研究主线汇总与各分支之间的衔接关系。
  - [docs/Priority.md](docs/Priority.md)：前人文献归属、原文页码与各定理的验证状态。
  - [docs/ResearchNotes.md](docs/ResearchNotes.md)：从证明回路、受限模型到四比特障碍的完整研究笔记。
  - [docs/HourResults.md](docs/HourResults.md)：四比特 256/282、五比特与 1521 底数等定量结论摘要。
- [vendor/](vendor/)：随附 Robert D. Barish 的 Lean 4 Cook–Levin 与计时图灵机形式化源码归档 [npcomplete-3e603e79.tar.gz](vendor/npcomplete-3e603e79.tar.gz)，固定至上游提交 [`3e603e79`](https://github.com/RBarish-UTokyo/NPCompleteness-Lean4/tree/3e603e795b44fedcf7d6dd65b7d1e30547ead925)，保留上游 Apache-2.0 许可证。
- [LICENSE](LICENSE)：本项目采用 Apache-2.0 许可证。

## 直觉起源与探索方向

- **直觉起源**：项目最初来自一个朴素的类比——从“停机问题里的自指成环”联想到莫比乌斯环“沿圈走一圈回到原点时正反面互换”的结构，想尝试把 3-SAT 的证明思路也写成类似翻面回路的形式。随后在与 AI 一起往下推进时，为了把想法落到可以具体算清楚的代数对象上，引入了“十六平方问题”的符号障碍（即前文四比特双符号表与方形约束中绕不开的 $1/15$ 失败率）。
- **核心猜想与推进思路**：整体设想是把计算复杂度问题翻译成几何或组合对象自身的性质——先不直接去碰“任意一般算法”，而是检验这类共享表项的几何/组合结构里，是否存在一种躲不掉的**一般性内在代价**：
  - 一类是局部与全局之间的“粘贴/挫败差”。记同一对符号表 $T$ 下第 $i$ 块的代价为 $f_i(T)$，即对比“各块各自取局部最优之和”与“共用同一对全局表时的共同最优”之间的差值 $\min_T\sum_i f_i(T)-\sum_i\min_T f_i(T)$（例如四比特 $K_4$ 中 2 与 3 的分离、共享轴双扇中 $p\ge 14$ 时中央板被迫让步）；
  - 另一类是跨块预知冲突时必须保留的信息代价（例如平行三维面成环所需检验的异或位数，以及宽接口合并、非边查询等场景下不得不传递的通信或记忆位数）。
- **对具体算法手段的逐项检验**：一旦找到候选的内在代价，就接着测试缓存、中间结果复用、线性异或消元、允许减法或增加工作带等具体计算手段，看它们能不能消去或绕开这些代价（例如允许减法就可以绕开网格上的 $\min,+$ 电路下界，增加一条独立工作带就可以绕开单带机时间下界）。至于这种代价能否进一步覆盖更强的计算模型，目前仍处于试探性的探索阶段，没有现成结论。
