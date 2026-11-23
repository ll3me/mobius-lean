# 已有工作与文献归属

核查日期为 2026 年 11 月 23 日。下文给出各步骤的原文位置，并注明仓库中相应定理的模型与核验范围。

## 逐板同时最优与图三着色

- **已有工作 · 单表四角条件。** Lenzhen、Morier-Genoud、Ovsienko 命题 3.5（式 3.4）给出单一符号函数的四角奇偶判据，文中将该判据追溯至 Yuzvinsky（1981）。Yagunov 命题 8 的证明在 16 阶棋盘型拉丁方上用同类方程导出矛盾。上述两个判据的符号均来自一张表。仓库的几何判定允许两张独立的全局表，各读取一对对角格。[Yuzvinsky，1981](https://doi.org/10.1307/mmj/1029002504) · [Lenzhen 等，命题 3.5，期刊第 2906 页](https://ovsienko.perso.math.cnrs.fr/Publis/Jpaa.pdf#page=4) · [Yagunov，命题 8，预印本第 7–8 页](https://pure.mpg.de/rest/items/item_3120352/component/file_3274665/content#page=7)
- **已有工作 · 布尔异或桥。** Tyson Williams 在 §4.3 图 4.1 给三角形的每个顶点施加恰一真约束，得到计数签名 $[0,1,0,1]$。按三个外部位的汉明重量排列，重量 1、3 的每份输入各有唯一内部匹配。把三条外边和三条内边全部取反，三个顶点便各要求恰二，外部关系变为 $c=a\oplus b$。仓库将对应的可延拓条件标为**重复实验（Lean 形式化复现）**。`ThreeFaceColoring.xor_bridge` 证明内部赋值存在当且仅当 $c=a\oplus b$。随后用三个实际四维子空间放置这个构件。[Williams，2015，印刷第 43 页，图 4.1](https://pages.cs.wisc.edu/~tdw/files/papers/Advances%20in%20the%20Computational%20Complexity%20of%20Holant%20Problems%20-%20Tyson%20Williams.pdf#page=50) · [布尔关系与几何坐标](../Mobius/ThreeFaceColoring.lean)
- **已有工作 · 法诺七线与删线。** Porschen、Schmidt、Speckenmeyer、Wotzlaw 在定理 5 的证明中使用有限射影平面的点线作恰一真约束。取二阶时，七条线一起无解。任删一线后有解，且该线上的三个点在每个解中都被迫为真（本项目以 $s=0$ 表示选中）。仓库在二阶情形核验七线的组合矛盾，并据此证明共用表项迫使七块板采用同一芯内坏方向。`delete_any_finite` 为任意删去的一块给出一对真实有限坐标表，使所有剩余板同时最优。[Porschen 等，定理 5 的证明，作者稿第 13 页](https://kups.ub.uni-koeln.de/55020/1/zaik632.pdf#page=13) · [七板的共同方向](../Mobius/ThreeFaceBoards.lean) · [删任一板的全局见证](../Mobius/ThreeFaceDeletion.lean)
- **已有工作 · 三态顶点与异色边。** Arends、Ouaknine、Wampler 定理 2 用三种允许着色的三角形代替每个顶点，用异色构件代替每条边。他们的目标是判断无四环、可四色的抽象图能否 101-着色，几何可嵌入性另在 §3 讨论。本项目以二元子空间的坐标为输入，`ThreeFaceRealization.finite_graph_iff` 核验三着色与同一对全局表上逐板最优的双向等价。[Arends 等，定理 2，第 5–6 页](https://people.mpi-sws.org/~joel/publications/ks11.pdf#page=5) · [有限坐标定理](../Mobius/ThreeFaceRealization.lean)

## 四比特的 1/15、刚性与 282

- Lenzhen、Morier-Genoud 与 Ovsienko 在命题 3.5 给出单表四角方程。命题 4.4 的式 (4.2) 及随后给出的周期四公式表明，他们那张显式表只在方向的汉明重量为 4 的倍数时失败。四比特非零方向中仅 1111 失败，故该表早已达到 1/15。Yagunov 命题 8 的矛盾证明展开为每个方向各一次的十五个方形。平移计数给出下界；把三个方形换到相邻起点也给出双表下界。上述计数把原文的单表构造和矛盾证书接到仓库的计分方式。[Lenzhen 等，命题 3.5、4.4](https://arxiv.org/pdf/1007.2337#page=6) · [Yagunov，命题 8](https://doi.org/10.1016/j.exmath.2014.12.002)
- 令两表初始相同，翻转其中一表的一个格。它涉及 15 个有向几何方形，原先恰有一个失败。新增 13 个几何失败，带起点计数因而由 256 增至 282。仓库证明**任意独立双表都跳过 256 与 282 之间的所有值；任意最优双表的所有缺陷都集中在唯一方向，而且非零残差的符号可分解到各条腿上。** 一张旧表提供一种最优图样，对所有最优表的结论还有全称量词。[本工程的间隔证明](SecondWeight.md) · [最优解及残差分类](RigidityKernel.md)
- 编码论的等价表述有助于跨领域查重。对顶点带行、列标签的方形取二元关联矩阵，将对面起点识别后形成长度 1,920 的失败向量。在全一向量加上合法赋号产生的线性码这个陪集中，最小和次小两个**不同**重量为 128、141。Zaragoza Martínez 的引理 5.1.2–3 已在单表 intercalate 矩阵中写出关联方程和对偶奇偶矛盾。2026 年同领域的计算论文研究最少颜色数以及对称矩阵分类。双表陪集的次重量及其整数证书见[次重量证明](SecondWeight.md)。1997 年关于极小障碍的另一篇预印本仅核到书目。[Zaragoza Martínez，第 5.1 节](https://morfismos.cinvestav.mx/sites/default/files/Upload/vol02-n1-6.pdf) · [Castro Campos、González Yáñez、Zaragoza Martínez，2026](https://doi.org/10.1080/10586458.2026.2625152)
- 沿闭路把边符号相乘、以两张覆盖的交换表示翻面是经典图论。此处莫比乌斯直觉的作用是发现了一个与抵消机制有关的等号问题。残差在所有最优解上的完整分类，才将这个问题接回张量成本。[Gross 与 Tucker 的图覆盖构造](https://www.sciencedirect.com/science/article/pii/0012365X77901315)

## Breuer 的算子与 1521

上次将 Breuer 的算子称为“近亲”不够精确。令 F 为交换，P₀ 为归一化辛单态投影。Breuer 的式 (3)、(5)、(6) 合起来就是 I−NP₀−F。在本工程的行切与所选辛基上，NP₀=|vec J⟩⟨vec J|，故这是同一个 E。Breuer 也已写出三个谱值，N=8 时的重数 1、27、36 随即得到。Park 推论 2.10 的式 (7)–(8) 另给出了标准与辛共轭情形的三个投影。[Breuer，2006，式 (3)、(5)、(6)](https://arxiv.org/pdf/quant-ph/0605036#page=2) · [Park，2026，推论 2.10](https://arxiv.org/pdf/2602.09860#page=10)

张量幂按次数分组、按相消后的谱支撑计数也已有先例。Anthropic 的附录 H 与 Majdoddin 的八平方分析使用秩 8 与 56 的两种谱空间；Alman 等对转置的对称、反对称部分使用高低次分组。仓库将 Breuer 三项按 Q+zE+z²P 分组，给出显式整数因子，并证明其中心项的下界与 1521 的指数底数匹配。1521=39² 是在重数与分组指定后由计数产生的常数，适合作为已有算子的一项具体应用。上游附录 B 已有更强的一般参数。[Anthropic，附录 B、H](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/paper.pdf) · [Majdoddin，第 12 页](https://arxiv.org/pdf/2610.41622#page=12) · [Alman 等，引理 4](https://arxiv.org/pdf/2611.05082#page=19)

## 五比特与 Singh 的下界

- 五比特的 3/31 构造直接来自三比特相位的商拉回。对于方向齐次且签名次数至多三的情形，Reed–Muller 最小重量已给出匹配下界。本工程允许一张表在所述 404 维空间内任取、另一张完全任意，失败也至少为 3/31。一般五比特双表的最优值仍未知。404 描述证明的适用域。对于向量布尔函数，逐行线性单表还与自相关表的指定对角和有关，比较时必须保留求和方式。[Morier-Genoud 与 Ovsienko](https://arxiv.org/pdf/1304.0949) · [Delsarte、Goethals 与 MacWilliams](https://doi.org/10.1016/S0019-9958%2870%2990214-7) · [Canteaut 等](https://arxiv.org/abs/1908.07445) · [本工程的结构化情形](FiveRowAffine.md)
- 22 项下界应归属 Singh 的切片方法在本工程残差上的应用。对 256 情形使用其方形下界与本工程的残差等价，对具体 282、304 见证使用干净切片及其三切片论证。三者沿用同一个既有秩不等式。[Singh，三切片证明](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/paper/crossing-lower-bounds.tex#L530-L543) · [相应归约](Naslund.md)

本次检索以四角方程、两表的独立量词、两种计数归一化和两切割的成本为比对标准，包含 intercalate 可签性、极化拉丁方、关联码陪集重量、平方恒等式、辛对称纠缠见证和 ETH crossing 分组等术语。

## 稀疏选面、奇环与恰一真

布尔反相器的奇环需要一个缺陷、图上同色边的最小数等于边数减最大割、以及正文字 1-in-3 的 NP 完全性，都有经典解释。本次工作的具体内容是让这些关系在指定的 XOR 方形、真实共享的四角坐标以及两张全局符号表上同时成立，并保留每个表项被使用的次数和原始等权失败数。仓库给出这个几何族在表项出现次数至多二和至多三之间的复杂性分界，以及它的精确赋值代价。[几何归约](PortEmbedding.md) · [Schaefer 的源问题](https://doi.org/10.1145/800133.804350) · [Alimonti 与 Kann 的有界度最大割](https://www.sciencedirect.com/science/article/pii/S0304397598001583)

## 本轮算法模型的先例

**甲线 · 重复实验（Lean 形式化复现）。** 独立集由二元二次多面体的边坐标取零得到，单调算术电路取面的逐门剪枝保持大小。这两个先例分别给出这里的几何与电路步骤。本项目将它们接到四角表的全顶点一元价格和可复用 DAG。网格 MWIS 电路下界采用 Korhonen 的定理，方格上允许减法后的上界采用 Hertrich–Sering 的精确最大流电路。[Laurent、Poljak、Rendl，§4.2](https://pure.uvt.nl/ws/portalfiles/portal/1215879/Connections.pdf#page=11) · [Grochow、Mulmuley、Qiao，定理 16](https://arxiv.org/pdf/1605.02815#page=27) · [Korhonen，定理 1 与推论 3](https://arxiv.org/pdf/2102.06901#page=2) · [Hertrich、Sering，算法 2–3 与定理 2](https://arxiv.org/pdf/2102.06635#page=12)

**乙线 · 重复实验（Lean 形式化复现）。** Hennie 已对首尾相同、中间填充的语言用单带越界记录得到 $\Theta(N^{3/2})$。Viola 的习题明确提出从填充回文归约到 3-SAT。仓库证明了自己的一元变量编号 3-CNF 在真实双向单带机上的 $\Omega_M(N^{3/2})$ 下界，并对同一次接受运行计费。[Hennie，1965，页 572–574](https://www.eecs.tufts.edu/~aloupis/comp260/lectures/hennie-1965.pdf#page=20) · [Viola，2023，Problem 4.2](https://emanueleviola.wordpress.com/2023/02/09/mathematics-of-the-impossible-computational-complexity-chapter-4-reductions/)

以上归属按步骤和模型给出。两条线在本仓库中的核验范围分别见[电路复现记录](ReusableCircuits.md)与[单带机复现记录](NextStep.md)。
