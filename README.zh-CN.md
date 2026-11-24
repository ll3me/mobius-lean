# Mobius：四比特符号表障碍与计算复杂度的 Lean 4 实验

[English](README.md) | **中文** · [固定余量猜想](#fixed-margin-conjecture) · [配对收缩阶段小结](#pair-contraction-summary) · [弱猜想](#weak-pair-contraction-conjecture) · [强猜想](#strong-pair-contraction-conjecture)

> 我不是专业的数学工作者，但是AI证明了黎曼猜想使我既欣喜又害怕。正好我的订阅额度要用不完了，我就决定在计算复杂度这个领域抽卡试试。不幸的是我对这个领域几乎一窍不通，所以只能凭一些简单的直觉推进工作。至于做出来的东西有没有意义，这个我倒不是觉得很重要。

本项目的研究、代码实现与初始文档由 GPT 6.2-Astra 协助完成。本仓库截止目前（2026/11/24）花费约1.03B token。

<a id="fixed-margin-conjecture"></a>

## 整张布尔电路的 $1/4-\sigma$ 配对收缩猜想（开放）

是否存在一个**与规模无关**的常数 $0<\sigma<1/4$，使每个充分大的 $m$ 都有一份判定 $2m$ 点有向哈密顿回路的精确最优 AND/OR/NOT 电路，以及一份保留完整 $m$ 点问题的配对，使写定的化简器 $R_+$ 输出至多 $(1/4-\sigma)$ 倍的原门数？电路允许任意共享，配对后对每张 $m$ 点小图都须判对。[量词与化简规则](docs/PairContraction.md#boolean-contraction-operator)

若成立，按 $N=n(n-1)$ 个原始弧位计，最少门数将达到 $\Omega(N^{1+\delta})$，其中 $\delta=\tfrac12\log_2(1/(1-4\sigma))>0$。已证的单出口奇偶区域重建有随规模变小的余量 $\sigma_m=1/(8m-4)$，计的是这些区域合计的门数。整图固定余量界是弱猜想 $1/4$ 和强猜想「比例趋零」之间的目标。[倍增推导](docs/MultiplicativeGap.md#fixed-quarter-margin) · [局部定理与覆盖率](docs/SignedCircuitSweeps.md)

## 省流 / 实测情况

**没有做什么：** 本项目**没有**证明 $\mathrm{P} \ne \mathrm{NP}$，没有改善上游已有 ETH 构造的总体时间上界（仓库里算出的 1,521 只是特定三比特分组下的局部对照常数），也没有突破任何通用计算模型的时间下界。

**最后做出来了什么：**

1. **四比特独立双表的组合刚性、间隙与局部/全局冲突**：把经典的单表 $1/15$ 障碍推到任意两张独立符号表，证明 3,840 个条件中最少失败 256 次且所有失败集中在唯一方向，精确数出全部 $15\cdot 2^{62}$ 对最优解并分类其残差；给出次小失败数 **282**（排除 257–281），并造出共享表项下“局部最优必须给全局最优让步”的具体例子（$K_4$ 的 78 面上 2 对 3 的分离、双扇结构 $p\ge 14$ 时被迫牺牲中央板）。
2. **完整四维板 / 方形约束的 NP 完全归约与 3-SAT 边界接口**：用 15 方形矛盾证书造出“反相线”和“恰一真”门，把图三着色、正文字 1-in-3 SAT 和 Max-Cut 编进同一对全局符号表，证明“仅给四维板基向量、判定能否逐板同时最优”是 NP 完全的；并在普通 3-CNF 上证明固定双表边界求和“1 次必有真假碰撞、2 次恰好够恢复精确 `#SAT`”，7,680 项测试集的阈值判错数精确等于抵消失败数。
3. **可复现的 Lean 4 证明与 Python 核验。** `Mobius/` 下共 122 个模块，24,633 行，配有使用 Python 标准库的核验脚本。传递公理审计覆盖 6,383 个项目声明和 3,933 个上游 `Complexity` 声明，其证明只依赖 Lean 的标准公理 `propext`、`Classical.choice`、`Quot.sound`。项目模块中 `sorry` 和 `native_decide` 的使用次数均为零。[模块](Mobius/) · [公理审计](Audit.lean)

**顺带做的对照与复现（不算新下界）：** 仓库还把几类文献里已有的受限计算模型下界（单带图灵机 $\Omega_M(N^{3/2})$、无减法 $\min,+$ 热带电路 $2^{\Omega(b)}$、nFBDD/DNNF、读 $r$ 次分支程序、两方通信）复现或搬运到了这套板输入编码上，并配了双带线性时间、带减法多项式最大流电路等反面对照——主要用来测这套障碍在加了哪些算法手段后会被绕开。

**至少有几张完整板必须偏离最优？** 从有 $v$ 个顶点、$e$ 条边的简单图构造 $B=8v+57e$ 张无权板。让同一对全局表作用于所有板，最少坏板数恰为使原图可三着色所需的最少删点数。由 OpenAI 第 106 族，区分零张坏板和超过 $v/2$ 张坏板是 NP 困难的，负例的损失至少为 $\sqrt{B/114}$ 张。一般等式有书面证明。逐格计分给出了 $K_4$ 坏 1 张、$K_5$ 坏 2 张的全局表，SAT 检查排除了更小的坏板数。[证明与出处](docs/FaceMultiplicity.md#color-deletion) · [复算脚本](experiments/color_deletion.py)

## 哈密顿回路判定的配对收缩（截至 2026-11-25）

记 $H_n$ 为 $n$ 点无自环有向图的哈密顿回路判定。在板网编码中，每条弧的开关占一个原始坐标位。同一对全局表能让所有板同时最优，当且仅当 $H_n=1$。取 $n=2m$，把顶点分成有向点对 $\rho=((a_i,b_i))_{i=1}^m$。固定开放每条 $a_i\to b_i$，让 $i\ne j$ 的 $b_i\to a_j$ 自由开关，其余弧全部关闭。全圈必须连续走完每一对，缩点后恰好保留所有小图上的 $H_m$。[板网编码](docs/HamiltonianBoards.md) · [配对构造](docs/PairContraction.md)

单调电路使用二输入 AND、OR。这里的一般布尔电路还允许一输入 NOT。每扇门计一次，扇出不限，输入、常量和连线免费。代入配对后，$R_0$ 传播常量，把操作数相同的 AND/OR 门和双重取反接回原线，按运算和操作数合并相同门（允许交换两个输入），最后删除无法通往输出的门。[化简规则](docs/PairContraction.md#1-计数和化简算子)

<a name="pair-contraction-summary"></a>

### 配对收缩阶段小结

对 $m\ge3$ 和每份计算 $H_{2m}$ 的精确最优 AND/OR/NOT 电路，都存在一份配对，使 $R_0$ **至少删去 $3m^2+m-2$ 扇门**，同时在全部小图输入上保留 $H_m$。每份配对固定 $3m^2-m$ 个弧位，最优性保证至少 $2m-2$ 个不同弧位有额外引用。能把这些引用一起计入删门数，是因为任意预先指定的 $2m+1$ 个弧位都可由一份配对同时固定。合计只读这些弧位的共享门也会一起化为常量。这个数是紧的，存在 $2m+2$ 个弧位，每种配对都留其中至少一位自由。一般规模的结论有书面证明，Lean 已核验出线计数和重放等价。[共同配对与删门证明](docs/JointNegativeContraction.md) · [Lean 出线计数](Mobius/PairContraction.lean#L312) · [Lean 重放引理](Mobius/PairContraction.lean#L406)

八点实验用同一份预定配对追踪 392 扇共享门。每扇门都能区分两张强连通、有环覆盖、却无全圈的图。第二种实现先让每个弧位经过一段在所有输入上都返回原位值的电路，再接入相同的计算。

| 八点电路 | 原门数 | 392 扇中化为常量 | 剩余总门数 | 四分之一准许剩余 |
| --- | ---: | ---: | ---: | ---: |
| Held–Karp 的德摩根对偶 | 2,317 | 374 | 33 | 579 |
| 接入恒等输入代理的同一电路 | 2,483 | 0 | 2,400 | 620 |

遍历全部 1,680 种配对，第一种实现每次都剩 33 门，第二种最少剩 2,400 门。同一门基里的原始 Held–Karp 实现只需 2,260 门，因此表中两份电路都严格大于最小规模。[逐门记录](docs/JointNegativeContraction.md#八点实例的同一份配对) · [Held–Karp 门数公式](docs/PairContraction.md#2-最优单调电路的逐级检验) · [Python 复核](experiments/negative_gate_loss.py)

**一般电路的 $1/4$ 规模界仍开放。** 设 $s$ 为 $H_{2m}$ 的最小门数，$E=s-4m^2$。从 $R_0$ 的已证界出发，再省 $\max(0,\lceil3E/4\rceil-m+2)$ 扇门就足以达到 $\lfloor s/4\rfloor$。修订后的猜想也计入同一配对下合并信号所节省的门数。$s$ 的实际大小未知。[缺口推导](docs/JointNegativeContraction.md#四分之一还差多少) · [共享门与消费者的计数](docs/JointNegativeContraction.md#一份配对同时向源门和消费者收取多少代价) · [修订后的猜想](#weak-pair-contraction-conjecture)

对 $d$ 个不同原弧位的固定合取，即使弧共用头或尾，均匀配对后合取未化零的概率也至多为 $C(d+1)^{1/4}4^{-\sqrt d}$。这能在同一份配对下对一批预先指定的合取输出计数。[证明、紧例与穷举](docs/PairContraction.md#general-arc-support)

八点哈密顿闭合游走容斥电路固定一份配对后，$R_+$ 留下 3,726 门。只从连线识别等价信号的额外候选分别留下 2,701 门（每线八个单项式）和 2,606 门（每线八个决策结点），在全部 4,096 个小图上判定正确。该源电路已知大于最优规模。[实验与逐门计费](docs/SignedCircuitSweeps.md)

**已证的局部界。** 对一批内部门互不重叠、只读原弧、仅出口可供外部使用的最优奇偶区域，同一配对下按正负相位重建，合计成本至多是这些区域原门数的 $p_m=(m-1)/(4m-2)=1/4-1/(8m-4)$ 倍。八点缩四点时 $p_4=3/14$。单靠这条估计，要把整张八点电路压到四分之一，区域须覆盖至少 $21/22$ 的原门。上述容斥源电路的实测覆盖率为零。[条件与证明](docs/SignedCircuitSweeps.md)

### 已证的语义 read-1 电路收缩定理

在只开一条全圈的输入上，一份接受证明在 OR 门选一个为真的操作数，在 AND 门取两个操作数。证明每次引用一扇共享门，都将它展开一次。语义 read-1 要求每条全圈至少有一份证明，恰好用一次圈上的每条弧。对每个充分大的偶数 $n$ 和**这个类中每一份门数最少的电路 $C$**，在所有有向配对上均匀取平均，有

$$
\frac{\mathbb E_\rho\!\left[\lvert R_0(C\vert_\rho)\rvert\right]}{\lvert C\rvert}
\le \exp\!\left[-\Omega\!\left(\frac{\log n}{\log\log n}\right)\right].
$$

分子是这份原电路实际剩下的门数的平均值。每扇门的各个单项式使用固定的弧尾集合和弧头集合。配对一旦让两者不相容，该门就变为零。靠近输出时，证明按各门的单项式还能怎样补成全圈来分组。若从这些门往上有太多延伸门或额外引用，重组就会得到一份更小的电路，与最优性矛盾。渐近定理已有书面证明。Lean 核验了配对必要条件、补项重组等式和出线计数。Python 枚举了四、六、八点的全部配对。四点的一份最优电路有 20 扇门，12 份配对各自都只留一扇。[书面证明](docs/ReadOneContraction.md) · [Lean 引理](Mobius/PairContraction.lean) · [枚举程序](experiments/read_one_contraction.py)

枚举脚本使用至多五份预定配对。进一步的书面推论将清单缩到四份，保证其中一份删去至少 $(1/28-o(1))\lvert C\rvert$ 扇门。对偶数 $n\ge 6$，模 $n$ 步长为 $+1,+2$ 的无向边构成连通的四正则 Cayley 图。由 Bermond、Favaron 和 Mahéo 的定理，它可以分为两条哈密顿圈。两条偶圈各自交替取边，恢复每条弧原来的朝向，共得四份配对，再用内部门引用计数即可。[四正则图分解原文](https://www.sciencedirect.com/science/article/pii/0095895689900403) · [内部门引用计数](docs/InternalSharing.md)

Sengupta 和 Venkateswaran 在 1994 年研究二分完美匹配时已用过“每个极小正例至少有一份无重复证明”这一条件。结合 Jukna 的 read-1 刻画、Jerrum–Snir 下界和 Held–Karp 上界，已有结果即给出哈密顿回路判定在本模型中的最小门数 $\Theta(n^2 2^n)$。本项目进一步计量指定的局部化简会从每份最优电路实际删去多少门。[Sengupta–Venkateswaran 定理 5.3](https://repository.gatech.edu/server/api/core/bitstreams/908c7751-3664-4150-ae9d-737d3383470f/content) · [Jukna 定理 1、2](https://arxiv.org/html/2207.08701v3) · [Jerrum–Snir §4.4](https://snir.cs.illinois.edu/listed/J7.pdf#page=16) · [Held–Karp](https://doi.org/10.1137/0110015)

<a name="pair-contraction-conjecture"></a>

### 配对收缩猜想（均开放）

一般布尔猜想采用 $R_+$（2026-11-25 修订）。对同一份已代入配对的电路 $D=C\vert_\rho$，从三个结果中取门数最少者。第一项是 $R_0(D)$。第二项再化简至多三门的窗口。第三项在第二项上识别固定的 XOR、XNOR 模式，并在 $\mathbb F_2$ 上化简仿射表达式。三个结果都按 AND/OR/NOT 门计价，重建 XOR 所用的门也计入总数。记 $S(n)$ 为 $H_n$ 在此门基上的最小规模。每个候选在全部小图输入上都计算 $H_m$，故 $S(m)\le\lvert R_+(D)\rvert\le\lvert R_0(D)\rvert$。[算子定义与例子](docs/PairContraction.md#boolean-contraction-operator)

<a name="weak-pair-contraction-conjecture"></a>

#### 弱配对收缩猜想（固定存活比例）

**一般布尔版。** 在计算 $H_{2m}$ 的**精确最优电路** $C$ 和有向配对 $\rho$ 中，取 $\lvert R_+(C\vert_\rho)\rvert/S(2m)$ 的最小值，记为 $r_+(m)$。弱猜想要求所有充分大的 $m$ 有 $r_+(m)\le1/4$。每个规模只须找到一份电路和一份配对。若成立，就有 $S(2m)\ge4S(m)$，与 $S(n)=\Theta(n^2)$ 相容。[当前界与猜想的差距](docs/JointNegativeContraction.md#四分之一还差多少)

对精确最优电路，还可约束整张图上的共享。若 $T$ 扇门足以检查强连通与有向环覆盖，那么所有在“强连通、有覆盖、无全圈”的图上各取固定值的内部门，其额外出线数与其中的 NOT 门数合计至多 $T+2$，允许这些门彼此依赖。对基线 $R_0$，存在大小为 $(1+o(1))S(n)$ 的电路族，在无穷多个二次幂规模上，**每种**配对都严格留下超过四分之一的门。[全图共享界](docs/JointNegativeContraction.md#全图中不区分这些负例的共享量) · [Lean 重放引理](Mobius/PairContraction.lean#L406) · [近最优反例](docs/StagedContraction.md)

**原有的单调版。** $r_{\rm mono}(m)$ 使用 $R_0$，在精确最优的 AND/OR 电路和有向配对中取最小值，允许每份接受证明重复用弧。猜想对每个充分大的 $m$ 有 $r_{\rm mono}(m)\le 1/2$，从而 $S_{\rm mono}(2m)\ge 2S_{\rm mono}(m)$。[单调猜想原文](docs/PairContraction.md#原创性可证伪的下一步及复核)

<a name="strong-pair-contraction-conjecture"></a>

#### 强配对收缩猜想（一般布尔电路，输出规模比例趋于零）

记 $\mathrm{Opt}_{\rm bool}(2m)$ 为计算 $H_{2m}$ 的全部门数最少的 AND/OR/NOT 电路。强猜想断言

$$
\lim_{m\to\infty}
\min_{C\in\mathrm{Opt}_{\rm bool}(2m)}\min_{\rho}
\frac{\lvert R_+(C\vert_\rho)\rvert}{S(2m)}=0.
$$

等价地，$r_+(m)\to0$。任给 $\epsilon>0$，从某个依赖于 $\epsilon$ 的规模起，每个 $m$ 都有一份精确最优电路 $C$ 和一份有向配对，使 $R_+$ 输出的电路至多用 $\epsilon S(2m)$ 扇门，在全部小图输入上计算 $H_m$。

取 $\epsilon=1/4$ 就得到一般布尔弱版。对任意固定的 $d>0$，取 $\epsilon=2^{-(d+1)}$，则所有充分大的 $m$ 都有 $S(2m)\ge 2^{d+1}S(m)$。沿二次幂规模迭代，即可排除 $S(n)=O(n^d)$。由于输入有 $n(n-1)$ 位，有向哈密顿回路判定将没有多项式规模电路族。这将推出 $\mathrm{NP}\not\subseteq\mathrm{P/poly}$，进而推出 $\mathrm{P}\ne\mathrm{NP}$。[倍增推导](docs/PairContraction.md#2-最优单调电路的逐级检验) · [Karp 的 NP 完全性定理，第 9 项](https://cgi.di.uoa.gr/~sgk/teaching/grad/handouts/karp.pdf) · [多项式时间的电路模拟，定理 13.12](https://files.boazbarak.org/introtcs/lnotes_book.pdf)

### 受限模型中的证据

每份门数为 $s$ 的精确最优单调电路，其内部门输出在首次使用以外至少还有 $(1/7-o(1))s$ 次引用。若一份配对能使其中正常数比例的额外引用所读的门同时变成零，出线计数就给出固定倍数的收缩。要达到单调版的一半，还须定量控制同一份配对实际消去的门数。[计数证明](docs/InternalSharing.md) · [证明所用的 Rao 匹配下界](https://homes.cs.washington.edu/~anuprao/pubs/matchinglowerbound.pdf#page=2)

若每条全圈都有一份证明，其中至多一成的不同弧被重复使用，各弧重复次数不限，则在这个类中，$2m$ 点和 $m$ 点的最小门数之比至少为 $2^{0.0620m-O(\log m)}$。这个数值比较两份分别取到最优的电路。在这个放宽的类里，每份最优电路经 $R_0$ 化简后的平均存活门数占比是否也趋于零，仍待证明。[按路径段缩点的证明](docs/ReadOneContraction.md#每条全圈的见证允许重复一部分弧)

有向环覆盖提供了一个对照。一份覆盖允许含有多个不相交的环，其弧仍然将每个顶点用作一次弧尾、一次弧头。相同配对保留较小的环覆盖问题。另取两层顶点，反向固定一份匹配、正向弧自由，就嵌入了任意二分完美匹配实例，给出所需的 read-1 规模下界。因此，同一个收缩证明也适用于 P 中的判定问题。[read-1 匹配下界](https://arxiv.org/html/2207.08701v3) · [Hopcroft–Karp 匹配算法](https://web.eecs.umich.edu/~pettie/matching/Hopcroft-Karp-bipartite-matching.pdf)

几何上已经能强制一致。对任何一对能使七块法诺板同时最优的全局表，七板的唯一坏方向必为公共芯内的同一个方向。外露面上每份合法的边界赋值又都能用**任意一个**芯内非零方向延拓，所以这个三选一的方向可以预先固定。哈密顿板编码另用标号排除小环。对两端都不是根的每条选中弧，起点标号必须小于终点标号。[共同方向定理](Mobius/ThreeFaceBoards.lean#L189) · [边界延拓充要条件](Mobius/ThreeFaceBoards.lean#L294) · [排除小环的约束](docs/HamiltonianBoards.md)

在 $\ell\ge 2$ 层的三线路板族里，每个顶点已经只有一个后继。即使开关起初全部可用、中间结果可以任意复用，在指定的寄存器模型中，判定这些后继组成一个环还是三个环，最坏也恰需 $\ell-1$ 条指令。配对收缩仍要回答的是，当每点可以有多条候选出弧时，选出一个全圈这一要求能否迫使最优单调电路中的固定比例门在同一份配对下消失。[模型与紧界](docs/PostReadSwitches.md) · [Lean 步数下界](Mobius/PostRead.lean#L215)

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

- [Mobius/](Mobius/) 与 [Mobius.lean](Mobius.lean)、[Audit.lean](Audit.lean)：全部 122 个 Lean 4 形式化模块、总入口与传递公理审计。
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
