# 与 Arth Singh 的 crossing 下界如何对接

核对的主分支提交为 `31ce9aac07ca04c2d12e50635339ebda1fc37417`。Singh 给定的张量正是 W(x,y,u,v)=[x=v][y=u]，允许的切割也正是 xy|uv 与 xu|yv。本工程在一侧有时以 vu 代替 uv，仅仅置换了矩阵的列。[官方定义与陈述](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/README.md) · [67/49 的 Lean 定理](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/SixtySevenFortyNinths.lean#L1286)

将 P_F 延拓到任意四腿张量 T，记 P_F(T) 为 T=B+C 时，B 在第一切割与 C 在第二切割的矩阵秩之和的最小值；等价地，每个秩一项可自由选择其中一种切割。逐条腿分别施加可逆线性变换会保持 P_F，因为可正向和反向搬运每一项。限制各腿的字母集合则只会降低或保持 P_F。Singh 证明在任意域且 n≥7 时 P_F(W_n)≥⌈67n/49⌉。以下取有理数域，使本工程中的二倍归一化可逆。

## 256 次失败的最优残差

设 E=(R+C−2W)/2。本工程对任意最优四比特双表核验了

    E(x,y,u,v) = a(x)b(y)[v=x⊕h][u=y⊕h]，a,b∈{−1,+1}。

逐腿符号和置换都是可逆的，故 **P_Q(E)=P_Q(W₁₆)≥22**。这回答了把残差进一步拆成两类切割时的成本问题。固定任意一种切割，该残差秩为 256；22 给出允许混用两个切割时的下界，确切混合项数仍可更大。对八个字母，Singh 的结果与八平方构造合起来还给出 **11≤P_Q(W₈)≤16**。[本工程的残差等价](RigidityKernel.md)

## 已知 282 构造仍含 W₁₅

从忽略最高位的三比特商构造出发，只有行表的 (0,0) 变号，h=8。R 的变化只会发生在 (x,y)=(0,0) 或 (v,u)=(0,0) 的位置。取 x≠0、v≠8、y≠8、u≠0，扰动全部消失。在留下的四组各 15 个字母上，经异或 8 重标，残差恰好是一个完整的 W₁₅。因此 **P_Q(E₂₈₂)≥⌈67·15/49⌉=21**。此处只使用具体达到 282 的那对表。新模块 `NaslundRestriction` 给出所需逐项恒等式。从另一方面，R 的变化只落在原矩阵的一行与一列，行切秩至多 2，因此该见证还满足 |P_Q(E₂₈₂)−P_Q(W₁₆)|≤2。一次改动虽然降低了两个普通矩阵秩，仍保留相当大的混合修复成本。

还有一个更强的结论。保留两条外腿的全部 16 个字母，只让 y 与重标后的 u′=u⊕8 避开 {0,8}。余下 14 个标签之间的 (x,v′) 切片恰为 [y=u′]I₁₆。Singh 的 4/3 证明只要求有三个不同的切片标签，空间维数仍为 16。它对矩形切片系统逐行适用，故这个 **282 见证的混合修复至少也要 22 项**。这是从原文三切片证明推出的矩形版本，不能把针对方形 W₁₆ 的主定理直接套在该残差上。对于行 (0,0) 与列 (0,1) 都翻转的 304 见证，避开 {0,8,1,9} 后仍有 12 个干净标签，同样至少 22 项。由此，这两次单矩阵降秩都保留同一个已知的混合项数下界；当前没有由此确定混合项数的精确值。[原文的切片恒等式](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/paper/crossing-lower-bounds.tex#L447-L478) · [三个标签推出 4/3 的证明](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/paper/crossing-lower-bounds.tex#L530-L543)

## 与多块 1521 底数的关系

本工程把 W 的 t 次张量积精确分为 2t+1 个系数张量 G_k，对每个 G_k 同时控制两种秩 r_k、c_k 的乘积。将每组交给较便宜的一侧，就得到 P_Q(W_{8^t})≤Σ_k min(r_k,c_k)。直接代入分层计数 r_k≤234^t/6^k、c_k≤234^t/6^(2t−k)，得到 P_Q(W_{8^t})≤(7/5)39^t。四字母的对应有理参数给出 P_Q(W_{4^t})≤2·(34/3)^t。两种上界与 Singh 的线性下界相容。Singh 的论文另列出已有的 O(n^1.62) 上界，所以上述换算并未刷新一般 P(n) 的已知上界。1521 是本工程指定分组中同时分解的秩乘积底数，并非 P(8) 的数值。[Singh 论文的上界讨论](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/paper/crossing-lower-bounds.tex#L403-L417)

Singh 的精确线性下界、n=4 时的精确值 7，与该仓库的六项 border 分解使用不同的量。后者是多项式参数退化后的极限，直接替换精确的 #SAT 交叉还需系数提取与成本分析。已独立运行该仓库的两个精确 Python 核验器，分别复算 189/77 行证书与四字母 border 恒等式。本次交付将其域上秩下界作为外部定理引用，未将 Singh 的 Mathlib 工程并入本工程或重建整套 Mathlib 证明。[上游证明入口](https://github.com/Arth-Singh/crossing-lower-bounds/blob/31ce9aac07ca04c2d12e50635339ebda1fc37417/Solution.lean)
