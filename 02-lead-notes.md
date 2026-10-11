# Lead 备忘录（新增关键工具，2024-10-10）

记 $D_j=\operatorname{supp}(a_j)$，$P_n=\bigcup_{i\le n}D_i$，$\Omega_m:=D_m\cap P_{m-1}$（$D_m$ 的"旧素数"，即首次出现在 $m$ 之前的那些素数；$R_m:=D_m\setminus P_{m-1}$ 为"新素数"）。

## 标记（Label）
- **TCL**：$\exists N\ \forall m>N\ \exists i\le N:\ D_i\subseteq D_m$。
- **TCL$'$（弱化：见证不要求 $\le N$）**：$\exists N\ \forall m>N\ \exists i<m:\ D_i\subseteq D_m$。
- **G2**：$\exists N\ \forall m>N\ \forall j:\ D_j\cap D_m\cap Q_N\ne\varnothing$，其中 $Q_N=P_N$（等价地：$D_m\cap Q_N$ 是 $\mathcal D_\infty$ 的横截集）。
- **"危险的" $m$**：$\exists m'>m$ 使 $D_{m'}\cap\Omega_m=\varnothing$。

## 新引理 (L1)【已由 Lead 证明】
**若 $m$ 是危险的，则不存在 $i<m$ 使 $D_i\subseteq D_m$。**

证明：设 $D_i\subseteq D_m$（$i<m$）。因 $D_i\subseteq P_i\subseteq P_{m-1}$，故 $D_i\subseteq D_m\cap P_{m-1}=\Omega_m$。由 (P1) 任两项互不互素，取 $p\in D_i\cap D_{m'}\ne\varnothing$（$m'$ 为危险见证）。则 $p\in D_i\subseteq\Omega_m$，故 $p\in D_{m'}\cap\Omega_m\ne\varnothing$，与危险见证 $D_{m'}\cap\Omega_m=\varnothing$ 矛盾。∎

推论：危险 $m$ 必"无见证"（$D_i\not\subseteq D_m,\ \forall i<m$）。故
$$\text{TCL}'\Longrightarrow \text{G2}\Longrightarrow \text{TCL}\Longrightarrow \text{TCL}'.$$
- TCL$'\Rightarrow$G2：若 $m>N$ 危险，则它无见证，与 TCL$'$ 给出的 $i<m$ 矛盾；故 $m>N$ 都不危险，即 $D_{m'}\cap\Omega_m\ne\varnothing\ (\forall m'>m>N)$，取 $N'\ge N$ 使 $Q_{N'}\supseteq\Omega_m\ \forall m\le$ 有限个例外即可。
- G2$\Rightarrow$TCL（**实现引理**，已在 01 提及，请用它）：取 $T_m:=D_m\cap Q_N$，G2 说它是 $\mathcal D_\infty$ 的横截集；令 $k_m:=\prod_{p\in T_m}p$ 的适当幂 $\ge a_1$（$k_m\le a_1\prod_{p\in Q_N}p=:C$），则 $\operatorname{supp}(k_m)=T_m$ 是横截集，故 $k_m\in A_\infty$，且 $k_m\ge a_1$，由 (P5) $k_m=a_{i}$ 是项，$D_i=T_m\subseteq D_m$；而 $i\le C$（间隙 $\ge1$）。于是 TCL 成立，$N:=C$。
- TCL$\Rightarrow$TCL$'$ 显然。

**结论：三者等价；证明任意一个即可。** 推荐目标：**TCL$'$（"最终每个项都包含某个更早项的全部素因子"）**，配合 (L1) 使用。

## 更短的充分路线：FME（推荐并列攻击）

**FME**：$A_\infty$ 只有有限多个极小元（等价地：族 $\mathcal D_\infty=\{D_1,D_2,\dots\}$ 只有有限多个极小横截集）。

**FME ⟹ 原题**（不需要 Main Lemma / TCL / G2！）：设 $A_\infty$ 的极小元为 $b_1,\dots,b_t$，则 $A_\infty=\bigcup_i b_i\mathbb Z$，故 $A_\infty$ 以 $L=\mathrm{lcm}(b_1,\dots,b_t)$ 为周期。由 (P5) 序列是 $A_\infty\cap[a_1,\infty)$ 的递增枚举；对周期集做递增枚举满足：$\forall k\in A_\infty$，$(k,k+L]$ 中恰有 $T:=|A_\infty\cap(0,L]|$ 个元素，故 $a_{n+T}=a_n+L$（$n$ 充分大），即得原题。∎

**注意**：G2 ⟹ Main Lemma ⟹（$A_\infty=A_N$ 只有有限多极小横截集）⟹ FME，所以 FME 严格弱于 G2，可能更好证。

**数值（Lead）**：$A_\infty$ 的极小元个数在 $a_1\le 255255$ 的样本中 ≤ 7，且都较小（例：$a_1=15$: $\{6,10,15\}$；$a_1=35$: $\{10,15,35,42\}$；$a_1=187$: $\{22,102,187,231,238\}$；$a_1=15015$: $\{6,10,14,22,26,15015\}$；$a_1=385$: $\{14,30,66,231,385,399,418\}$；$a_1=210,2310,30030,46410$: $\{2\}$）。

**可能的抓手**：每个极小横截集 $S$ 的每个 $p\in S$ 都有"见证" $i(p)$ 使 $D_{i(p)}\cap S=\{p\}$；$b_S=\prod_{p\in S}p\in A_\infty$ 且（若 $\ge a_1$）是项；若素数 $p$ 整除所有项则 $p^e$ 是项、$S=\{p\}$ 唯一；可用 (L1)（危险 ⟹ 无见证）与"两个不相交横截集 = 击杀"做反证。

## 数值事实（Lead 与 verifier 独立跑）
- $\min N$(G2) 很小：$a_1\le200$ 时 $\le5$（最坏 $a_1=187$，危险对 $(5,6)$）；$a_1=385$ 时 $\le6$；多数 $a_1$ 为 1。
- 若某素数 $p$ 整除所有项，则 $p^e\in A_\infty$，$p^e$ 终将成为项（(P5)），给出支撑 $\{p\}$ 的见证——这是"见证存在"的最简单机制。
- 一般机制：后期项的最小素因子 $p_m\le\max D_1$ 有界；若某个"最小素因子类"最终唯一，则同类项之间共享小素数、跨类项需另找共享素数（危险对必须跨类且共享素数"新"）。
