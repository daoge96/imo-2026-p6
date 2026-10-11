# Lead 归约（已严格证明的部分 + 唯一剩余核心引理）

> 状态：以下 (P1)–(P7)、定理的"归约"部分均已由 Lead 严格证明（见各条括号内理由）。
> **唯一剩余任务：证明 TCL（或等价的 UCL）**，见文末"剩余核心问题"。

## 1. 记号

固定整数 $a_1\ge 2$。序列按题设递归定义。对整数 $k\ge 2$ 记
$$\operatorname{supp}(k):=\{p\ \text{素数}: p\mid k\},\qquad D_n:=\operatorname{supp}(a_n)\ (\ne\varnothing).$$
$$
A_n:=\{k\ge 2:\ \operatorname{supp}(k)\cap D_i\ne\varnothing\ \ \forall\, i\le n\},\qquad
A_\infty:=\bigcap_{n\ge 1}A_n .
$$
称有限素数集 $S$ 是 $\mathcal D_n:=\{D_1,\dots,D_n\}$ 的**横截集**，若 $S\cap D_i\ne\varnothing\ (\forall i\le n)$。于是
$$k\in A_n\iff \operatorname{supp}(k)\ \text{是}\ \mathcal D_n\ \text{的横截集},$$
特别地 $A_n$ 对"取倍数"封闭（$k\in A_n,\ k\mid k'\Rightarrow k'\in A_n$），且 $A_{n+1}\subseteq A_n$。

对整数 $k\ge2$ 记 $\mathrm{kill}(k):=\min\{i\ge1:\ \gcd(k,a_i)=1\}$（若无则 $=\infty$）。则
$$k\in A_\infty\iff \mathrm{kill}(k)=\infty,\qquad k\in A_N\iff \mathrm{kill}(k)>N .$$

## 2. 已证明的事实

- **(P1)** 由归纳：$a_{n+1}\in A_n$，且任意两项互不互素：$\gcd(a_i,a_j)>1\ (i\ne j)$。故 $D_i\cap D_j\ne\varnothing$。
  （理由：$a_{n+1}$ 的定义条件即 $\gcd(a_{n+1},a_i)>1\ \forall i\le n$；对 $i<j\le n+1$ 亦然。）
- **(P2)** 每个 $D_j$ 都是整个族 $\{D_i\}_{i\ge1}$ 的横截集（由 (P1) 两两相交）。故每个 $a_j\in A_\infty$，且 $a_j\ge2$ 时 $\operatorname{rad}(a_j)\in A_\infty$（$\operatorname{rad}$ 即最大无平方因子数，其支撑恰为 $D_j$）。 —— 这就是 (P7)。
- **(P3)** $A_\infty=\bigcap_n A_n\subseteq A_n$。
- **(P4)** $a_{n+1}=\min\bigl(A_n\cap(a_n,\infty)\bigr)=\min\bigl(A_\infty\cap(a_n,\infty)\bigr)$。
  （后者的最小值 $\ge$ 前者；而前者是项，由 (P2) 属于 $A_\infty$，故相等。）
- **(P5)** 序列 $(a_n)$ 恰是集合 $A_\infty\cap[a_1,\infty)$ 的递增枚举。
- **(P6)**（间隙有界）$\operatorname{rad}(a_1)\in A_\infty$，故 $a_{n+1}\le a_n+\operatorname{rad}(a_1)$，即 $a_n\le a_1+(n-1)\operatorname{rad}(a_1)$。
- **(P7)** 见 (P2)：对每个 $i$，$\operatorname{rad}(a_i)\in A_\infty$；特别地若 $\operatorname{rad}(a_i)\ge a_1$，则 $\operatorname{rad}(a_i)$ 本身就是序列中的一项（由 (P5)），即 $D_i$ 一定被某个项 $a_j$ 以 $D_j=D_i$ 的方式"实现"。
- **(P8)** 序列无穷且良定义：$M:=\operatorname{rad}(a_1\cdots a_n)$ 的任意倍数属于 $A_n$，故 $\{k>a_n:k\in A_n\}\ne\varnothing$。

## 3. 主引理（Main Lemma）——它蕴含原题

**Main Lemma.** 存在 $N\ge1$ 使 $A_N=A_\infty$（等价地：$\{\mathrm{kill}(k)<\infty\}$ 中的 $\mathrm{kill}(k)$ 有界）。

**Main Lemma ⟹ 原题。** 取 $N$ 使 $A_N=A_\infty$。则 $A_\infty$ 是"周期集"：令 $L:=\mathrm{lcm}(D_1,\dots,D_N)$（各素数之积，取最小公倍数），则 $A_N=\bigcap_{i\le N}\bigcup_{p\in D_i}p\mathbb Z$ 只依赖于 $k\bmod L$，即
$$k\in A_\infty\iff k+L\in A_\infty\qquad(\forall k\ge2).$$
又 $A_\infty\supseteq \operatorname{rad}(a_1)\mathbb Z$ 无限，令 $T:=|A_\infty\cap(0,L]|\ge1$。由 (P5) 序列是 $A_\infty\cap[a_1,\infty)$ 的递增枚举；而对任意 $k\in A_\infty$，区间 $(k,k+L]$ 中恰有 $T$ 个 $A_\infty$ 的元素（每个模 $L$ 的允许剩余类恰出现一次）。于是对每个 $n$ 有 $a_{n+T}=a_n+L$。∎

## 4. 与 Main Lemma 等价的组合命题（UCL）与充分条件（TCL）

**UCL.** 存在 $N$，使得对一切 $m>N$，存在非空 $J\subseteq\{1,\dots,N\}$ 满足
$$\bigcup_{j\in J}D_j\ \subseteq\ D_m .$$

**(a) UCL ⟹ Main Lemma。** 取 $k\in A_N$。对 $m>N$：$\operatorname{supp}(k)$ 是 $\mathcal D_N$ 的横截集，故与每个 $D_j\ (j\in J)$ 相交，从而与 $\bigcup_{j\in J}D_j$ 相交，于是与 $D_m$ 相交，即 $\gcd(k,a_m)>1$；对 $m\le N$ 由 $k\in A_N$ 亦然。故 $k\in A_\infty$，即 $A_N\subseteq A_\infty$，配合 (P3) 得 $A_N=A_\infty$。

**(b) TCL（单集情形）⟹ UCL。** 由 (P1)，$D_i$ 本身是 $\mathcal D_N$ 的横截集，所以 $J=\{i\}$ 可用。因此只要证：

> **TCL.** 存在 $N$，使得对一切 $m>N$，存在 $i\le N$ 使 $D_i\subseteq D_m$（即 $a_m$ 被某个"早期项的全体素因子"整除）。

**(c)（可选，供参考）逆命题。** 若 Main Lemma 成立而 UCL 不成立，则由横截集对偶（有限族 $\mathcal D_N$ 的横截集之极小元的集族等于 $\mathcal D_N$ 中若干成员之并的极小元集族）可得矛盾；证明者可自行选择是否需要。

**（注意）** "影子相等"命题（$D_m\cap P_N\in\{D_1,\dots,D_N\}$，$P_N=\bigcup_{i\le N}D_i$）在数值上**不成立**；而"$D_i\cap D_m$ 是 $\mathcal D_N$ 的横截集"这一较弱条件对 $N=1$ 就（平凡地）成立，单独也不够。请以 TCL/UCL 为准。

## 5. 已做的数值实验（精确整数运算，详见 `20-verification.md`）

1. 对 $a_1\le200$ 及 $15,35,77,105,210,385,1001,2310,3003,15015,30030$ 等：序列最终满足 $a_{n+T}=a_n+L$（例：$a_1{=}2\Rightarrow(T,L)=(1,2)$；$a_1{=}15\Rightarrow(8,30)$；$a_1{=}35\Rightarrow(34,210)$；$a_1{=}15015\Rightarrow L=30030$）。
2. 击杀事件有限：例如 $a_1=15015$ 共 19 次击杀，最后一次在第 52 步；此后 $A_n$ 稳定。
3. TCL 在长区间内成立（最小可用 $N$ 有限）：$a_1=3003\Rightarrow N\approx1187$；$a_1=15015\Rightarrow N\approx1293$；$a_1=46410\Rightarrow N\approx2334$。这些 $N$ 的量级≈"某个小支撑的项首次出现的位置"，提示：不变量应是**项的小支撑**（如素幂 $2^k,3^k$、或 $2^a3^b$ 之类）而不是横截集的影子。

## 6. 剩余核心问题（交给证明者）

证明 **TCL**（推荐）或直接证明 **UCL**。可用的抓手：
- (P1) 两两相交；每个 $D_i$ 都含 $D_1$ 中某个素数；(P7) 每个项的 $\operatorname{rad}$ 属于 $A_\infty$；
- 击杀 $=$ "两个不相交横截集"：第 $m$ 步被杀的恰是支撑为 $\mathcal D_{m-1}$ 的横截集且与 $D_m$ 不交的那些 $k$；
- 若素数 $p$ 整除所有项（$p\mid a_i\ \forall i$），则 $p^e\in A_\infty$，于是 $p^e$ 终将成为一项（(P5)），给出支撑 $\{p\}$ 的"见证项"。
