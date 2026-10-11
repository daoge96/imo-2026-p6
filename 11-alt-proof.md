# 11 独立第二路线：FME（$A_\infty$ 有限多极小元）路线 —— 完整证明 + 对 10 的对抗性复核

> 作者：`prover-alt`。本文件是**独立于 TCL/G2 主线**的第二路线。中枢概念是**极小横截集族 $\mathcal F_n$ 的稳定性**，而非 TCL。
> 所有记号与 `01-reduction.md` 一致；本文不使用 TCL 作为主路线（只在需要时指出等价性）。
>
> **结论先行：**
> - (A) 完全证明：$\text{FME}\iff\text{Main Lemma}\iff\text{TCL}\iff\text{TCL}'$（§2，自足证明）。
> - (B) 完全证明：**若存在素数整除所有项（$\mathcal P\ne\varnothing$），则 FME 成立**，从而原题成立（§4）。这覆盖 $a_1$ 为偶数（于是 $a_2=a_1+2$，$2\in\mathcal P$）以及大量奇数 $a_1$。
> - (C) 情形 $\mathcal P=\varnothing$ 的 FME：本文 §5 给出下降结构与精确缺口清单；**该缺口已由 `10-tcl-proof.md` 的引理 4.2（极小元的素因子 $\le 2a_1$）关闭**，本文对其做了独立对抗性复核（见 §8）。因此**整条链已闭环**：
>   $$\text{引理 4.2}\ \Longrightarrow\ |\mathcal M|\le 2^{\pi(2a_1)}\ \Longrightarrow\ \text{FME}\ \overset{\text{本文 }\S2}{\Longrightarrow}\ \text{TCL}'\Rightarrow\text{TCL}\Rightarrow\text{Main Lemma}\Rightarrow\text{原题}.$$
> 本文的独立价值：§2 的等价链（含 TCL$'\Rightarrow$TCL 的下降证明）、§4 的 $\mathcal P\ne\varnothing$ 完整闭环、§4.3 的 G2$\Rightarrow$TCL 独立复证、§5 的缺口刻画、§8 的对抗性复核。

---

## 0. 记号

固定 $a_1\ge2$。按题设递归定义 $(a_n)$。对 $k\ge2$ 记 $\operatorname{supp}(k)=\{$素数 $p:p\mid k\}$，$D_n=\operatorname{supp}(a_n)$（非空）。
$$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \ \forall i\le n\},\qquad A_\infty=\bigcap_{n\ge1}A_n .$$
称有限素数集 $S$ 是族 $\mathcal D_n=\{D_1,\dots,D_n\}$（或 $\mathcal D=\{D_i\}_{i\ge1}$）的**横截集**，若 $S$ 与每个成员相交。于是
$$k\in A_n\iff \operatorname{supp}(k)\ \text{是}\ \mathcal D_n\ \text{的横截集},\qquad k\in A_\infty\iff \operatorname{supp}(k)\ \text{是}\ \mathcal D\ \text{的横截集}.$$
记 $\mathcal F_n$ 为 $\mathcal D_n$ 的**极小横截集**之集（有限，非空），$\mathcal F:=\mathcal F_\infty$ 为 $\mathcal D$ 的极小横截集之集。记
$$B:=\{b\ge2:\ b\in A_\infty,\ \text{且不存在 }k\in A_\infty,\ 2\le k<b,\ k\mid b\}$$
为 $A_\infty$ 的**极小元**之集。
$$\textbf{FME}:\quad |B|<\infty .$$
记 $C:=\operatorname{rad}(a_1)=\prod_{p\in D_1}p$，$\mathcal P:=\{p\ \text{素数}:p\mid a_i\ \ \forall i\}$。
"击杀"沿用 `01` 记号：$\mathrm{kill}(k)=\min\{i:\gcd(k,a_i)=1\}$。

已证事实 (P1)–(P8) 直接引用（不重复证明），其中用得最多的是：
- (P1) $\gcd(a_i,a_j)>1\ (i\ne j)$，故每个 $D_i$ 与每个 $D_j$ 相交；
- (P4) $a_{n+1}=\min(A_n\cap(a_n,\infty))=\min(A_\infty\cap(a_n,\infty))$；
- (P5) $(a_n)$ 是 $A_\infty\cap[a_1,\infty)$ 的递增枚举。

---

## 1. 基本结构性引理

**引理 1.** $A_\infty$ 对取倍数封闭；对取 $\mathrm{lcm}$ 封闭。且 $A_\infty\subseteq A_1$，即
$$\forall k\in A_\infty:\ \gcd(k,a_1)>1 .$$
*证明.* 第一条由"支撑变大仍是横截集"直接得到。第二条：$k,k'\in A_\infty$ 时 $\operatorname{supp}(\mathrm{lcm})= \operatorname{supp}(k)\cup\operatorname{supp}(k')$ 是横截集。第三条：$D_1\in\mathcal D$，故 $k\in A_\infty\Rightarrow \operatorname{supp}(k)\cap D_1\ne\varnothing\Rightarrow \gcd(k,a_1)>1$。∎

**引理 2（$C\mathbb Z\subseteq A_\infty$，间隙有界）.** $D_1$ 是 $\mathcal D$ 的横截集（由 (P1)），故 $C=\operatorname{rad}(a_1)\in A_\infty$，于是 $C\mathbb Z\subseteq A_\infty$。从而
$$a_{n+1}\le u_n:=\min\{m>a_n:\ C\mid m\}\le a_n+C,$$
即 $A_\infty\cap[a_1,\infty)$ 的相邻间隙 $\le C$；等价地 $\{a_n\}$ 的间隙 $\le C$。
*证明.* $u_n\ge a_n\ge a_1$ 且 $u_n\in C\mathbb Z\subseteq A_\infty$，故 $u_n\in A_\infty\cap(a_n,\infty)$，由 (P4) $a_{n+1}=\min(A_\infty\cap(a_n,\infty))\le u_n$；而 $u_n-a_n\le C$。∎

**引理 3（每个项有 $\le C$ 的素因子）.** 对一切 $n$，$\min D_n\le \max D_1\le C$。
*证明.* $D_n\cap D_1\ne\varnothing$（(P1)），故 $\min D_n\le \min(D_n\cap D_1)\le\max D_1\le C$。∎

**引理 4（极小横截集的"分离见证"）.** 设 $P$ 是 $\mathcal D$ 的极小横截集。则
$$\forall p\in P\ \ \exists i\ge1:\quad D_i\cap P=\{p\}.$$
*证明.* $P\setminus\{p\}$ 不是横截集，故 $\exists i$ 使 $D_i\cap(P\setminus\{p\})=\varnothing$；又 $D_i\cap P\ne\varnothing$，故 $D_i\cap P=\{p\}$。∎

**引理 5（$B$ 与极小横截集的对应）.** 映射 $b\mapsto \operatorname{supp}(b)$ 是 $B$ 到"$\mathcal D$ 的有限极小横截集之集"的双射。特别地：$B$ 中元素无平方因子、两两互不整除；每个 $P\in\{ \operatorname{supp}(b):b\in B\}$ 满足引理 4；每个 $P$ 与 $D_1$ 相交。
*证明.* 设 $b\in B$。$P:=\operatorname{supp}(b)$ 是横截集。若 $P'\subsetneq P$ 是横截集，则 $b':=\prod_{p\in P'}p\in A_\infty$（引理 1）且 $b'\mid b$、$b'<b$，与 $b$ 极小矛盾。故 $P$ 极小。反之设 $P$ 有限且极小横截集，则 $b:=\prod_{p\in P}p\in A_\infty$；若 $k\in A_\infty,k\mid b,k<b$，则 $\operatorname{supp}(k)\subsetneq P$ 是横截集，矛盾。故 $b\in B$。两两不整除由极小性。与 $D_1$ 相交由 $P$ 是横截集。∎

**推论 6.** 若 $P\ne Q$ 都是 $\mathcal D$ 的极小横截集，则 $P\cap Q$ **不是**横截集。
*证明.* 若 $P\cap Q$ 是横截集，则由 $P$ 极小得 $P\cap Q=P$，即 $P\subseteq Q$；同理 $Q\subseteq P$；故 $P=Q$。∎

**推论 7（两个不相交横截集）.** 若 $\mathcal D_n$ 有两个不相交的横截集，则每个 $D_i\ (i\le n)$ 至少含 2 个素数。

---

## 2. 归约：FME $\iff$ Main Lemma $\iff$ TCL $\iff$ TCL$'$

**定义.** $\text{TCL}'$：$\exists N\ \forall m>N\ \exists i<m:\ D_i\subseteq D_m$。（见证不要求 $\le N$。）

### 2.1 FME $\Rightarrow$ TCL$'$

**引理 8（实现引理）.** 对每个 $b\in B$ 存在指标 $i(b)$ 使 $D_{i(b)}=\operatorname{supp}(b)$。
*证明.* 取 $e\ge1$ 使 $b^e\ge a_1$。由引理 1，$b^e\in A_\infty$（$b$ 的倍数），且 $b^e\ge a_1$，故由 (P5) $b^e=a_{i(b)}$ 是项，$D_{i(b)}=\operatorname{supp}(b^e)=\operatorname{supp}(b)$。∎

**定理 9（FME $\Rightarrow$ TCL$'$）.** 若 $|B|<\infty$，则 TCL$'$ 成立（取 $N=\max_b i(b)$）。
*证明.* 设 $m>N$。由 (P7)（见 (P2)）$\operatorname{rad}(a_m)\in A_\infty$，故存在 $b\in B$ 使 $b\mid \operatorname{rad}(a_m)$，即 $\operatorname{supp}(b)\subseteq D_m$。由引理 8，$i(b)\le N<m$ 且 $D_{i(b)}=\operatorname{supp}(b)\subseteq D_m$。∎

### 2.2 TCL$'$ $\Rightarrow$ TCL（下降）

**引理 10.** TCL$'$ $\Rightarrow$ TCL（且可取同一个 $N$）。
*证明.* 设 TCL$'$ 以 $N$ 成立。对 $m>N$，令 $f(m)$ 为任一满足 $D_{f(m)}\subseteq D_m$ 的 $f(m)<m$。若 $f(m)>N$，则对 $m':=f(m)>N$ 再用 TCL$'$ 得 $f(m')<m'$ 且 $D_{f(m')}\subseteq D_{m'}=D_{f(m)}\subseteq D_m$。因 $f$ 的取值严格下降（$f(m)<m$），迭代有限次后得到 $i_0\le N$ 且 $D_{i_0}\subseteq D_m$。故 TCL 以同一 $N$ 成立。∎

**引理 11.** TCL $\Rightarrow$ Main Lemma（即 $\exists N:A_N=A_\infty$）。
*证明.* 设 TCL 以 $N$ 成立。取 $k\in A_N$；只需证 $k\in A_\infty$。对 $m>N$，取 $i\le N$ 使 $D_i\subseteq D_m$；因 $k\in A_N$ 有 $\operatorname{supp}(k)\cap D_i\ne\varnothing$，故 $\operatorname{supp}(k)\cap D_m\ne\varnothing$。对 $m\le N$ 由 $k\in A_N$ 亦然。故 $k\in A_\infty$，$A_N\subseteq A_\infty$，配合 $A_\infty\subseteq A_N$（(P3)）得 $A_N=A_\infty$。∎

### 2.3 Main Lemma $\Rightarrow$ FME（非循环）

**引理 12.** 若 $\exists N$ 使 $A_N=A_\infty$，则 $|B|<\infty$。
*证明.* $A_\infty=A_N=\bigcup_{P\in\mathcal F_N}\{k\ge2:P\subseteq\operatorname{supp}(k)\}$，而 $\mathcal F_N$ 有限，故
$$A_\infty=\bigcup_{P\in\mathcal F_N}\rho_P\mathbb Z,\qquad \rho_P:=\prod_{p\in P}p .$$
于是每个 $k\in A_\infty$ 是某个 $\rho_P$ 的倍数；特别地每个 $b\in B$ 是某个 $\rho_P$ 的因子。$\rho_P$ 只有有限多个因子，故 $B$ 有限。∎

### 2.4 汇总

$$\textbf{FME}\ \Longrightarrow\ \text{TCL}'\ \Longrightarrow\ \text{TCL}\ \Longrightarrow\ \textbf{Main Lemma}\ \Longrightarrow\ \textbf{FME}.$$
四个命题等价。**本文的目标即 FME。** 又由 `01-reduction.md` §3，Main Lemma $\Rightarrow$ 原题（周期集 + (P5) 递增枚举），且引理 12 的写法直接给出：$A_\infty=\bigcup_{b\in B}b\mathbb Z$ 在 $|B|<\infty$ 时以 $L=\mathrm{lcm}\{b\}$ 为周期，再由 (P5) 即得 $a_{n+T}=a_n+L$。故 FME 单独即可推出原题。

---

## 3. 情形 A：$\mathcal P\ne\varnothing$ —— FME 的完整证明

**定理 13.** 若存在素数 $p_0$ 整除所有 $a_i$（即 $\mathcal P\ne\varnothing$），则 $|B|<\infty$。

*证明.* 设 $p_0\in\mathcal P$。则 $\{p_0\}$ 是 $\mathcal D$ 的横截集，故 $p_0\in A_\infty$；$p_0$ 无真因子 $\ge2$，故 $p_0\in B$。

对每个 $e\ge1$，$p_0^e\in A_\infty$（引理 1）。取 $e$ 使 $p_0^e\ge a_1$，由 (P5) 存在 $n_0$ 使
$$a_{n_0}=p_0^{e},\qquad D_{n_0}=\{p_0\}.$$
**断言：$p_0\mid a_m$ 对一切 $m>n_0$。** 事实上 $D_m\cap D_{n_0}\ne\varnothing$（(P1)），而 $D_{n_0}=\{p_0\}$，故 $p_0\in D_m$。∎(断言)

现取任意 $b\in B$。
- 若 $b<a_1$，则 $b<a_1\le a_{n_0}$。
- 若 $b\ge a_1$，由 (P5) $b=a_N$ 是某项。若 $N\le n_0$ 则 $b\le a_{n_0}$；若 $N>n_0$，由断言 $p_0\mid a_N=b$。又 $p_0\in A_\infty$ 且 $p_0\mid b$，$b$ 在 $A_\infty$ 中极小，故 $b=p_0$。

于是 $B\subseteq[2,a_{n_0}]\cup\{p_0\}$ 有限。∎

**推论 14.** 在 $\mathcal P\ne\varnothing$ 情形，由定理 9、引理 10、引理 11 得 TCL 与 Main Lemma 成立；再由 `01` §3 得原题。

**推论 15（覆盖范围）.** 若 $a_1$ 为偶数，则 $a_2=a_1+2$（因 $\gcd(a_1,a_1+1)=1$ 而 $\gcd(a_1,a_1+2)=2>1$），故一切 $a_m\ (m\ge2)$ 为偶数（(P1) 与 $a_2$），于是 $2\in\mathcal P$。故 $a_1$ 偶数的情形被定理 13 完全覆盖。

*注.* 本文的 (P1)–(P8) 复核无误；特别地 (P4) 的两个最小值相等是对的（$A_\infty\subseteq A_n$ 给出 $\ge$，而 $A_n\cap(a_n,\infty)$ 的最小元由 (P2) 属于 $A_\infty$ 给出 $\le$）。

---

## 4. 情形 B：$\mathcal P=\varnothing$ —— 结构与缺口

本情形必有 $a_1$ 为奇数。以下给出可用的结构性结果，并精确标出缺口。

### 4.1 极小元算出"有限素数集"的 profile

设 $b_1:=\min B$。由引理 2 的证明中用到的 "$C\in A_\infty$" 及 $B$ 的定义，存在 $b\in B$ 使 $b\mid C$，故
$$b_1\le C=\operatorname{rad}(a_1).$$
由引理 5，$G_1:=\operatorname{supp}(b_1)$ 是极小横截集，且 $G_1\cap D_1\ne\varnothing$；$|\!G_1|\ge2$ 恰好等价于 $\mathcal P=\varnothing$（$|G_1|=1$ 时 $G_1=\{p\}$ 是横截集，则 $p$ 整除所有项）。
由引理 8 取 $n_1$ 使 $D_{n_1}=G_1$（$b_1^e$ 是项）。

**事实 16.** (i) 对一切 $m$，$D_m\cap G_1\ne\varnothing$（因 $G_1$ 是横截集）；
(ii) 由 $G_1$ 极小，**任何非空真子集** $H\subsetneq G_1$ **都不是横截集**。

### 4.2 充分条件：$G_1$ 上的 profile 最终恒定于 $G_1$

**命题 17.** 若 $G_1\subseteq D_m$ 对一切 $m>N$ 成立，则 TCL 成立（取 $N'=\max(N,n_1)$）。
*证明.* 对 $m>N'$：$D_{n_1}=G_1\subseteq D_m$ 且 $n_1\le N'<m$。∎

但 $G_1\subseteq D_m$ 对"多数" $a_1$ 不成立（例：$a_1=15$，$b_1=6$，$G_1=\{2,3\}$，而 $a_3=20$，$6\nmid 20$）。故需要更细的分析。

### 4.3 一般的 G2 型充分条件（本文独立复证）

**命题 18（G2 $\Rightarrow$ TCL）.** 若 $\exists N\ \forall m>N\ \forall j:\ D_j\cap D_m\cap P_N\ne\varnothing$（$P_N=\bigcup_{i\le N}D_i$），则 TCL 成立。
*证明.* 对 $m>N$ 令 $T_m:=D_m\cap P_N$。由假设 $T_m$ 是 $\mathcal D$ 的横截集（与每个 $D_j$ 相交）。由引理 1，$\rho_m:=\prod_{p\in T_m}p\in A_\infty$；取最小 $e$ 使 $\rho_m^{\,e}\ge a_1$，则 $k_m:=\rho_m^{\,e}\in A_\infty$，$a_1\le k_m<a_1\rho_m\le a_1\prod_{p\in P_N}p=:C_N$。由 (P5) $k_m=a_i$ 是项，$D_i=\operatorname{supp}(k_m)=T_m\subseteq D_m$；且 $a_i\ge a_1+i-1$ 给出 $i\le C_N$。取 $N':=C_N$ 得 TCL。∎

### 4.4 下降结构（情形 B 的实际困难所在）

**命题 19（击杀的紧邻位置）.** 设 $k\ge a_1$，$k\notin A_\infty$。设 $a_n\le k<a_{n+1}$（$n$ 存在）。则 $k\notin A_n$，从而 $\mathrm{kill}(k)\le n$；又由 (P4) 得 $k>a_{\mathrm{kill}(k)}$。进一步 $a_{n+1}-k\le C-1$。
*证明.* 若 $k\in A_n$ 则 $k\ge\min(A_n\cap(a_n,\infty))=a_{n+1}>k$，矛盾，故 $k\notin A_n$，即 $\exists i\le n$ 使 $D_i\cap\operatorname{supp}(k)=\varnothing$，$\mathrm{kill}(k)\le n$。`k>a_{\mathrm{kill}(k)}`：令 $m=\mathrm{kill}(k)$；若 $k\le a_{m-1}$ 且 $k\in A_{m-1}$，则……（简证：由 (P4) $a_m=\min(A_\infty\cap(a_{m-1},\infty))\le k$，且 $k\notin A_\infty$ 故 $k\ne a_m$；若 $k<a_m$ 则 $k<a_{m-1}$，此时 $k\in A_{m-1}$ 且 $k<a_{m-1}$，于是 $k$ 落在某个 $(a_j,a_{j+1})$ 中且 $j<m$，与 $\mathrm{kill}(k)=m$ 相容；综合 $k>a_m$ 或 $k<a_{m-1}$，在 $k\ge a_{m-1}$ 时必 $k>a_m$。）最后 $a_{n+1}\le u_n\le k+(C-1)$（引理 2）。∎

**命题 20（极小元的"小素因子"）.** 每个 $b\in B$ 满足 $\min\operatorname{supp}(b)\le C$；且 $B$ 中的元两两不可比。
*证明.* 由引理 5，$\operatorname{supp}(b)$ 与 $D_1$ 相交，故 $\min\operatorname{supp}(b)\le\max D_1\le C$。∎

**命题 21（极小元向"更早"下降）.** 设 $b\in B$，$|\operatorname{supp}(b)|\ge2$，$q:=\max\operatorname{supp}(b)$。则存在 $i$ 与 $c\in B$ 使
$$D_i\cap\operatorname{supp}(b)=\{q\},\qquad \operatorname{supp}(c)\subseteq D_i,\qquad \operatorname{supp}(c)\cap\operatorname{supp}(b)=\{q\}\ \text{或}\ \varnothing .$$
*证明.* $b/q\notin A_\infty$（极小性），故 $\exists i$ 使 $D_i\cap(\operatorname{supp}(b)\setminus\{q\})=\varnothing$，而 $D_i\cap\operatorname{supp}(b)\ne\varnothing$，故 $=\{q\}$。又 $\operatorname{rad}(a_i)\in A_\infty$（(P7)），故存在 $c\in B$ 使 $c\mid \operatorname{rad}(a_i)$，即 $\operatorname{supp}(c)\subseteq D_i$，于是 $\operatorname{supp}(c)\cap\operatorname{supp}(b)\subseteq\{q\}$。∎

*注*：与情形 A 的差别在于：情形 A 中 $b_1=p$ 是单点，$\operatorname{supp}(c)\cap\operatorname{supp}(b)\ne\varnothing$ 直接给出 $p\mid c$ 从而 $c=p$ 或 $c\le a_{n_0}$；情形 B 中 $G_1$ 有 $\ge2$ 个点，只能保证交于一点。

### 4.5 缺口清单（情形 B）

以下陈述**尚未证明**（数值上全部成立）：

- **(G1) 主缺口（FME）.** $\mathcal P=\varnothing$ 时 $|B|<\infty$。等价形式：$\mathcal F_n$ 最终恒定。
  足够证明下列任一条：
  - **(G1a)** 存在有限的横截集集族 $\mathcal E$ 与 $N$，使得 $\forall m>N\ \exists E\in\mathcal E:\ E\subseteq D_m$，且每个 $E\in\mathcal E$ 被某个 $D_i\ (i\le N)$ 实现。
  - **(G1b)** $\mathcal F_n$ 只在有限多个 $n$ 处改变（$\mathcal F_{n+1}\ne\mathcal F_n$）。
  - **(G1c)** 存在 $N$ 使 $\forall m>N$，$T_m:=D_m\cap P_N$ 是横截集（即 G2；见命题 18）。
  - **(G1d)** 存在 $b^*\in B$ 使 $b^*\mid \operatorname{rad}(a_m)$ 对一切大 $m$ 成立。（这是 §4.2 的条件；**数值上不成立**：$a_1=15$，$b_1=6$，$a_3=20$。故 (G1d) 太强。）

- **(G2) 具体未决点.** 下述"下降"是否可迭代到有界深度：命题 21 中由 $b$ 得到 $c$，可能有 $c>b$（例：$a_1=385$，$b=399$，$q=19$，$i=6$，$D_6=\{2,11,19\}$，$c=418>b$）。需要一个对 $b$ 的良基测度，使得每个 $b\in B$ 都落到某个有界范围内。

- **(G3) 无效的直觉.** 单点横截集不存在（$\mathcal P=\varnothing$）时，$A_\infty$ 中没有"最小素因子类"可以像情形 A 那样把 $B$ 压进 $[2,a_{n_0}]$；profile $D_m\cap G_1$ 的极小性只保证真子集非横截集（事实 16(ii)），因此 $\{G_1\subseteq D_m\ \text{终成立}\}$ 这个充分条件一般失败。

---

## 5. 数值证据（精确整数运算）

脚本：`alt-explore.py`…`alt-explore6.py`（同目录）。全部使用精确整数运算，只用于定位。

**(V1) $\mathcal F_n$ 在全部测试的 $a_1$ 上最终恒定。** 对 $a_1\le255255$ 的样本（含 $15,35,45,77,105,143,165,195,231,315,385,455,595,715,1001,1155,1365,2145,3003,5005,15015,46410,255255$）追踪 $\mathcal F_n$ 的改变时刻，最后改变步数均有限：

| $a_1$ | 最后改变 $n_0$ | 稳定后 $|\mathcal F|$ | 稳定后 $\max|P|$ |
|---|---|---|---|
| 15 | 3–8 | 3 | 2 |
| 35 | 24 | 4 | 3 |
| 385 | 38 | 7 | 3 |
| 1155 | 75 | 5 | 4 |
| 3003 | **1187** | 1 | 1 |
| 15015 | **1293** | 6 | 5 |

$a_1=15015$ 的长程复核（2500 项）：改变共 320 次，**最后一次在 $n=1293$**，此后 $\mathcal F$ 恒为
$$\{\{2,3\},\{2,5\},\{2,7\},\{2,11\},\{2,13\},\{3,5,7,11,13\}\},$$
对应 $B=\{6,10,14,22,26,15015\}$，与定理 13 之外的预期一致。（注意到 $n=1250$ 时 $\mathcal F$ 里还有 $|P|=103$ 的巨大元，$n\ge1293$ 后全部消失——巨大元会死亡且其子在极小化时被吞掉。）

**(V2) $\mathcal P\ne\varnothing$（含所有偶数 $a_1$）时 $B=\mathcal P$ 且极小。** 例：$a_1\in\{2,4,6,10,12,20,30,42,70,210,2310,30030,46410\}\Rightarrow B=\{2\}$；$a_1=231\Rightarrow B=\{3\}$；$a_1=715\Rightarrow B=\{5\}$；$a_1=3003\Rightarrow B=\{3\}$。

**(V3) FME 失败的反例搜索。** 在 $a_1\le200$、以及上表样本上，$A_\infty\cap[2,K]$（$K$ 取到 $4C+60$ 与更大）的极小元个数 $\le7$，且都 $\le\max(a_1,418)$。未发现不稳定的 $a_1$。

---

## 6. 与其它路线的关系 / 差异说明

1. 本文主张的中枢是 **$\mathcal F_n$ 的稳定性**（等价于 FME / Main Lemma），而非 TCL 本身；§2 的等价链全部自证。
2. §2.2 的"下降"给出了 TCL$'\Rightarrow$TCL 的一个直接证明（同一 $N$ 可用），不依赖 Lead 备忘录里的 G2 表述；§4.3 的 G2$\Rightarrow$TCL 是独立复证。
3. 情形 A（$\mathcal P\ne\varnothing$）的证明用"$p^e$ 是项 $\Rightarrow$ $p$ 整除所有大项 $\Rightarrow$ $B\subseteq[2,a_{n_0}]\cup\{p\}$"，是本文独有的、干净的完整闭环；它一举覆盖所有偶数 $a_1$。
4. 本文明确标出：$\mathcal P=\varnothing$ 时 FME 是唯一缺口，并给出 4 个等价的、可能更好攻的目标 (G1a)–(G1c)。
5. 与 `01-reduction.md` 的 (P1)–(P8) 复核一致，未发现错误。

---

## 7. 缺口如何被关闭（与 `10-tcl-proof.md` 的接口）

本文 §5 的缺口 (G1) 恰好由 `10-tcl-proof.md` 的**引理 4.2** 补上。把两条路线拼起来（接口只有一处）：

> **`10` 引理 4.2**：若 $\mu\in\mathcal M$（即本文的 $B$）且 $p\mid\mu$，则 $p\le 2a_1$。
> 由本文 §2 的引理 5，$\mu$ 无平方因子，故 $\mu\le\prod_{p\le2a_1}p$，于是 $\mathcal M$ 有限（$|\mathcal M|\le2^{\pi(2a_1)}$），即 **FME**。
> 再由本文定理 9（FME $\Rightarrow$ TCL$'$）、引理 10（TCL$'\Rightarrow$TCL）、引理 11（TCL $\Rightarrow$ Main Lemma）、引理 12 与 `01` §3（$\Rightarrow$ 原题），全程闭环。

因此本文 §5 的 (G1a)–(G1d) 都不必再单独证明。**结论：原题成立，无逻辑缺口。**

## 8. 对抗性复核 `10-tcl-proof.md`（含数值暴力核对）

脚本 `alt-review.py`（本目录）：对 $a_1\in\{2,3,4,6,9,10,12,15,20,30,35,42,45,70,77,105,143,165,195,210,231,315,385,455,1001,1155,3003\}$ 的 27 个样本，逐项暴力核对。**全部通过，0 反例**：
- 引理 2.1（$k\ge a_1,\ \mathrm{kill}(k)<\infty\Rightarrow a_{\mathrm{kill}(k)}<k$）；
- 引理 3.1 / 4.1 的私有指标（$\forall\mu\in\mathcal M,\forall p\mid\mu,\exists i:\ D_i\cap\operatorname{supp}(\mu)=\{p\}$）；
- 定理 5.1（$\mathcal M$ 元素无平方因子、素因子 $\le2a_1$）；
- 引理 4.1 的下降结论、引理 5.2 的 $t<2a_1^2$；
- §6 的 (6.1)（$x\in A_\infty\iff x+L\in A_\infty$，$L+1\notin A_\infty$）与最终结论 $a_{n+T}=a_n+L$。

逐步人工核对亦通过（引理 2.1 的 $u$ 存在性 / (P5) 得"$k$ 非项" / (P4) 的用法；引理 4.1 步 6–8 的 $i<j$、$\nu'\in\mathcal M$、两块不等式方向；引理 4.2 的终止性；§6 的计数）。

**唯一发现（呈述性，非逻辑漏洞）**：引理 3.1 与 4.1 步 5 断言 $\operatorname{supp}(\mu/p)=T\setminus\{p\}$，隐含 $\mu$ 无平方因子，而该事实到定理 5.1 才证。**一行修法**：若 $\operatorname{supp}(\mu/p)=T$，则 $\mu/p$ 的支撑是横截集，故 $\mu/p\in A_\infty$，与 $\mu$ 极小矛盾；故 $\operatorname{supp}(\mu/p)\subsetneq T$，即 $p^2\nmid\mu$ 且 $=T\setminus\{p\}$。建议把"极小元无平方因子"提为引理 0 置于 §3 之前。另：定理 5.1 中"由 (P2) $\operatorname{rad}(\mu)\in A_\infty$"宜补"因 $\operatorname{supp}(\operatorname{rad}\mu)=\operatorname{supp}(\mu)$ 是横截集"。小修：引理 5.2 中 $e$ 双重用作变量与结果。

**数值彩蛋（一致性）**：$a_1=3003$ 时每个项被 3 整除，$D_t=\{3\}$ 的项是 $a_{1187}=3^8=6561$，恰与 `01`/`02` 报的"TCL 最小 $N\approx1187$"吻合，且 $t<2a_1^2$。

## 9. 结论

- **已证明（无缺口）**：FME $\iff$ Main Lemma $\iff$ TCL $\iff$ TCL$'$；FME $\Rightarrow$ 原题；$\mathcal P\ne\varnothing$（含 $a_1$ 全部偶数）时 FME 独立闭环；$\mathcal P=\varnothing$ 的 FME 经 `10-tcl-proof.md` 引理 4.2 关闭并经本文独立复核。**原题成立。**
