# TCL 的证明 —— 并附带证明更强/更基础的 FME

**作者**：prover-tcl（task-1）。**依赖**：`00-problem.md`、`01-reduction.md` 的 (P1)–(P8) 与 §1 的 `kill` 词典、§4 的等价链；`02-lead-notes.md` 的 (L1) 仅在"一致性核对"中使用。
**结论**：本文给出 **FME**（$A_\infty$ 只有有限多个极小元）与 **TCL**（$\exists N\ \forall m>N\ \exists i\le N:\ D_i\subseteq D_m$）的完整证明，二者都成立，且界显式：
$$\#\{\text{极小元}\}\le 2^{\pi(2a_1)},\qquad \text{TCL 可取 } N=2a_1^2 .$$
$\text{FME}\Rightarrow$ 原题（见 §6，走 Lead 在 02 中给出的最短路线）$\Rightarrow$ 不需要 Main Lemma/G2。TCL 则另外经 01 §4 推出 Main Lemma。**没有闭环缺口**（见 §8 存疑清单，均为"界未优化"，非逻辑缺口）。

---

## 1. 记号与引自 00/01 的已证事实

沿用 01 的全部记号：$\operatorname{supp}(k)=\{p\ \text{素}:p\mid k\}$，$D_n=\operatorname{supp}(a_n)$，$P_n=\bigcup_{i\le n}D_i$，
$$A_n=\{k\ge2:\ \operatorname{supp}(k)\cap D_i\ne\varnothing\ \ \forall i\le n\},\qquad A_\infty=\bigcap_{n\ge1}A_n,$$
$\mathrm{kill}(k)=\min\{i\ge1:\gcd(k,a_i)=1\}$（无则 $=\infty$）。有限集 $S$ 称为横截集，若 $S\cap D_i\ne\varnothing\ (\forall i)$；于是 $k\in A_\infty\iff \operatorname{supp}(k)$ 是横截集。

以下事实**已在 01 中证明**，本文直接引用（编号沿用 01）：

* **(P1)** 任意两项互不互素：$\gcd(a_i,a_j)>1\ (i\ne j)$；等价地每个 $D_j$ 都是族 $\{D_i\}_{i\ge1}$ 的横截集。
* **(P2)** 对每个 $j$：$a_j\in A_\infty$ 且 $\operatorname{rad}(a_j)\in A_\infty$。
* **(P3)** $A_\infty\subseteq A_n\subseteq A_m\ (m\le n)$。
* **(P4)(P5)** $a_{n+1}=\min\bigl(A_n\cap(a_n,\infty)\bigr)=\min\bigl(A_\infty\cap(a_n,\infty)\bigr)$，且 $(a_n)$ 是 $A_\infty\cap[a_1,\infty)$ 的严格递增枚举。
* **(P6)** 放置 $\operatorname{rad}(a_1)\in A_\infty$，故 $a_{n+1}-a_n\le\operatorname{rad}(a_1)$。
* **(P8)** 序列无穷、良定义。
* **(K)** （01 §1）对一切 $k\ge2,N\ge1$：$k\in A_N\iff \mathrm{kill}(k)>N$；$k\in A_\infty\iff\mathrm{kill}(k)=\infty$。
* **(M)** $A_\infty$ 对"取倍数"封闭；$A_\infty\ne\varnothing$（$\operatorname{rad}(a_1)\in A_\infty$）；$A_\infty\subseteq\{k\ge2\}$。

**定义 1.1（极小元）** $\mu\ge2$ 称为 $A_\infty$ 的**极小元**，若 $\mu\in A_\infty$ 且不存在 $\mu$ 的真因子 $\nu$（$2\le\nu<\mu$）满足 $\nu\in A_\infty$。记 $\mathcal M$ 为全部极小元之集。
**定义 1.2** 整数 $k$ 是**项**，指 $\exists t\ge1: k=a_t$。

**引理 1.3（极小元覆盖 $A_\infty$）** 每个 $k\in A_\infty$ 都有极小元 $\mu\in\mathcal M$ 使 $\mu\mid k$。
**证明** 对 $k$ 作强归纳（$k\ge2$）。若 $k$ 是极小元，取 $\mu=k$。否则存在真因子 $\nu\mid k$，$2\le\nu<k$，$\nu\in A_\infty$，由归纳假设得极小元 $\mu\mid\nu\mid k$。∎
于是由 (M)：$A_\infty=\bigcup_{\mu\in\mathcal M}\mu\,\mathbb Z_{\ge2}$。

---

## 2. 位置引理：被杀的数在"凶手"之后

**引理 2.1（位置引理）** 设 $k\ge a_1$ 且 $\mathrm{kill}(k)=i<\infty$，则 $a_i<k$。

**证明** 由 (K)：$k\in A_{i-1}$ 且 $k\notin A_i$。

1. $A_\infty\subseteq A_i$（(P3)），故 $k\notin A_\infty$。又 $k\ge a_1$，由 (P5)（$A_\infty\cap[a_1,\infty)$ 恰是项集）知 **$k$ 不是项**。
2. 令 $u:=\max\{t\ge1: a_t\le k\}$（存在，因 $a_1\le k$ 且 $a_t\to\infty$）。由 1. 知 $a_u\ne k$，故 $a_u<k$。又 $k$ 不是项且 $a_{u+1}$ 是大于 $a_u$ 的最小项，故
$$k<a_{u+1}. \tag{2.1}$$
3. 若 $u\le i-1$，则 $A_{i-1}\subseteq A_u$（(P3)），故 $k\in A_u$；与 $k>a_u$ 及 (P4)（$a_{u+1}=\min(A_u\cap(a_u,\infty))$）得 $a_{u+1}\le k$，与 (2.1) 矛盾。
4. 故 $u\ge i$，于是 $a_i\le a_u<k$。∎

**注 2.2** 引理 2.1 的思想是：$k$（$\ge a_1$ 的被害者）位于项序列中某个"空档"$(a_u,a_{u+1})$ 内，而 $k\in A_{i-1}$ 迫使 $u\ge i$，即凶手必在被杀者之前"足够久"。

---

## 3. 私有指标引理

**引理 3.1（私有指标）** 设 $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$，$T:=\operatorname{supp}(\mu)$。则存在 $i\ge1$ 使
$$D_i\cap T=\{p\}.$$

**证明** $T$ 是横截集（因 $\mu\in A_\infty$）。

* 若 $\mu=p$（即 $\operatorname{supp}(\mu)=\{p\}$）：$T$ 横截 $\Rightarrow p\in D_i\ (\forall i)$，取 $i=1$ 即得 $D_1\cap T=\{p\}$。
* 否则 $\mu/p\ge2$。因 $\mu$ 极小，$\mu/p\notin A_\infty$，由 (K) 得 $i:=\mathrm{kill}(\mu/p)<\infty$。故 $\gcd(\mu/p,a_i)=1$，即 $\operatorname{supp}(\mu/p)\cap D_i=\varnothing$；而 $\operatorname{supp}(\mu/p)=T\setminus\{p\}$，于是 $D_i\cap T\subseteq\{p\}$。另一方面 $T$ 横截给出 $D_i\cap T\ne\varnothing$，故 $D_i\cap T=\{p\}$。∎

---

## 4. 关键引理：极小元的素因子不超过 $2a_1$

**引理 4.1（下降步骤）** 设 $\nu\in\mathcal M$，$\nu>2a_1$，$p\in\operatorname{supp}(\nu)$。则存在 $\nu'\in\mathcal M$ 使
$$p\in\operatorname{supp}(\nu'),\qquad \nu'<\nu/p .$$

**证明** 记 $T:=\operatorname{supp}(\nu)$。

1. $\nu>2a_1\ge a_1$，故 $\nu\in A_\infty\cap[a_1,\infty)$，由 (P5) $\nu$ 是项：$\nu=a_j$（某 $j\ge1$）；于是 $T=\operatorname{supp}(a_j)=D_j$，仍是横截集（$T$ 横截已由 $\nu\in A_\infty$ 保证）。
2. $\nu/p\ge2$：否则 $\nu/p=1$，即 $\nu=p$；此时 $T=\{p\}$ 横截 $\Rightarrow p\mid a_i\ (\forall i)\Rightarrow p\mid a_1\Rightarrow p\le a_1<2a_1$，与 $\nu>2a_1$ 矛盾。
3. 又 $\nu/p\ge\nu/2>a_1$。因 $\nu$ 极小，$\nu/p\notin A_\infty$（$\nu/p$ 是 $\nu$ 的真因子且 $\ge2$），故 $i:=\mathrm{kill}(\nu/p)<\infty$（(K)）。
4. 用引理 2.1（注意 $k:=\nu/p\ge\nu/2>a_1$，故 $k\ge a_1$；且 $\mathrm{kill}(k)=i$）得
$$a_i<\nu/p. \tag{4.1}$$
5. $\gcd(\nu/p,a_i)=1\Rightarrow \operatorname{supp}(\nu/p)\cap D_i=\varnothing\Rightarrow D_i\cap T\subseteq\{p\}$；又 $D_i\cap T\ne\varnothing$（$T$ 横截），故
$$D_i\cap T=\{p\}. \tag{4.2}$$
6. 由 (4.1)：$a_i<\nu/p<\nu=a_j$，项严格递增，故 $i<j$。由 (P2)，$a_i\in A_\infty$ 且 $\operatorname{rad}(a_i)\in A_\infty$，$\operatorname{rad}(a_i)\ge2$。
7. 取 $\nu'$ 为集合 $\mathcal F:=\{\nu''\ge2:\ \nu''\mid \operatorname{rad}(a_i),\ \nu''\in A_\infty\}$ 中在整除意义下极小者（$\mathcal F\ne\varnothing$，含 $\operatorname{rad}(a_i)$；取定一个）。则 $\nu'\in\mathcal M$：若 $\nu''\mid\nu'$、$\nu''\in A_\infty$、$2\le\nu''<\nu'$，则 $\nu''\mid\operatorname{rad}(a_i)$ 故 $\nu''\in\mathcal F$，与 $\nu'$ 的取法矛盾。
8. $\operatorname{supp}(\nu')\subseteq\operatorname{supp}(\operatorname{rad}(a_i))=D_i$，结合 (4.2)：
$$\operatorname{supp}(\nu')\cap T\subseteq D_i\cap T=\{p\};$$
又 $\operatorname{supp}(\nu')\cap T\ne\varnothing$（$\nu'\in A_\infty$ 而 $T=D_j$ 横截），故 $\operatorname{supp}(\nu')\cap T=\{p\}$，特别 $p\in\operatorname{supp}(\nu')$。
9. 最后 $\nu'\le\operatorname{rad}(a_i)\le a_i\overset{(4.1)}{<}\nu/p$。∎

**引理 4.2（关键引理）** 设 $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$。则 $p\le2a_1$。

**证明** 若 $\mu\le2a_1$ 则 $p\le\mu\le2a_1$。设 $\mu>2a_1$。用引理 4.1 迭代定义序列 $(\nu_r)_{r\ge0}$：
$$\nu_0:=\mu,\qquad \nu_{r+1}:=\text{引理 4.1 对 }(\nu_r,p)\text{ 给出的 }\nu'\ \ (\text{当 }\nu_r>2a_1).$$
归纳地，只要 $\nu_r>2a_1$ 就有 $p\in\operatorname{supp}(\nu_r)$（$r=0$ 为假设；由引理 4.1 的结论 $p\in\operatorname{supp}(\nu_{r+1})$ 传递），且
$$\nu_{r+1}<\nu_r/p\le\nu_r/2 .$$
于是 $(\nu_r)$ 是严格递减的正整数序列，必在有限步 $k$ 停机；停机意味着（由构造）$\nu_k\le2a_1$（否则可继续一步）。又 $p\in\operatorname{supp}(\nu_k)$，故 $p\le\nu_k\le2a_1$。∎

**注 4.3** 迭代链的关键在于：链条每一步都保持同一个素数 $p$ 在支撑中（第 8 步的"$\operatorname{supp}(\nu')\cap T=\{p\}$"），而值至少除以 $p$，故链长 $\le\log_2\mu$。

---

## 5. FME：极小元只有有限多个，且 TCL 成立

**定理 5.1（FME）** $\mathcal M$ 有限。更精确地：
$$\mathcal M\subseteq\Bigl\{k\ge2\ \text{无平方因子}:\ \operatorname{supp}(k)\subseteq\{p\ \text{素}:p\le2a_1\}\Bigr\},$$
从而每个 $\mu\in\mathcal M$ 整除 $\prod_{p\le2a_1}p$，且 $\#\mathcal M\le2^{\pi(2a_1)}$（$\pi$ 为素数计数）。

**证明** 设 $\mu\in\mathcal M$。

* $\mu$ 无平方因子：若 $p^2\mid\mu$，则 $\operatorname{rad}(\mu)\mid\mu$、$\operatorname{rad}(\mu)<\mu$、$\operatorname{rad}(\mu)\ge2$，而由 (P2) $\operatorname{rad}(\mu)\in A_\infty$，与 $\mu$ 极小矛盾。
* 由引理 4.2，$\operatorname{supp}(\mu)$ 的每个元素 $\le2a_1$；无平方因子给出 $\mu=\prod_{p\in\operatorname{supp}(\mu)}p\le\prod_{p\le2a_1}p$。
* 满足条件的无平方因子数共有 $\le2^{\pi(2a_1)}$ 个（每个 $\le2a_1$ 的素子集对应一个）。∎

**引理 5.2（实现引理）** 设 $\mu\in\mathcal M$。则存在项 $a_t$ 使 $D_t=\operatorname{supp}(\mu)$，且 $t<2a_1^2$。

**证明** 取 $p\in\operatorname{supp}(\mu)$（非空，$\mu\ge2$），令 $e:=\min\{e\ge1:\mu p^e\ge a_1\}$，$k:=\mu p^e$。则 $\operatorname{supp}(k)=\operatorname{supp}(\mu)$（$p$ 已属支撑），$k\in A_\infty$（(M)：$k$ 是 $\mu$ 的倍数），$k\ge a_1$，且 $k=\mu p^e=\mu p^{e-1}\cdot p<a_1p\le2a_1^2$（用引理 4.2：$p\le2a_1$）。由 (P5) $k$ 是项：$k=a_t$，且 $D_t=\operatorname{supp}(k)=\operatorname{supp}(\mu)$。最后项严格递增（步长 $\ge1$）给出 $a_t\ge a_1+(t-1)$，故 $t\le k-a_1+1<2a_1^2$。∎

**定理 5.3（TCL）** 取 $N:=2a_1^2$。则对一切 $m>N$ 存在 $i\le N$ 使 $D_i\subseteq D_m$。

**证明** 设 $m>N$。由 (P2) $a_m\in A_\infty$，再由 (P2) $\operatorname{rad}(a_m)\in A_\infty$。由引理 1.3 取极小元 $\mu\mid\operatorname{rad}(a_m)$，则
$$\operatorname{supp}(\mu)\subseteq\operatorname{supp}(\operatorname{rad}(a_m))=D_m .$$
由引理 5.2 取项 $a_i$ 使 $D_i=\operatorname{supp}(\mu)$ 且 $i<2a_1^2=N$。于是 $i\le N$ 且 $D_i\subseteq D_m$。∎

**注 5.4（与 02-lead-notes 的关系）** 引理 4.2 正是 02 §FME"可能的抓手"的落地：每 $p\in S$ 有私有指标；此处进一步用"极小元链条"把 $p$ 压到 $\le2a_1$。02 的 (L1)（危险 $\Rightarrow$ 无见证）与本文一致：取 $N=2a_1^2$，TCL 给出 $m>N$ 有见证 $i\le N<m$，故由 (L1) 的逆否形式，**一切 $m>N$ 都不危险**——这正是 Lead 数值观察中"$\min N(\mathrm{G2})$ 很小"的定性来源。

---

## 6. 与原题的衔接（两条独立路线）

**路线 A（最短，只需 FME）** 由引理 1.3 与 (M)：$A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$。由定理 5.1，$\mathcal M$ 有限，令 $L:=\operatorname{lcm}\{\mu:\mu\in\mathcal M\}\ (\ge2)$。于是 $\mu\mid L\ (\forall\mu\in\mathcal M)$，从而对一切 $x\ge2$：
$$x\in A_\infty\iff x+L\in A_\infty. \tag{6.1}$$
（$\Leftarrow$：$x+L\in A_\infty$ 蕴含 $x+L\ge2$ 属于某个 $\mu\mathbb Z$，故 $x\in\mu\mathbb Z$，又 $x\ge2$，故 $x\in A_\infty$。）

再注意 $L+1\notin A_\infty$：否则 $L+1$ 属于某个 $\mu\mathbb Z$，即 $\mu\mid L+1$；而 $\mu\mid L$，故 $\mu\mid1$，矛盾。又 $1\notin A_\infty$（$A_\infty\subseteq\{k\ge2\}$）。

**计数**：对 $k\ge2$ 定义 $g(k):=|A_\infty\cap(k,k+L]|$。对 $k\ge2$，由 (6.1)（注意 $k+1\ge3>2$、$k+L+1\ge3>2$，两者相差 $L$）：
$$g(k+1)-g(k)=\bigl[k+L+1\in A_\infty\bigr]-\bigl[k+1\in A_\infty\bigr]=0,$$
故 $g$ 在 $\{2,3,4,\dots\}$ 上取常值，记该常值为 $T:=g(a_1)\ge1$（$\ge1$ 因 $a_1+L\in A_\infty\cap(a_1,a_1+L]$）。并且
$$T=g(2)=|A_\infty\cap(2,L+2]|=|A_\infty\cap(0,L]|,$$
最后一个等号：$|A_\infty\cap[3,L+2]|-|A_\infty\cap[2,L]|=\bigl[L+1\in A_\infty\bigr]+\bigl([L+2\in A_\infty]-[2\in A_\infty]\bigr)=0$（$[3,L+2]$ 与 $[2,L]$ 的对称差含于 $\{2,L+1,L+2\}$；用 (6.1) 得 $[L+2\in A_\infty]=[2\in A_\infty]$，用上文得 $[L+1\in A_\infty]=0$；又 $1\notin A_\infty$）。于是
$$|A_\infty\cap(k,k+L]|=T\qquad(\forall k\ge2). \tag{6.2}$$

取 $k=a_n\ (\ge a_1\ge2)$：由 (6.2)，$A_\infty\cap(a_n,a_n+L]$ 恰有 $T$ 个元素，它们都 $>a_n\ge a_1$，故由 (P5) 恰是接下来的 $T$ 个项 $a_{n+1},\dots,a_{n+T}$；其中最大者为 $a_n+L\in A_\infty$（(6.1)），于是
$$a_{n+T}=a_n+L\qquad(\forall n\ge1).$$
即原题（取 $T,L$ 如上）。∎

**路线 B（经 TCL，与 01 完全对接，用于交叉验证）** 定理 5.3 即 TCL $\Rightarrow$（01 §4(b)，取 $J=\{i\}$）UCL $\Rightarrow$（01 §4(a)）Main Lemma $\Rightarrow$（01 §3）原题。两条路线结论一致，互为独立校验。

---

## 7. 数值核对（非证明，仅定位；脚本见 `logs/`）

| 项 | 观测 | 与本文定理 |
|---|---|---|
| $\mathcal M$（$a_1\le200$ 等样本，`logs/explore3.py`、`explore4.py`） | 元素个数 $\le7$，全部素因子 $\le\max D_1\le a_1$ | 定理 5.1（界 $2a_1$ 更松） |
| $b_m:=\min\{k\in A_\infty:\operatorname{supp}(k)\subseteq D_m\}$ | $\max_m b_m\le a_1+\operatorname{rad}(a_1)\le2a_1$；每个 $b_m$ 都是 $\mathcal M$ 的元素 | 引理 4.2、5.2（$b_m$ 即"极小元中整除 $\operatorname{rad}(a_m)$ 者"） |
| 每个极小元 $\mu$ | 都存在项 $a_t$ 使 $D_t=\operatorname{supp}(\mu)$，且 $t$ 很小 | 引理 5.2（$t<2a_1^2$） |
| TCL 最小 $N^*$ | $a_1=3003$ 时 $\approx1187$；$2a_1^2\approx1.8\times10^7$ | 定理 5.3（界极松） |

`logs/verify_lemmas.py` 另对 $a_1\le2000$ 的样本逐项核对引理 2.1（对被杀 $k$ 验证 $a_{\mathrm{kill}(k)}<k$）、引理 4.2、以及 02 的 (L1)，均无违例。

---

## 8. 存疑 / 自查清单

1. **无逻辑缺口**：§1 的 (P1)–(P8)、(K) 均引自 01（已证）；引理 1.3、2.1、3.1、4.1、4.2、5.2 与定理 5.1、5.3 均在本文给出完整证明；§6 路线 A 只用 (P2)(P5)(M) 与本文定理 5.1，路线 B 只用 01 的 §3/§4。
2. **界很松（非缺口）**：定理 5.1 的 $2^{\pi(2a_1)}$、定理 5.3 的 $N=2a_1^2$ 都远大于数值观测；链条论证只用了"每步除以 $p$"这一最粗估计。可能的优化方向：$|{\operatorname{supp}(\mu)}|\le|D_1|+1$、$\mu\le a_1+\operatorname{rad}(a_1)$（数值均成立，本文未证）。
3. **边界情形已逐一处理**：$\mu=p$（素极小元，此时 $p\mid a_1$，$\mu/p=1$）在引理 3.1、4.1 中单列；$a_1=2$（$\mathcal M=\{2\}$，$N=8$）成立；$\operatorname{rad}(a_1)=a_1$ 或 $\mu\le2a_1$ 的退化分支直接取 $p\le\mu$。
4. **对 $a_1$ 无隐藏假设**：定理陈述与证明中只出现 $a_1$ 与 (P1)–(P8)；特别地**不需要**"某素数整除所有项"（该情形只是 $\mathcal M=\{p\}$ 的特例），也不需要 $a_1$ 为偶数/无平方因子等。
5. **引理 2.1 中 $k\ge a_1$ 的条件**：来自 (P5)（项 $\leftrightarrow A_\infty\cap[a_1,\infty)$ 中的元素），在引理 4.1 第 4 步处 $k=\nu/p>a_1$ 满足；若去掉该条件，需另行处理 $k<a_1$ 的小数，本文不需要。
6. **与 02 的 (L1)/G2/TCL$'$ 一致性**：已核（注 5.4）。(L1) 独立成立，本文结论与其不冲突；事实上 $N=2a_1^2$ 之后无"危险" $m$。
7. **未做**：Main Lemma 的直接证明（本文经 TCL 得到，未独立验证 01 §4(a) 的每一步，只引用其陈述）；G2 的独立证明（Lead 已有）。

---

### 附：核心证明链一览

$$\underbrace{\text{(P1) }T\text{ 横截}}_{\text{引理 3.1: 私有指标 }D_i\cap T=\{p\}}\ \Longrightarrow\ \underbrace{\text{引理 2.1: }a_{\mathrm{kill}(k)}<k}_{\text{击杀位置}}\ \Longrightarrow\ \underbrace{\text{引理 4.1: }\nu>2a_1\Rightarrow\exists\nu'<\nu/p,\ p\in\operatorname{supp}(\nu')}_{\text{下降步骤}}$$
$$\Longrightarrow\ \underbrace{\text{引理 4.2: }p\le2a_1}_{\text{关键}}\ \Longrightarrow\ \underbrace{\text{定理 5.1: } \mathcal M\ \text{有限}}_{\text{FME}}\ \Longrightarrow\ \underbrace{\text{引理 5.2: 每个 }\mu\text{ 被项实现}}_{D_t=\operatorname{supp}(\mu)}\ \Longrightarrow\ \text{TCL}\ \Longrightarrow\ \text{原题（§6）。}$$
