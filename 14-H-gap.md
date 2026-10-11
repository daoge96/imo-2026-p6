# H 缺口的收尾：$X=\prod_{B}p\le a_1$ 路线、$|B|\le1$ 闭环与 $|B|\ge2$ 的定量约束

> **作者**：prover-h（task-6）。**依赖**：`30-final-proof.md`（记号与 (P1)–(P6)、(K)、(M)、引理 2.2/3.1/4.1/5.1/5.2，逐条自核后引用）、`13-mu-bound.md`（prover-mu 的 引理 1.1/2.1/3.3/3.4/5.1/5.3，本文复核并指出一处需要更正的写法）。
> **结论口径（先看这里）**：
> 1. **目标化归（已证，完整）**：只需对每个极小元 $\mu$ 证明 $\mu\le2a_1^2$，即可把 TCL 的显式常数写回 $N=2a_1^2$（§2）。特别地，Lead 的新目标 $X:=\prod_{p\in B}p\le a_1$（$B:=S\setminus D_1$）蕴含 $\mu\le\operatorname{rad}(a_1)X\le a_1^2$，因此也充分（§2 系 2.3）。
> 2. **已完全闭环的情形**（都给出 $\mu\le2a_1^2$，从而由 §2 常数成立）：$B=\varnothing$（$\mu\le a_1$）；$|B|=1$（两分支：$\mu/p<a_1$ 时 $\mu<2a_1^2$；$\mu/p\ge a_1$ 时 $\mu\le a_1^2/2$，且此时 $\neg$H）；$|S|=2$（**H 不可能**，新证明，§4 定理 4.2）；$|S|=1$（系 3.3）。
> 3. **唯一缺口（已收窄）**：$\text{H}\wedge\bigl[(|B|=2\wedge\min B>2a_1/\Pi)\vee|B|\ge3\bigr]$，$\Pi=\prod_{C}p$（见 §5 注 5.7）。缺口处已证的定量约束见 §5（定理 5.1、命题 5.4），其中 $|B|=2$ 时给出 $q_1q_2<(\prod_{C}p)^2$、$2p_2<\Pi p_1$、$\min B\ge a_1/\Pi$；数值（§7）在 $a_1\le1600$、$B_{\text{scan}}=8a_1$ 上 $X\le a_1$ 与 $\mu\le2a_1^2$ 均无反例。
> 4. **记号**：$S=\operatorname{supp}(\mu)$；$C:=S\cap D_1$；$B:=S\setminus D_1$；$A:=D_1\setminus S$；$X:=\prod_{p\in B}p$（$B=\varnothing$ 时 $X=1$）。恒等式（多处使用）：$\mu=\bigl(\prod_{C}p\bigr)X$、$\operatorname{rad}(a_1)=\bigl(\prod_{C}p\bigr)\bigl(\prod_{A}p\bigr)$。

---

## 1. 记号与引用（逐条自核）

固定整数 $a_1\ge2$，序列按题设定义，$D_n=\operatorname{supp}(a_n)$，
$$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \forall i\le n\},\quad A_\infty=\bigcap_n A_n,\quad \mathrm{kill}(k)=\min\{i:\gcd(k,a_i)=1\}.$$
$\mu\ge2$ 是极小元 $\iff$ $\mu\in A_\infty$ 且无真因子 $\in A_\infty$；$\mathcal M$ 为全体极小元。$k$ 是**项** $\iff\exists t:k=a_t$。有限素集 $T$ 是横截集 $\iff T\cap D_i\ne\varnothing\ \forall i$；于是 $k\in A_\infty\iff\operatorname{supp}(k)$ 是横截集。

以下在 `30-final-proof.md`（或 `01-reduction.md`）已证，本文引用：

* **(P1)** $\gcd(a_i,a_j)>1\ (i\ne j)$；每个 $D_j$ 是横截集。（30 §2 (P1)，即 $a_i\in A_\infty$ 的等价形式）
* **(P2)** 每个 $a_j\in A_\infty$；$k\in A_\infty\Rightarrow\operatorname{rad}(k)\in A_\infty$。（30 §2 (P2)）
* **(P3)** $A_{n+1}\subseteq A_n$；**(P4)** $a_{n+1}=\min(A_n\cap(a_n,\infty))$。
* **(P5)** $(a_n)$ 是 $A_\infty\cap[a_1,\infty)$ 的严格递增枚举；故 $k\ge a_1$ 是项 $\iff k\in A_\infty$。（30 §2 (P5)）
* **(K)** $k\in A_n\iff\mathrm{kill}(k)>n$；$k\in A_\infty\iff\mathrm{kill}(k)=\infty$。（30 §2 (K)）
* **(M)** $A_\infty$ 对取倍数封闭。（30 §2 (M)）
* **引理 2.2** 每个 $k\in A_\infty$ 被某 $\mu\in\mathcal M$ 整除；每个 $\mu\in\mathcal M$ 无平方因子。（30 §2）
* **引理 3.1（位置引理）** $k\ge a_1,\ \mathrm{kill}(k)=i<\infty\Rightarrow a_i<k$。（30 §3，已逐行自核）
* **引理 4.1（私有指标）** $\mu\in\mathcal M,\ p\in S\Rightarrow\exists i:D_i\cap S=\{p\}$。（30 §4）
* **引理 5.1（下降）** $\nu\in\mathcal M,\nu>2a_1,p\in\operatorname{supp}(\nu)\Rightarrow\exists\nu'\in\mathcal M:p\mid\nu',\operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\},\nu'<\nu/p$。（30 §5）
* **引理 5.2（素因子界）** $\mu\in\mathcal M,p\in S\Rightarrow p\le2a_1$。（30 §5）

以下三条在 `13-mu-bound.md` 已证，本文复核后引用（并修正其一处记号）：

* **引理 $\ast$（$D_1$ 饱和）** $D_1\subseteq S\Rightarrow S=D_1$；故 $B\ne\varnothing\Rightarrow A\ne\varnothing$，且 $A=\varnothing\Rightarrow S=D_1\Rightarrow B=\varnothing$。（13 引理 1.1，证明只用引理 4.1 与 (P1)：取 $p\in B$、$i$ 使 $D_i\cap S=\{p\}$，再取 $\rho\in D_i\cap D_1$；若 $D_1\subseteq S$ 则 $\rho\in S$，故 $\rho=p\in D_1$，与 $p\notin D_1$ 矛盾。）
* **引理 $\ast\ast$（强化下降）** $\nu\in\mathcal M,\ p\in\operatorname{supp}(\nu),\ \nu>a_1p\Rightarrow\exists\nu'\in\mathcal M$：$p\mid\nu'$，$\operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\}$，$\nu'<\nu/p$。（13 引理 2.1；证明与引理 5.1 逐字相同，只用位置引理，条件换成 $\nu/p>a_1$。特别地 H 成立时对一切 $p\in S$ 都有 $\mu>a_1p$，故可用。）
* **引理 $\ast\ast\ast$（$B\to A$ 对应）** 设 $p\in B$，$i_p:=\mathrm{kill}(\mu/p)$（H 下有限）。则 $D_{i_p}\cap D_1\ne\varnothing$ 且 $D_{i_p}\cap D_1\subseteq A$；故 $\exists q_p\in A$：$q_p\mid a_{i_p}$。（13 引理 5.1，证明只用 (P1) 与引理 4.1。）

**自核注 1.1** 13 §3.4.2 与 §4 使用了 "$T_p<\mu/p$"（$T_p=a_{i_p}p$）。但 13 引理 3.3.1 本身只给出 $T_p<\mu$（因为位置引理只给 $a_{i_p}<\mu/p$，乘 $p$ 后得 $T_p<\mu$）。$T_p<\mu/p$ 需要额外的 $a_{i_p}p^2<\mu$。本文以下按**正确版本**（$T_p<\mu$、$a_{i_p}<\mu/p$）推导；§6 给出一条不依赖 $T_p<\mu/p$ 的 $|S|=2$ 新证明。

---

## 2. 目标化归：$\mu\le2a_1^2$ 就够了；$X\le a_1$ 也够

**引理 2.1（实现项的指标界）** 设 $\mu\in\mathcal M$，$p\in S$，$j:=\min\{s\ge0:\mu p^s\ge a_1\}$，$k:=\mu p^j$。则 $k\in A_\infty$、$\operatorname{supp}(k)=S$、$k\ge a_1$，故 $k=a_t$ 是项且 $D_t=S$；并且
$$t\le k-a_1+1,\qquad\text{且}\quad j\ge1\Rightarrow k<a_1p\le2a_1^2,\qquad j=0\Rightarrow k=\mu .$$
证明：$\operatorname{supp}(k)=\operatorname{supp}(\mu)=S$（$p\in S$）。(M) 给 $k\in A_\infty$；$k\ge a_1$ 由 $j$ 的取法。由 (P5) $k=a_t$、$D_t=\operatorname{supp}(k)=S$。项严格递增给 $a_t\ge a_1+(t-1)$，故 $t\le k-a_1+1$。$j\ge1$ 时 $k=\mu p^{j-1}\cdot p<a_1p\le2a_1^2$（引理 5.2）；$j=0$ 时 $k=\mu$。∎

**定理 2.2（化归，完整）** 若 $\forall\mu\in\mathcal M:\mu\le2a_1^2$，则 TCL 的显式常数可取 $N=2a_1^2$：对一切 $m>N$ 存在 $i\le N$ 使 $D_i\subseteq D_m$。

证明：取 $m>N$。由 (P2) $\operatorname{rad}(a_m)\in A_\infty$，由引理 2.2 取 $\mu\in\mathcal M$，$\mu\mid\operatorname{rad}(a_m)$，则 $S=\operatorname{supp}(\mu)\subseteq D_m$。取 $p\in S$ 与引理 2.1 的 $k=a_t$：若 $j\ge1$ 则 $t\le k-a_1+1<2a_1^2=N$；若 $j=0$ 则 $k=\mu\le2a_1^2$，故 $t\le\mu-a_1+1<2a_1^2=N$。于是 $i:=t\le N$ 且 $D_i=S\subseteq D_m$。∎

（与 30 定理 6.3/注 的接口：把那里的"实现引理"替换为本定理即可，常数由 $\max\{2a_1^2,\prod_{p\le2a_1}p\}$ 改回 $2a_1^2$。）

**系 2.3（Lead 的目标充分）** 若 $\forall\mu\in\mathcal M:\ X\le a_1$，则 $\mu=\bigl(\prod_C p\bigr)X\le\operatorname{rad}(a_1)X\le a_1^2\le2a_1^2$，故定理 2.2 给出 $N=2a_1^2$。

**注 2.4（H 与常数的关系）** H $\iff\forall p\in S:\mu/p\ge a_1$；$\neg$H 时取 $p$ 使 $\mu/p<a_1$，则 $\mu<a_1p\le2a_1^2$（引理 5.2）故由引理 2.1（$j=0$ 分支 $k=\mu\le2a_1^2$）同样得常数。因此"$\mu\le2a_1^2$"与"$\neg$H"是两条平行的充分路线；本文两条都推进。

---

## 3. H 的初步结构（完整证明）

**引理 3.1** 设 H 成立。则

1. $\forall p\in S$：$\mu/p>a_1$；特别 $\mu>a_1\max S\ge2a_1$。
2. $B\ne\varnothing$ 且 $A\ne\varnothing$；$C\ne\varnothing$。
3. $\forall p\in B$：$i_p:=\mathrm{kill}(\mu/p)<\infty$，$a_{i_p}<\mu/p$，$D_{i_p}\cap S=\{p\}$，且 $\exists q_p\in A:q_p\mid a_{i_p}$，故 $p\,q_p\le a_{i_p}<\mu/p$。
4. $\forall p\in S$：$\mu/p\notin A_\infty$（$s\ge2$ 时），且 $p\le2a_1$。

证明：

1. H 给 $\mu/p\ge a_1\ge2$，故 $\mu/p$ 是 $\mu$ 的真因子、$\ge2$，由极小性 $\mu/p\notin A_\infty$，故 $i:=\mathrm{kill}(\mu/p)<\infty$（(K)）。若 $\mu/p=a_1$，则位置引理（$k=\mu/p=a_1\ge a_1$）给 $a_i<\mu/p=a_1\le a_i$，矛盾；故 $\mu/p>a_1$。取 $p=\max S\ge2$ 得 $\mu>a_1\max S\ge2a_1$。
2. $\mu>2a_1>a_1$ 是项（(P5)）。若 $B=\varnothing$ 即 $S\subseteq D_1$，则 $\mu=\prod_S p\le\operatorname{rad}(a_1)\le a_1<2a_1<\mu$，矛盾；故 $B\ne\varnothing$，由引理 $\ast$ 得 $A\ne\varnothing$。$C=S\cap D_1\ne\varnothing$ 因 $S$ 是横截集（取 $i=1$）。
3. 第 1 条给 $\mu/p>a_1$，故 $\mu/p\notin A_\infty$ 且 $i_p<\infty$；位置引理给 $a_{i_p}<\mu/p$。又 $\gcd(\mu/p,a_{i_p})=1$ 即 $D_{i_p}\cap(S\setminus\{p\})=\varnothing$，而 $D_{i_p}$ 是横截集，故 $D_{i_p}\cap S=\{p\}$，特别 $p\mid a_{i_p}$。最后 $p\notin D_1$，而 $D_{i_p}\cap D_1\ne\varnothing$（(P1)），其元素 $\notin S$（否则 $\in D_{i_p}\cap S=\{p\}\ni p\in D_1$，矛盾），故 $\in A$（引理 $\ast\ast\ast$）。∎
4. 第 1 条已给 $\mu/p\notin A_\infty$；$p\le2a_1$ 是引理 5.2。∎

**系 3.2（H 排除 $\mu\le2a_1$ 的极小元）** H 成立 $\Rightarrow\mu>2a_1$。故若 $\mu\le2a_1$ 则 $\neg$H，从而 $\mu<2a_1^2$（注 2.4）。特别地，"$\mu\le2a_1$"（prover-mu 的目标 T1）是比本文目标更强的充分条件。

**系 3.3（$|S|=1$）** $S=\{p\}$ 时 $\mu=p$，$\mu/p=1<a_1$，故 $\neg$H；且 $\mu=p\le2a_1\le2a_1^2$。

---

## 4. $|B|\le1$ 的完全闭环，以及 $|S|=2$ 的 H-排除

本节的 $B=\varnothing$、$|B|=1$、$|S|=2$ 三种情形下都得到 $\mu\le2a_1^2$（更强地 $\mu\le a_1^2/2$ 或 $\neg$H），于是定理 2.2 可用。

**定理 4.1（$|B|\le1$ 时不用 H 也闭环）** 设 $\mu\in\mathcal M$，$B=S\setminus D_1$，$|B|\le1$。则 $\mu\le a_1^2/2\le2a_1^2$（$a_1=2$ 时按 $B=\varnothing$ 分支亦成立）。

证明：**分支 1：$B=\varnothing$。** $S\subseteq D_1$，故 $\mu=\prod_S p\le\operatorname{rad}(a_1)\le a_1\le a_1^2/2$（$a_1\ge2$）。

**分支 2：$B=\{p\}$。** 此时 $\mu=p\cdot\prod_C p$，$C=S\cap D_1\ne\varnothing$（$S$ 横截，取 $i=1$），故 $\mu/p=\prod_C p\ge2$、$\mu/p\notin A_\infty$，$i_p:=\mathrm{kill}(\mu/p)<\infty$。

* 子分支 2a：$\mu/p<a_1$。则 $\mu=p\cdot(\mu/p)<p\,a_1\le2a_1^2$（引理 5.2），更强地 $\mu/p<a_1$ 即 $\neg$H。
* 子分支 2b：$\mu/p\ge a_1$。若 $\mu/p=a_1$，则位置引理给 $a_{i_p}<\mu/p=a_1\le a_{i_p}$，矛盾；故 $\mu/p>a_1$，位置引理给 $a_{i_p}<\mu/p=\prod_C p\le\operatorname{rad}(a_1)$。又 $A\ne\varnothing$（引理 $\ast$，因 $B\ne\varnothing$），由引理 $\ast\ast\ast$ 取 $q_p\in A$，$q_p\mid a_{i_p}$；而 $p\mid a_{i_p}$（$D_{i_p}\cap S=\{p\}$）且 $p\ne q_p$（$p\notin D_1\ni q_p$），故 $p\,q_p\mid a_{i_p}$，于是
$$p\,q_p\le a_{i_p}<\prod_C p\le\operatorname{rad}(a_1)\ \Longrightarrow\ p<\frac{\operatorname{rad}(a_1)}{q_p}\le\frac{\operatorname{rad}(a_1)}2 .$$
（$p\notin D_1$、$q_p\in D_1$ 都是素因子，故 $q_p\mid\operatorname{rad}(a_1)$、$p\nmid q_p$，于是 $\operatorname{rad}(a_1)/q_p$ 是 $\operatorname{rad}(a_1)$ 的整数因子，$\ge\operatorname{rad}(a_1)/q_p$ 中不含 $p$…… 直接用 $q_p\ge2$ 即得第二个不等号。）于是
$$\mu=p\cdot\prod_C p<\frac{\operatorname{rad}(a_1)}{q_p}\cdot\operatorname{rad}(a_1)\le\frac{a_1^2}2\le2a_1^2 .$$
（$\operatorname{rad}(a_1)\le a_1$。）∎

**定理 4.2（$|S|=2$ 时 H 不可能；新）** 设 $\mu\in\mathcal M$，$S=\{p,q\}$。则 $\neg$H，从而 $\mu<2a_1^2$。

证明：反设 H。由引理 3.1.1，对 $x\in S$ 有 $\mu/x>a_1$；又 $\mu/x$ 是 $\mu$ 的真因子且 $\ge2$（$x\le\mu/2$），故 $\mu/x\notin A_\infty$，得 $i_x:=\mathrm{kill}(\mu/x)<\infty$（(K)）。位置引理（$k:=\mu/x>a_1\ge a_1$）给
$$a_{i_x}<\mu/x .$$
又 $\gcd(\mu/x,a_{i_x})=1$ 给 $D_{i_x}\cap(S\setminus\{x\})=\varnothing$，而 $D_{i_x}$ 是横截集，故 $D_{i_x}\cap S=\{x\}$，特别 $x\mid a_{i_x}$。写 $a_{i_x}=x\,m$（$m\ge1$ 整数）。若 $m\ge2$，则
$$a_{i_x}\ \ge\ 2x\ >\ 2a_1\ \ge\ \mu/x\ >\ a_{i_x}$$
（中间：$x>a_1$ 由 $\mu/x=a_1$ 不可能——否则位置引理给 $a_{i_x}<a_1\le a_{i_x}$——即引理 3.1.1；$\mu/x\le2a_1$ 由引理 5.2，因 $\mu/x$ 是 $\mu$ 的素因子），矛盾。故 $m=1$，即 $a_{i_x}=x$。

于是 $x=a_{i_x}\in A_\infty$，故 $\operatorname{supp}(x)=\{x\}$ 是横截集，即 $x\mid a_j$ 对一切 $j$，特别 $x\mid a_1$，即 $x\in D_1$。对 $x=p$ 与 $x=q$ 都成立，故 $S\subseteq D_1$，于是 $\mu=pq\le\operatorname{rad}(a_1)\le a_1$；但 H 给 $\mu>a_1\max S\ge2a_1>a_1$（引理 3.1.1），矛盾。∎

**注 4.3** 定理 4.2 只用引理 3.1、位置引理与引理 5.2，不用任何乘积估计、也不用 13 §3.4.2 的 $T_p<\mu/p$；这是对 13 §4 的 $s=2$ 分支的独立（且更省）复核。把同一技巧用于一般 $s$ 得到下面这条**对 $s\ge3$ 仍然有效**的信息（§5 使用）：

> **系 4.4** 设 H 成立，$x\in S$。则或者 $x\in D_1$（当 $a_{i_x}=x$），或者 $a_{i_x}\ge2x$。特别对 $x\in B$（此时 $x\notin D_1$，故 $a_{i_x}\neq x$）有
> $$2x\le a_{i_x}<\mu/x,\qquad\text{从而}\quad x^2<\mu/2,\ \ x<\sqrt{\mu/2}.$$

证明：$a_{i_x}=x m$、$m\ge1$；$m=1$ 即 $a_{i_x}=x$，由定理 4.2 证明中的推理得 $x\in D_1$；故 $x\notin D_1$ 时 $m\ge2$，即 $a_{i_x}\ge2x$；再用 $a_{i_x}<\mu/x$。∎

---

## 5. $|B|\ge2$：H 下的全部定量约束（已证）与缺口

**定理 5.1（H 下的乘积约束）** 设 H 成立，$|B|\ge2$。则
$$\boxed{\ X^{\,2-|B|}\cdot\prod_{p\in B}q_p\cdot\Bigl(\prod_{A}p\Bigr)^{|B|}<\operatorname{rad}(a_1)^{|B|}\ }\tag{5.1}$$
其中 $q_p\in A$ 由引理 3.1.3 给出（于是 $q_p\mid a_{i_p}$，$p\,q_p\le a_{i_p}<\mu/p$）。特别

* $|B|=2$：$\ q_1q_2<\bigl(\prod_C p\bigr)^2$；
* $|B|\ge3$：$X>\prod_B q_p\cdot\bigl(\prod_A p\bigr)^{|B|}/\operatorname{rad}(a_1)^{|B|}$（对 $X$ 只有下界）；
* 一般地 $1<X^{(|B|-1)}$-型结论：$\prod_B q_p<(\prod_C p)^{|B|}X^{|B|-2}$。

证明：对每个 $p\in S$，由引理 3.1.3，$a_{i_p}<\mu/p$ 且 $D_{i_p}\cap S=\{p\}$，故 $p\mid a_{i_p}$；于是 $U_p:=a_{i_p}$ 满足
$$U_p\in A_\infty,\qquad \operatorname{supp}(U_p)\cap S=\{p\},\qquad p\,q_p\le U_p<\frac{\mu}{p}.\tag{5.2}$$
（$U_p$ 是项；$\operatorname{supp}(U_p)\cap S=\{p\}$ 由 $D_{i_p}\cap S=\{p\}$；$U_p\in A_\infty$ 由 (P2)；上界即位置引理。）对 $p\in B$ 连乘（只用上界）：
$$\prod_{p\in B}U_p<\prod_{p\in B}\frac{\mu}{p}=\frac{\mu^{|B|}}{X}. \tag{5.3}$$
（用 $\prod_{p\in B}p=X$。注意：这里用的是 $U_p=a_{i_p}<\mu/p$，即 13 的正确版本，不需 $a_{i_p}p<\mu/p$。）另一方面由 (5.2) 的下界 $\prod_{p\in B}U_p\ge X\prod_{p\in B}q_p$。代入 (5.3)：
$$X^2\prod_{p\in B}q_p<\mu^{|B|}=\Bigl(\bigl(\prod_C p\bigr)X\Bigr)^{|B|}\ \Longrightarrow\ X^{2-|B|}\prod_{p\in B}q_p<\Bigl(\prod_C p\Bigr)^{|B|}. \tag{5.4}$$
再用 $A\sqcup C=D_1$、$C=S\cap D_1$：$\operatorname{rad}(a_1)=(\prod_C p)(\prod_A p)$，代入 (5.4) 得 (5.1)。∎

**推论 5.2（若干等价形式与上界）** 在 H 且 $|B|\ge2$ 下：

1. $\forall p\in B$：$a_{i_p}\ge2p$（系 4.4），$p^2q_p<\mu=(\prod_C p)X$，即 $p<\dfrac{(\prod_C p)(X/p)}{q_p}$；特别 $p<\sqrt{\mu/2}$，即 $p^2<\mu/2$。
2. 由 1.：$X=\prod_{p\in B}p<(\mu/2)^{|B|/2}$；故 $|B|=2$ 时 $X<\mu/2$，进而 $\prod_C p>2$；$|B|\ge3$ 时 $X^{1-|B|/2}<(\prod_C p)^{|B|/2}/2^{|B|/2}$，对 $X$ 又是下界。
3. $\forall p\in B$：$p<\mu/a_1$（由 H 的 $\mu/p>a_1$），故 $X<(\mu/a_1)^{|B|}=\bigl((\prod_C p)X/a_1\bigr)^{|B|}$，即
$$X^{|B|-1}>\frac{a_1^{|B|}}{\bigl(\prod_C p\bigr)^{|B|}}\qquad(\text{又是下界}).$$
4. 待证目标（$X\le a_1$ 或 $\mu\le2a_1^2$）在 (5.1)、(5.4) 与 1.–3. 下**不被**自动推出：$|B|=2$ 时 (5.4) 为 $q_1q_2<(\prod_C p)^2$、1.–2. 为 $X<\mu/2$，都不含 $X$ 与 $a_1$ 的直接比较。这正是缺口。

**缺口 5.3（最窄形式）**
> **待证**：H 成立且 $|B|\ge2$ 时 $\mu\le2a_1^2$（等价地 $\operatorname{rad}(a_1)X\le2a_1^2\prod_A p$；充分条件为 $X\le a_1$）。
> 已排除的子情形：$|B|=0$（定理 4.1 分支 1）、$|B|=1$（定理 4.1 分支 2）；$|S|\le2$（系 3.3 与定理 4.2）；$|B|=2$ 且 $\min B\le2a_1/\Pi$（系 5.6）。
> 已知的可用输入（全部已证）：$2\le p\le2a_1$（$p\in S$，引理 5.2）；$q_p\in A$ 且 $p^2q_p<\mu$；$U_p=a_{i_p}$ 满足 (5.2)；$U_p$ 两两不互素（都是项，(P1)），且公共素因子 $\notin S$（因 $\operatorname{supp}(U_p)\cap S=\{p\}$）；$a_{i_p}\ge2p$（$p\in B$，注 4.3）。

**建议路线（按可行性排序）**

1. **用交叉素数加强 (5.4)**：对 $p\ne p'\in B$，取 $r_{pp'}\in\operatorname{supp}(U_p)\cap\operatorname{supp}(U_{p'})\setminus S$（存在：(P1) 且各自 $\cap S$ 只含自身素因子）。$r_{pp'}\mid a_{i_p}$ 且 $r_{pp'}\ne p$，于是 $U_p\ge p\,q_p\,r_{pp'}$。例如 $|B|=2$ 时 (5.4) 加强为 $q_1q_2r<(\prod_C p)^2$；能否进一步利用 $r$ 与 $A\cup C$ 的关系（$r\notin S$，可为 $A$ 中素数或全新素数）是关键。
2. **对 $B$ 中的最大素 $p_2$ 单列**：由推论 5.2.1，$p_2<\frac{(\prod_C p)(p_1)}{q_{p_2}}$（$p_1=\min B$），故 $X=p_1p_2<\frac{(\prod_C p)p_1^2}{q_{p_2}}$；若再有 $p_1^2\le q_{p_2}\cdot\frac{a_1}{\prod_C p}\cdot\ldots$ 之类，即可闭合（$|B|=2$ 时为 $p_1^2q_{p_2}<(\prod_C p)a_1/\operatorname{rad}(a_1)\cdot\ldots$）。
3. **降链**：H 给 $\mu>a_1p\ (\forall p\in S)$，故引理 $\ast\ast$ 对每个 $p$ 可用，得 $\nu^{(p)}\in\mathcal M$，$p\mid\nu^{(p)}$，$\operatorname{supp}(\nu^{(p)})\cap S=\{p\}$，$\nu^{(p)}<\mu/p$。对 $\nu^{(p)}$ 再用一次（以 $p$ 为素数）可把 $\operatorname{supp}$ 逐层"剥离"，可能给出 $\mu$ 的乘性上界。
4. **强目标**：直接证 $\mu\le2a_1$（prover-mu 的 T1；数值最大 $1.4483$）。由系 3.2，$\mu\le2a_1$ 直接消灭 H，比本文目标更强，但需要新的输入（(5.1) 只给 $|B|=2$ 时的 $q_1q_2$ 型信息）。

**命题 5.4（H 下的"窗口"必要条件；$|B|=2,|C|=1$ 情形）** 设 H 成立，$|B|=2$，$C=\{c\}$，记 $B=\{p_1,p_2\}$，$p_1<p_2$，$m:=a_1/c$（整数）。则

1. $p_1\ge m$；进一步 $2p_2<c\,p_1$，特别 $c>2$（由 $p_2\ge p_1$）；
2. $q_{p_1},q_{p_2}\mid m$，故 $q_{p_1}q_{p_2}\le m$（若 $q_{p_1}\ne q_{p_2}$；否则 $q\le m$）；
3. $p_1q_{p_1}<c\,p_2$，$p_2q_{p_2}<c\,p_1$，故 $\max(2,q_{p_1})q_{p_2}<c^2$；
4. $X=p_1p_2>4c$；并且 $X\le a_1=cm\iff p_2\le \dfrac{cm}{p_1}$。

证明：

1. H 给 $\mu=c p_1p_2\ge a_1\max S=a_1p_2$，即 $c p_1\ge a_1=cm$，故 $p_1\ge m$。又 $U_{p_2}=a_{i_{p_2}}\ge2p_2$（系 4.4，$p_2\in B$）与 $U_{p_2}<\mu/p_2=c p_1$ 给 $2p_2<c p_1$。
2. 因 $q_{p_i}\in A\subseteq D_1\setminus S$ 是整除 $a_1=cm$ 的素数，而 $c\in S$ 故 $q_{p_i}\ne c$，于是 $q_{p_i}\mid m$。
3. (5.2) 给 $U_{p_i}\ge p_iq_{p_i}$ 与 $U_{p_i}<\mu/p_i=c\,p_{3-i}$；取 $i=1,2$ 得两式。第二式与 $U_{p_1}\ge2p_1$ 一起：$\max(2,q_{p_1})p_1\le U_{p_1}<c p_2$，配合 $p_2q_{p_2}<cp_1$ 得 $\max(2,q_{p_1})q_{p_2}\,p_1p_2<c^2p_1p_2$，即 $\max(2,q_{p_1})q_{p_2}<c^2$。
4. $U_c<\mu/c=p_1p_2=X$，而 $U_c\supseteq c\,r_{cp_1}r_{cp_2}$（$r_{cp_i}\in\operatorname{supp}(U_c)\cap\operatorname{supp}(U_{p_i})\setminus S$ 是互异素数 $\ge2$），故 $4c\le c\,r_{cp_1}r_{cp_2}<X$。最后一条是 $cm/p_1$ 的代数变形（$p_1>0$）。∎

**注 5.5** 命题 5.4.1 说明：H 要求 $B$ 的最小素 $\ge a_1/c$；当 $m>c$ 时立即得到 $X=p_1p_2\ge m^2>cm=a_1$，因此**若 H 成立且 $m>c$，则 $X>a_1$**（此时收口只能用 $\mu\le2a_1^2$ 而非 $X\le a_1$）。这解释了数值上"H 从未出现 + $X\le a_1$ 恒成立"两个现象为何不能直接相乘：两者对应不同的极值结构。

**系 5.6（$|B|=2$ 的一个新子情形闭环，对任意 $C$ 成立）** 设 H 成立，$|B|=2$，$B=\{p_1,p_2\}$，$p_1<p_2$，并记
$$\Pi:=\prod_{p\in C}p\ (=\operatorname{rad}(a_1)/\prod_A p),\qquad m:=a_1/\Pi .$$
（$\Pi\mid\operatorname{rad}(a_1)\mid a_1$，故 $m$ 是正整数；$\mu=\Pi\,X$、$a_1=\Pi\,m$。）若
$$p_1\le 2m=\frac{2a_1}{\Pi},$$
则 $\mu<2a_1^2$，从而该情形闭环（$\mu\le2a_1^2$ 即够，定理 2.2）。

证明：只需两点：

* 由 $\mu/p_2\notin A_\infty$、$i_{p_2}:=\mathrm{kill}(\mu/p_2)<\infty$、位置引理（H 给 $\mu/p_2>a_1$）得 $a_{i_{p_2}}<\mu/p_2=(\Pi)(X/p_2)=\Pi\,p_1$；又 $p_2\in B$ 故 $a_{i_{p_2}}\ge2p_2$（系 4.4），于是
$$2p_2<\Pi\,p_1\ \Longrightarrow\ X=p_1p_2<\frac{\Pi\,p_1^2}2 .$$
* 由 $p_1\le 2m$ 得 $X<\frac{\Pi\cdot4m^2}2=2\Pi m^2$，故
$$\mu=\Pi X<2\Pi^2m^2=2a_1^2 .\qed$$

**注 5.7（缺口的最窄形式，更新）** 由定理 4.1、4.2、系 5.6，缺口只剩
$$\text{H}\ \wedge\ \Bigl[\ \bigl(|B|=2\ \wedge\ \min B>\tfrac{2a_1}{\Pi}\bigr)\ \ \vee\ \ |B|\ge3\ \Bigr],\qquad \Pi:=\prod_{C}p .$$
其中 $p_1=\min B>2a_1/\Pi$ 意味着 $X=p_1p_2\ge p_1^2>4a_1^2/\Pi^2$（大 $X$ 情形）。**数值上第二个析取项以外的情形可能并不存在**：在 $a_1\le1200$ 的全部 103 个 $|B|=2$ 极小元中都有 $\min B\le2a_1/\Pi$（`logs/x_gap.py`，0 例外），即系 5.6 的条件在样本中恒满足；若这条（"$\min B\le2a_1/\Pi$"）能无条件证明，则 $|B|=2$ 全部闭环，缺口就回到 $|B|\ge3$（$\Rightarrow|S|\ge4\ge3$，即 task-6 的原始形式）。

**注 5.8（$\Pi=2$ 的临界性）** 若 $\Pi=2$（即 $C=\{2\}$，$2\mid a_1$）且 $\min B>a_1$，则 $X=p_1p_2>a_1\,p_2\ge a_1p_1>a_1^2$，故 $\mu=\Pi X>2a_1^2$——此时 $\mu\le2a_1^2$ 不再自动成立，必须真的排除 H（或对该结构另取实现项）。这解释了 $\Pi=2$ 在缺口中的特殊地位：$2m=a_1$，系 5.6 的条件退化为 $p_1\le a_1$。

---

## 6. 与 `13-mu-bound.md` 的交叉核对

| 13 的条目 | 本文复核 | 说明 |
|---|---|---|
| 引理 1.1（$D_1$ 饱和）、引理 1.3、引理 2.1（强化下降）、引理 3.2（H 严格化）、引理 3.3（T-构造）、引理 5.1（$B\to A$ 对应）、引理 5.3 | ✅ 正确 | 逐行复核；引理 3.3.1 的 $T_p=a_{i_p}p\ge a_1p$、$T_p<\mu$、$\operatorname{supp}(T_p)\cap S=\{p\}$、交叉素数 $\notin S$ 均成立 |
| 13 §3.4.2、§4（$s=3$ 的 H-排除） | ⚠️ 需注意 | 那里用了 $T_p<\mu/p$（从而 $\prod T_p<\mu^{s-1}$）。但 $T_p=a_{i_p}p$ 与位置引理只给 $T_p<\mu$；在 H 下 $T_p<\mu/p$ 等价于 $a_{i_p}p^2<\mu$，需要额外论证（本文 §5 改用 $U_p=a_{i_p}$，只用到 $U_p<\mu/p$，完全严格）。故 13 §4 的 $s=3$ 分支若要直接引用，建议按本文 (5.2)–(5.4) 重写；本文因此不把 $s=3$ 计入已闭环 |
| 缺口定位（H 且 $|B|\ge2$ 且 $|S|\ge4$） | ⚠️ 略窄于本文口径 | 若采用 13 的 $s\le3$ 结论，缺口为 $|B|\ge3$；按本文严格口径（只用已核实的不等式），缺口为 H $\wedge$ $|B|\ge2$（含 $|B|=2,|S|=3$ 与 $|B|\ge3$ 两支） |

**另一条可替代写法（若要用 $T_p=a_{i_p}p$ 型的量）**：把 13 §3.4.2 的连乘换成 $U_p=a_{i_p}$（本文 §5 的 (5.2)–(5.4)），所有不等式都严格；$|B|\ge2$ 时结论与 13 §5 的缺口不等式一致。

---

## 7. 数值（精确整数，非证明；脚本 `logs/x_diag.py`、`logs/x_b1.py`、`logs/h_mulist.py`）

计算方式：把序列生成到首次 $a_N>B_{\text{scan}}$，增量维护 $\min A_n$（算法与 `logs/mub_scan.py` 相同）。**精确性**：$a_N>B$ 时 $\min A_N\cap[2,B]=\mathcal M\cap[2,B]$（$\subseteq$：$m\in\min A_N$、$m\le B$ 若 $\notin A_\infty$ 则在步 $j$ 被杀，$a_j<m\le B<a_N$ 与 $m\in A_N\subseteq A_j$ 矛盾；$\supseteq$：反之取 $m\in\min A_N$ 真整除 $\mu$，$m\in\mathcal M$，矛盾）。

| 检验 | 范围 | 结果 |
|---|---|---|
| $X\le a_1$ | $a_1\le600$，$B_{\text{scan}}=8a_1$（`logs/x_diag.out`） | **0 反例**；$\max X/a_1=0.3547$（$a_1=375,\mu=399$，$B=\{7,19\}$） |
| $X\le a_1$（续） | $601\le a_1\le1600$，$B_{\text{scan}}=8a_1$（`logs/x_diag2.out`） | **0 反例**；$\max X/a_1=0.3426$（$a_1=645,\mu=663$，$B=\{13,17\}$） |
| $\mu\le2a_1^2$ | $a_1\le1600$（同上两份日志） | 0 反例 |
| $|B|$ 的分布 | $a_1\le600$ / $601..1600$ | $|B|\le2$ 共 599,100,52 / 1000,182,79 例；$|B|=3$ 有 10 例（$\ge601$ 段，如 $a_1=759,\mu=770=2\cdot5\cdot7\cdot11$，$X=70$） |
| $|B|=1$ 的分支 | $a_1\le1500$（`logs/x_b1.out`） | 259 例**全部**落在子分支 2a（$\mu/p<a_1$），且 $\max p/a_1=0.1333$（$a_1=15,\mu=10,p=2$）；0 反例于 $X\le a_1$ |
| 系 5.6 的条件 $\min B\le2a_1/\Pi$ | $a_1\le1200$ 的 103 个 $\|B\|=2$ 例（`logs/x_gap.out`） | **103/103 满足**，0 例外 |
| H（$\forall p:\mu/p\ge a_1$） | $a_1\le1200$（`logs/h_scan.py`、`logs/h_fast.out`） | 0 反例；$\max\mu/(a_1\max S)=0.5$（平凡 $a_1=2$） |
| 极值样本结构 | $a_1=375,\mu=399$ | $S=\{3,7,19\}$，$C=\{3\}$，$B=\{7,19\}$，$X=133$，$A=\{5\}$，$q_7=q_{19}=5$；$\mu/p<a_1$ 对一切 $p\in S$，故 $\neg$H |
| 极值样本结构 | $a_1=899,\mu=1302=2\cdot3\cdot7\cdot31$ | $B=\{2,3,7\}$，$X=42$，$A=\{29\}$，$C=\{31\}$；$\mu/a_1=1.4483$（全部样本最大），$\neg$H |

**观察**：所有数值样本都满足 $\neg$H 且 $X\le a_1$，最大 $\mu/(2a_1)=0.724$、$\max X/a_1=0.3547$，与"缺口需新一步"相符。$|B|\ge2$ 的极值样本（如 $a_1=899,\mu=1302=2\cdot3\cdot7\cdot31$，$B=\{2,3,7\}$）中 (5.1) 的余地很大，说明缺的不是反例。

---

## 8. 已证 / 缺口清单

**已证（严格、自足，只用 §1 引用的事实与本文引理）**

1. 引理 2.1、定理 2.2（$\mu\le2a_1^2\Rightarrow$ TCL 常数 $N=2a_1^2$）、系 2.3（$X\le a_1\Rightarrow$ 同上）、注 2.4。
2. 引理 3.1（H 的全部基本结构）、系 3.2（H $\Rightarrow\mu>2a_1$）、系 3.3（$|S|=1$）。
3. 定理 4.1（$B=\varnothing$ 时 $\mu\le a_1$；$|B|=1$ 时子分支 2a 给 $\mu<2a_1^2$、子分支 2b 给 $\mu\le a_1^2/2$，都不用 H）；
4. 定理 4.2（$|S|=2$ 时 H 不可能；$\neg$H $\Rightarrow\mu<2a_1^2$）与系 4.4（$a_{i_x}$ 的二分：$a_{i_x}=x\Rightarrow x\mid a_1$，否则 $a_{i_x}\ge2x$）；
5. 定理 5.1（H 且 $|B|\ge2$ 时的乘积约束 (5.1)）与推论 5.2；命题 5.4（H 下 $B$ 的窗口必要条件 $\min B\ge a_1/\Pi$、$2\max B<\Pi\min B$ 等）；
6. 系 5.6（H $\wedge$ $|B|=2$ $\wedge$ $\min B\le2a_1/\Pi$ $\Rightarrow$ $\mu<2a_1^2$）、注 5.7（缺口最窄形式）、注 5.8（$\Pi=2$ 的临界性）；
7. §6 对 `13-mu-bound.md` 的复核与一处写法更正。

**缺口（唯一，已收窄）**

8. 只剩 $\text{H}\wedge\bigl[(|B|=2\wedge\min B>2a_1/\Pi)\vee|B|\ge3\bigr]$（$\Pi=\prod_C p$；系 5.6 把 $|B|=2,\min B\le2a_1/\Pi$ 闭环）。该情形下需证 $\mu\le2a_1^2$（充分条件 $X\le a_1$）。缺口处可用工具：定理 5.1 的 (5.1)、命题 5.4 的窗口必要条件、系 4.4 的 $a_{i_x}\ge2x$、交叉素数 $r_{xy}$。**已闭环子情形**：$|S|\le1$（系 3.3）、$B=\varnothing$、$|B|=1$（定理 4.1）、$|S|=2$（定理 4.2）、$|B|=2\wedge\min B\le2a_1/\Pi$（系 5.6）。数值上第一个析取项（$|B|=2$ 且 $\min B>2a_1/\Pi$）在 $a_1\le1200$ 的 103 个 $|B|=2$ 样本中一次未出现；若"$\min B\le2a_1/\Pi$ 恒成立"被证，则只需处理 $|B|\ge3$（$\Rightarrow|S|\ge4$，即 task-6 的原始缺口）。若另确认 13 §4 的 $s\le3$，结论相同。
