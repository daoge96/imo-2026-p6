# 极小元上界补强：$\mu\le 2a_1$ / $\mu\le 2a_1^2$（大部分情形闭环，缺口已收缩到 $|B|\ge2$）

> 作者：prover-mu（task-5）。依赖：`30-final-proof.md`（Lead 定稿）§1–§5 的记号与已证引理（本文 §1 逐条自核后引用）。
> 结论口径（先看这里）：
> - **已完全证明**（假设 H 在这些情形下不可能，于是目标达成）：
>   (i) $|\operatorname{supp}(\mu)|\le3$（定理 4.1）；(ii) $S\subseteq D_1$；(iii) $|B|=1$，其中 $B=S\setminus D_1$（引理 5.3）；(iv) $|B|=2$ 且 $a_1\le64$（§5 末注）。
>   在 (i)–(iv) 中都有 $\exists p\in\operatorname{supp}(\mu):\mu/p<a_1$，从而 $\mu<2a_1^2$ 且实现项 $t<2a_1^2$，即 TCL 常数 $N=2a_1^2$ 在这些情形成立（§6）。
> - **唯一缺口**：排除 H 且 $|B|\ge2$ 且 $|S|\ge4$（最窄形式：$|B|\ge3$）。缺口处的全部已知推论与可行定量形式见 §5【缺口 5.2】，数值证据见 §7。
> - 记号 H 的定义见 §3：$H:\iff \forall p\in\operatorname{supp}(\mu):\ \mu/p\ge a_1$。**¬H ⟹ 目标达成**（§6），故全部工作量就是排除 H。
> - 额外副产品（已证）：假设 H 成立时 $\mu>2a_1$（引理 3.2），特别 H 与「$\mu\le2a_1$」不能同时成立；此外 H 时 $|B|=1\Rightarrow\mu<a_1^{3/2}/\sqrt2$、$|B|=2\Rightarrow\mu<a_1^3/32$。
> - 注：任务书里的 (T2)「$\mu\le2\operatorname{rad}(a_1)$」**是假的**（$a_1=175,\mu=195$，$\operatorname{rad}=35$；另有 $a_1=375,\mu=399$）；(T3) 第二式 $\mu/p_{\max}\le a_1$ 与 (T1) 都仍开放，本文的 ¬H 路线蕴含 (T3) 第二式（取到 $p$ 后 $\mu/p_{\max}\le\mu/p<a_1$）。

---

## 1. 记号与引用的已证工具（逐条自核）

固定整数 $a_1\ge2$；序列按题设定义（每项 $>1$，$a_{n+1}$ 是 $>a_n$ 且与 $a_1,\dots,a_n$ 全不互素的最小正整数）。记
$$\operatorname{supp}(k)=\{p\ \text{素}:p\mid k\},\quad D_n=\operatorname{supp}(a_n),\quad P_n=\bigcup_{i\le n}D_i,$$
$$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \forall i\le n\},\qquad A_\infty=\bigcap_{n\ge1}A_n,\qquad \mathrm{kill}(k)=\min\{i:\gcd(k,a_i)=1\}.$$
有限素集 $S$ 是 $\mathcal D_n$ 的**横截集**，指 $S\cap D_i\ne\varnothing\ (\forall i\le n)$；于是 $k\in A_n\iff\operatorname{supp}(k)$ 是横截集。$\mu\ge2$ 是**极小元**，指 $\mu\in A_\infty$ 且无真因子 $\nu\in A_\infty$（$2\le\nu<\mu$）；$\mathcal M$ 为全体极小元；**项** 指某个 $a_t$。

以下事实在 `30-final-proof.md`（及 `01-reduction.md`）中已证，本文直接引用；括号内为自核位置：

* **(P1)** $\gcd(a_i,a_j)>1\ (i\ne j)$；每个 $D_j$ 是整个族的横截集。（30 §2 (P1)）
* **(P2)** 每个 $a_j\in A_\infty$；$a_j\ge2$ 时 $\operatorname{rad}(a_j)\in A_\infty$。（30 §2 (P2)）
* **(P3)** $A_{n+1}\subseteq A_n$。（30 §2 (P3)）
* **(P4)** $a_{n+1}=\min\bigl(A_n\cap(a_n,\infty)\bigr)=\min\bigl(A_\infty\cap(a_n,\infty)\bigr)$。（30 §2 (P4)）
* **(P5)** $(a_n)$ 恰是 $A_\infty\cap[a_1,\infty)$ 的严格递增枚举；特别地 $k\ge a_1$ 是项 $\iff k\in A_\infty$。（30 §2 (P5)）
* **(K)** $k\in A_N\iff \mathrm{kill}(k)>N$；$k\in A_\infty\iff\mathrm{kill}(k)=\infty$。（30 §2 (K)）
* **(M)** $A_\infty$ 对取倍数、对乘法封闭。（30 §2 (M)）
* **引理 2.2**（极小元覆盖）每个 $k\in A_\infty$ 被某 $\mu\in\mathcal M$ 整除；每个 $\mu\in\mathcal M$ 无平方因子。（30 §2 引理 2.2）
* **引理 3.1**（位置引理）$k\ge a_1$，$\mathrm{kill}(k)=i<\infty$ $\Rightarrow$ $a_i<k$。（30 §3 引理 3.1）
* **引理 4.1**（私有指标）$\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)=:T$ $\Rightarrow$ $\exists i\ge1:D_i\cap T=\{p\}$。（30 §4 引理 4.1）
* **引理 5.1**（下降）$\nu\in\mathcal M$，$\nu>2a_1$，$p\in\operatorname{supp}(\nu)$ $\Rightarrow$ $\exists\nu'\in\mathcal M$：$p\mid\nu'$，$\operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\}$，$\nu'<\nu/p$。（30 §5 引理 5.1）
* **引理 5.2**（素因子界）$\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$ $\Rightarrow$ $p\le2a_1$。等价地 $\mathcal M\subseteq\{k\ge2:\operatorname{supp}(k)\subseteq\{p:p\le2a_1\}\}$。（30 §5 引理 5.2；§6 定理 6.1）

以下三条是本文**新的、完全证明的**简单事实，后面反复使用。

**引理 1.1（$D_1$ 饱和引理）** 设 $\mu\in\mathcal M$，$S=\operatorname{supp}(\mu)$。则
$$D_1\subseteq S\ \Longrightarrow\ S=D_1 .$$
特别地，若 $S\setminus D_1\ne\varnothing$ 则 $D_1\setminus S\ne\varnothing$。

证明：设 $B:=S\setminus D_1\ne\varnothing$，取 $p\in B$。由引理 4.1 取 $i$ 使 $D_i\cap S=\{p\}$。由 (P1) $D_i\cap D_1\ne\varnothing$，取素数 $\rho\in D_i\cap D_1$。若 $D_1\subseteq S$，则 $\rho\in S$，于是 $\rho\in D_i\cap S=\{p\}$，即 $\rho=p\in D_1$，与 $p\notin D_1$ 矛盾。故 $D_1\not\subseteq S$；取逆否即得。若 $B\ne\varnothing$ 则 $D_1\not\subseteq S$ 而 $D_1\cap S\ne\varnothing$（$S$ 横截），故 $D_1\setminus S\ne\varnothing$。∎

**引理 1.2（$S\cap D_1\ne\varnothing$）** 每个 $\mu\in\mathcal M$ 满足 $S\cap D_1\ne\varnothing$，且 $\exists q\in S\cap D_1$：$q\le a_1$（因 $q\mid a_1$）。

证明：$S$ 是横截集（$\mu\in A_\infty$），取 $i=1$：$S\cap D_1\ne\varnothing$；再取 $q\in S\cap D_1$，则 $q\mid a_1$，故 $q\le a_1$。∎

**引理 1.3（$\min\mathcal M\le a_1$）** 存在 $\mu_0\in\mathcal M$ 使 $\mu_0\le a_1$。

证明：$\operatorname{rad}(a_1)\in A_\infty$（(P2)），由引理 2.2 取 $\mu_0\in\mathcal M$，$\mu_0\mid\operatorname{rad}(a_1)$，故 $\mu_0\le\operatorname{rad}(a_1)\le a_1$。∎

---

## 2. 强化下降引理：阈值 $2a_1$ 可降为 $a_1p$

引理 5.1 的证明只用到「$\nu/p\ge a_1$ 以便用位置引理」。把假设从 $\nu>2a_1$ 换成 $\nu>a_1p$ 即可（因为 $\nu>a_1p\Rightarrow\nu/p>a_1$）；这一强化是后面全部论证的引擎，且本身严格。

**引理 2.1（强化下降）** 设 $\nu\in\mathcal M$，$p\in\operatorname{supp}(\nu)=:T$，且
$$\nu>a_1p .$$
则存在 $\nu'\in\mathcal M$ 使
$$p\in\operatorname{supp}(\nu'),\qquad \operatorname{supp}(\nu')\cap T=\{p\},\qquad \nu'<\nu/p .$$

证明：逐步复核引理 5.1。

1. $\nu>a_1p\ge a_1$，由 (P5) $\nu$ 是项：$\nu=a_j$（某 $j\ge1$），且 $T=D_j$ 是横截集。
2. $\nu/p\ge2$：否则 $\nu=p$，$T=\{p\}$ 横截 $\Rightarrow p\mid a_i\ (\forall i)\Rightarrow p\mid a_1\Rightarrow p\le a_1$，而 $\nu=p>a_1p$ 给出 $p>a_1p\ge2p>p$，矛盾。故 $\nu/p\ge2$。
3. $\nu/p$ 是 $\nu$ 的真因子、$\ge2$，由极小性 $\nu/p\notin A_\infty$；由 (K) 令 $i:=\mathrm{kill}(\nu/p)<\infty$。
4. 位置引理（引理 3.1）条件成立：$k:=\nu/p>a_1\ge a_1$，$\mathrm{kill}(k)=i<\infty$。于是
$$a_i<\nu/p . \tag{2.1}$$
5. $\gcd(\nu/p,a_i)=1\Rightarrow\operatorname{supp}(\nu/p)\cap D_i=\varnothing$。而 $\operatorname{supp}(\nu/p)=T\setminus\{p\}$，故 $D_i\cap T\subseteq\{p\}$；又 $T$ 横截，$D_i\cap T\ne\varnothing$，于是
$$D_i\cap T=\{p\}. \tag{2.2}$$
6. 由 (2.1)：$a_i<\nu/p<\nu=a_j$，项严格递增 $\Rightarrow i<j$。由 (P2)，$a_i\in A_\infty$ 且 $R:=\operatorname{rad}(a_i)\in A_\infty$，$R\ge2$。
7. 取 $\nu'$ 为 $\mathcal F:=\{\nu''\ge2:\nu''\mid R,\ \nu''\in A_\infty\}$ 中在整除意义下极小者（$\mathcal F\ne\varnothing\ni R$，取定一个）。则 $\nu'\in\mathcal M$：若 $\nu''\mid\nu'$、$2\le\nu''<\nu'$、$\nu''\in A_\infty$，则 $\nu''\mid R$ 使 $\nu''\in\mathcal F$，与 $\nu'$ 极小矛盾。
8. $\operatorname{supp}(\nu')\subseteq\operatorname{supp}(R)=D_i$，结合 (2.2)：$\operatorname{supp}(\nu')\cap T\subseteq\{p\}$；又 $\nu'\in A_\infty$ 而 $T=D_j$ 横截 $\Rightarrow\operatorname{supp}(\nu')\cap T\ne\varnothing$，故 $=\{p\}$，特别 $p\in\operatorname{supp}(\nu')$。
9. $\nu'\le R\le a_i\overset{(2.1)}{<}\nu/p$。∎

**注 2.2（与引理 5.1 的关系）** 引理 2.1 与 引理 5.1 的证明逐字相同（都用位置引理 3.1），只有「保证 $k=\nu/p\ge a_1$」的方式不同：引理 5.1 用 $\nu>2a_1\Rightarrow\nu/p\ge\nu/2>a_1$，引理 2.1 用 $\nu>a_1p\Rightarrow\nu/p>a_1$。两条互不包含（$a_1p$ 与 $2a_1$ 无固定大小关系），本文两条都引用。

**系 2.3（链的终止形式）** 设 $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$。则存在链 $\nu_0=\mu,\nu_1,\dots,\nu_k\in\mathcal M$ 与 $\mathcal M$ 中元素如此使得
$$\nu_{r+1}<\nu_r/p,\quad p\in\operatorname{supp}(\nu_{r+1}),\quad \operatorname{supp}(\nu_{r+1})\cap\operatorname{supp}(\nu_r)=\{p\}\qquad(0\le r<k),$$
且 $\nu_k\le a_1p$。

证明：只要 $\nu_r>a_1p$ 就用引理 2.1 走一步；$(\nu_r)$ 是严格递减正整数列（$\nu_{r+1}<\nu_r/p\le\nu_r/2$），必在有限步 $k$ 停机，停机即 $\nu_k\le a_1p$。∎

（注：把停机条件换成「$\nu_r>2a_1$」即得 引理 5.2 的 $p\le2a_1$；本文仍以 引理 5.2 的形式引用 $p\le2a_1$。）

---

## 3. 假设 H、T-构造与交叉素数

**定义 3.1（关键假设 H）** 设 $\mu\in\mathcal M$，$S=\operatorname{supp}(\mu)$。称 H 成立，若
$$H:\qquad \forall p\in S:\ \frac{\mu}{p}\ \ge\ a_1 .$$
（因 $p\mapsto\mu/p$ 随 $p$ 递减，$H\iff \mu/\min S\ge a_1$。）

**引理 3.2（H 的严格化）** 若 H 成立，则 $\forall p\in S$ 都有 $\mu/p>a_1$，且 $\mu>2a_1$；故引理 2.1、引理 3.1 对一切 $p\in S$、$k=\mu/p$ 可用。

证明：若 $\mu/p\ge a_1$，则 $i:=\mathrm{kill}(\mu/p)<\infty$：事实上 $\mu/p\ge a_1\ge2$ 且 $\mu/p$ 是 $\mu$ 的真因子（$\mu$ 无平方因子），由极小性 $\mu/p\notin A_\infty$，再用 (K)。于是位置引理可用（$k=\mu/p\ge a_1$），得 $a_i<\mu/p$，而 $a_i\ge a_1$（项）——故若 $\mu/p=a_1$ 则 $a_i<a_1\le a_i$，矛盾。故 $\mu/p>a_1$。取 $p=\max S\ge2$ 得 $\mu>a_1p\ge2a_1$。∎

**引理 3.3（T-构造）** 设 H 成立，$\mu\in\mathcal M$，$S=\operatorname{supp}(\mu)$。对每个 $p\in S$ 令 $i_p:=\mathrm{kill}(\mu/p)$、$T_p:=a_{i_p}\cdot p$。则

1. $i_p<\infty$，$\operatorname{supp}(T_p)=D_{i_p}$，$D_{i_p}\cap S=\{p\}$，$T_p\ge a_1p$，$T_p<\mu$；
2. $T_p\in A_\infty$，且 $T_p$ 是**项**；
3. 对 $p\ne q\in S$：$T_p\ne T_q$，$\gcd(T_p,T_q)>1$，且每个公共素因子 $\notin S$。

证明：

* $\mu/p\notin A_\infty$（$\mu/p$ 是 $\mu$ 的真因子、$\ge2$，用极小性；$\mu/p\ge2$ 见引理 3.2 的 $\mu>2a_1,p\le\mu$），故 $i_p<\infty$（(K)）。
* $\gcd(\mu/p,a_{i_p})=1\Rightarrow D_{i_p}\cap(S\setminus\{p\})=\varnothing$；又 $D_{i_p}$ 横截 $\Rightarrow D_{i_p}\cap S\ne\varnothing$，故 $D_{i_p}\cap S=\{p\}$，特别 $p\in D_{i_p}$，于是 $\operatorname{supp}(T_p)=\operatorname{supp}(a_{i_p})\cup\{p\}=D_{i_p}$。
* $T_p\ge a_1p$（$a_{i_p}\ge a_1$，项）；$T_p<p\cdot(\mu/p)=\mu$（引理 3.1 给 $a_{i_p}<\mu/p$，条件由引理 3.2 保证）。这证明了 1。
* $T_p$ 是 $a_{i_p}$ 的倍数 $\Rightarrow T_p\in A_\infty$（(M)）；又 $T_p\ge a_1p\ge a_1$，由 (P5) $T_p$ 是项。这证明了 2。
* $T_p\ne T_q$：$\operatorname{supp}(T_p)\cap S=\{p\}\ne\{q\}=\operatorname{supp}(T_q)\cap S$。两式都是项，由 (P1) $\gcd(T_p,T_q)>1$；公共素因子若 $\in S$ 则同时属于 $\{p\}$ 与 $\{q\}$，不可能，故 $\notin S$。这证明了 3。∎

**引理 3.4（H 下的乘积界）** 设 H 成立，$s:=|S|$，并记 $R_p$ 为 $\{r_{pq}:q\in S\setminus\{p\}\}$ 中所有**不同**素因子之积（$r_{pq}$ 为引理 3.3.3 给出的公共素因子）。则

1. $\operatorname{supp}(T_p)\cap S=\{p\}$ 且 $r_{pq}\ne p$，故 $r_{pq}\mid a_{i_p}$，于是 $T_p\ge a_1p\,R_p$；
2. $\displaystyle\prod_{p\in S}T_p<\prod_{p\in S}\frac{\mu}{p}=\mu^{s-1}$；
3. 因此 $\displaystyle a_1^s\prod_{p\in S}R_p<\mu^{s-2}$；特别（$R_p\ge2$，$s\ge2$ 时）$2^s a_1^s<\mu^{s-2}$。

证明：1. 由引理 3.3.1 $T_p=a_{i_p}p$、$p\in D_{i_p}$；$r_{pq}\in\operatorname{supp}(T_p)=D_{i_p}$ 且 $r_{pq}\notin S\ni p$，故 $r_{pq}\ne p$，于是 $r_{pq}\mid a_{i_p}$；不同的 $r_{pq}$ 之积 $R_p\mid a_{i_p}$，故 $a_{i_p}\ge R_p$，从而 $T_p\ge a_1pR_p$。
2. 由引理 3.3.1 $T_p<\mu/p$，连乘并用 $\prod_{p\in S}p=\mu$。
3. 由 1.、2.：$a_1^s\mu\prod_pR_p\le\prod_pT_p<\mu^{s-1}$，约去 $\mu$ 即得；$R_p\ne\varnothing$（$s\ge2$）给出 $R_p\ge2$。∎

---

## 4. $|S|\le3$：H 不可能

**定理 4.1** 设 $\mu\in\mathcal M$，$s=|\operatorname{supp}(\mu)|\le3$。则 $\exists p\in\operatorname{supp}(\mu)$ 使 $\mu/p<a_1$；从而 $\mu<a_1p\le2a_1^2$（用引理 5.2：$p\le2a_1$）。

证明：反设 H 成立。由引理 3.2，$\mu>2a_1$，引理 2.1/3.1/3.3 全部可用。

* $s=1$：$S=\{p\}$，$\mu=p$，则 $\mu/p=1<a_1$（$a_1\ge2$），与 H 矛盾。✔
* $s=2$：$S=\{p,q\}$。由引理 3.3.1，$T_p<\mu/p=q$，$T_q<\mu/q=p$，且 $T_p\ge a_1p,\ T_q\ge a_1q$。连乘：
$$a_1^2pq\le T_pT_q<\frac{\mu}{p}\cdot\frac{\mu}{q}=\frac{\mu^2}{pq}=\mu ,$$
即 $a_1^2\mu<\mu$，亦即 $a_1^2<1$，与 $a_1\ge2$ 矛盾。✔
* $s=3$：记 $S=\{p,q,r\}$。由引理 3.3.3，$r_{pq},r_{qr},r_{rp}\notin S$ 均为素数。对每个 $x\in S$，设 $y,z$ 是 $S\setminus\{x\}$ 的两个元素；$r_{xy},r_{xz}$ 都是 $\notin S$ 的素数、且都整除 $a_{i_x}$（引理 3.4.1），故
$$T_x=a_{i_x}x\ \ge\ a_1x\max(r_{xy},r_{xz})\ \ge\ a_1x\sqrt{r_{xy}r_{xz}}$$
（若 $r_{xy}=r_{xz}=r$ 则 $a_{i_x}\ge r=\sqrt{r^2}$；若不同则 $a_{i_x}\ge r_{xy}r_{xz}\ge\sqrt{r_{xy}r_{xz}}$）。三式连乘：
$$\prod_{x\in S}T_x\ \ge\ a_1^3(pqr)\sqrt{(r_{pq}r_{pr})(r_{pq}r_{qr})(r_{pr}r_{qr})}\ =\ a_1^3\mu\, R,$$
其中 $R:=r_{pq}r_{pr}r_{qr}$（这是三个整数之积，允许其中两个值相同；无论同异，$R\ge2^3=8$）。另一方面由引理 3.4.2：
$$\prod_{x\in S}T_x<\mu^{2}.$$
于是 $a_1^3\mu R<\mu^2$，即 $\mu>a_1^3R\ge8a_1^3$。但由引理 5.2 每个素因子 $\le2a_1$，故 $\mu=pqr\le(2a_1)^3=8a_1^3$。矛盾。✔
（$\sqrt{r_{xy}r_{xz}}$ 那一步的正当性：$r_{xy},r_{xz}$ 都是整除 $a_{i_x}$ 的素数；若它们不同则 $a_{i_x}\ge r_{xy}r_{xz}\ge\sqrt{r_{xy}r_{xz}}$；若相同 $=r$ 则 $a_{i_x}\ge r=\sqrt{r^2}$。)\qed

**系 4.2** 若 $|\operatorname{supp}(\mu)|\le3$ 则 $\mu\le2a_1^2$；更强地 $\mu<a_1p\le2a_1^2$，其中 $p$ 为定理 4.1 给出的素数。特别地 TCL 可用常数 $N=2a_1^2$（接口见 §6）对一切 $|\operatorname{supp}(\mu)|\le3$ 的极小元成立。

**注 4.3** $s=2$ 的论证其实用不到交叉素数：只用 $T_p<\mu/p$ 与 $T_p\ge a_1p$。$s=3$ 必须用交叉素数（$\prod R_p$ 那一环），这正是 $s\ge4$ 时失效的地方：$s\ge4$ 时 $\prod_pR_p\ge2^s$ 只给出 $\mu^{s-2}>2^sa_1^s$，与 $\mu\le(2a_1)^s$ 相容。

---

## 5. $|S|\ge4$：已得到的全部推论（【缺口】在此）

设 H 成立，$s=|S|\ge4$。由 §3 与引理 5.2 得下列**已证**约束：

1. $\forall p\in S$：$\dfrac{\mu}{p}>a_1$（引理 3.2），且 $T_p\in[a_1p,\mu/p)$ 是项、$\operatorname{supp}(T_p)\cap S=\{p\}$（引理 3.3）；
2. $\forall p\in S$：$a_1p^2<\mu$，即 $p<\sqrt{\mu/a_1}$（由引理 3.3.1 的 $a_1p\le T_p<\mu/p$ 立即得到——注意 $T_p<\mu/p$ 而非 $<\mu$）；
3. $\forall p\in S$：$p\le2a_1$（引理 5.2）；
4. $a_1^s<\mu^{s-2}$；更强地 $2^sa_1^s<\mu^{s-2}$（引理 3.4.3）；于是 $\mu>a_1^{s/(s-2)}$（$s=4$ 时即 $\mu>a_1^2$；$s\ge5$ 时弱于 $a_1^2$），且 $s=4$ 时由 $2^4a_1^4<\mu^2$ 得 $\mu>4a_1^2$；
5. $p\ne q\Rightarrow\exists r_{pq}\notin S$，$r_{pq}\mid T_p,T_q$（引理 3.3.3）；每个 $p\in B:=S\setminus D_1$ 的私有见证 $D_{i_p}$ 还含 $D_1\setminus S$ 中的素数（引理 1.1 + (P1)，见下）；
6. $\mu\le(2a_1)^s$（引理 5.2）；
7. $2\in S$ 的样本中全部极值点都出现；H 蕴含 $\mu\ge2a_1$，而所有数值样本 $\mu\le1.45a_1$，故若 H 成立必须 $\mu\in[2a_1,(2a_1)^s]$——与所有观测严重不符（§7）。

**引理 5.1（$B\to D_1\setminus S$ 的对应，已证）** 设 $\mu\in\mathcal M$，$S=\operatorname{supp}(\mu)$，$p\in B:=S\setminus D_1$。则 $D_{i_p}\cap D_1\ne\varnothing$（(P1)），且 $D_{i_p}\cap D_1\subseteq D_1\setminus S$；故每个 $p\in B$ 都配到一个素数 $q_p\in D_1\setminus S$ 使 $q_p\mid a_{i_p}$，于是 $a_{i_p}\ge p\,q_p$，即 $T_p\ge p^2q_p$（对比引理 1.1）。

证明：由引理 4.1 取 $i_p$（私有指标），$D_{i_p}\cap S=\{p\}$。设 $\rho\in D_{i_p}\cap D_1$（(P1) 保证非空）。若 $\rho\in S$ 则 $\rho=p\notin D_1$，矛盾（$\rho\in D_1$）；故 $\rho\notin S$，即 $\rho\in D_1\setminus S$。取 $q_p:=\rho$。∎

**引理 5.3（$|B|=1$ 与 $B=\varnothing$ 的情形已闭环）** 设 $\mu\in\mathcal M$，$S=\operatorname{supp}(\mu)$，$B=S\setminus D_1$，$C=S\cap D_1$。

1. 若 $B=\varnothing$（即 $S\subseteq D_1$，由引理 1.1 等价于 $S=D_1$）：$\mu=\operatorname{rad}(a_1)\le a_1$，与 H 的 $\mu>2a_1$ 矛盾。特别地 **H 成立 $\Rightarrow B\ne\varnothing$**，从而由引理 1.1 $A:=D_1\setminus S\ne\varnothing$。
2. 若 H 成立且 $|B|=1$：$\mu<a_1^{3/2}/\sqrt2\le2a_1^2$，且实现项可取 $t\le\mu-a_1+1<2a_1^2$。

证明：1. $S\subseteq D_1$ 时 $\mu=\prod_{p\in S}p\le\operatorname{rad}(a_1)\le a_1$；而 H 由引理 3.2 给 $\mu>2a_1$。
2. 记 $B=\{p\}$，$X=p$。由 1. 取 $q_p\in A$（引理 5.1），$q_p\ge2$。由引理 5.1 $T_p\ge p^2q_p$，又引理 3.3.1 $T_p<\mu/p=\prod_{C}p$（因 $S=B\sqcup C$，$\mu/p=\prod_{C}p$）。故
$$p^2q_p<\prod_{C}p\le\operatorname{rad}(a_1)\le a_1\ \Longrightarrow\ p<\sqrt{a_1/q_p}\le\sqrt{a_1/2},$$
于是 $\mu=p\prod_Cp<\sqrt{a_1/2}\cdot a_1=a_1^{3/2}/\sqrt2$，而 $a_1^{3/2}/\sqrt2\le2a_1^2\iff1\le2\sqrt{2a_1}$（$a_1\ge2$ 成立）。最后 $t\le\mu-a_1+1<a_1^{3/2}+1\le2a_1^2-a_1$ 对 $a_1\ge2$ 可直接核对（$a_1=2$：$3.83<6$；$a_1\ge3$ 时 $a_1^{3/2}\le a_1^2$）。∎

**【缺口 5.2】**
> 缺口（唯一，已收缩到最窄形式）：排除 H 且 $|B|\ge2$ 且 $s\ge4$ 的情形（$B:=S\setminus D_1$）；等价地，只需在这个情形下证明 $\mu\le2a_1^2$（或导出矛盾）。
> 之所以只需排除 H：H 的否定恰给出 $\exists p\in S:\mu/p<a_1$，由 §6 定理 6.1 立刻得到实现项 $t<2a_1^2$。反之若 H 成立，§5 的推论（已证）给出 $s=4$ 时 $\mu>4a_1^2$、一般 $s\ge4$ 时 $\mu>2^{s/(s-2)}a_1^{s/(s-2)}$，故 H 成立时不能自动得到 $\mu\le2a_1^2$，必须真的排除 H（或在 H 下另找满足常数的实现方式）。
> 已经排除的子情形：$s\le3$（定理 4.1，两种计数在 $s=3$ 时相撞：$8a_1^3<\mu\le(2a_1)^3$）；$|B|=1$（引理 5.3：H 时 $\mu<a_1^{3/2}/\sqrt2\le2a_1^2$）；$B=\varnothing$（则 $S\subseteq D_1$，$\mu\le\operatorname{rad}(a_1)\le a_1$，与 H 的 $\mu>2a_1$ 矛盾）。
> 剩下的硬核（$|B|\ge2$，$s\ge4$，数值极值点正落在这里：$a_1=899,\mu=1302$ 有 $B=\{2,3,7\}$，$|B|=3$）：H 时 $T_p<\mu/p$ 且 $T_p\ge p^2q_p$（$q_p\in A:=D_1\setminus S$，引理 5.1）给出 $p^3q_p<\mu$；又 $\mu=\operatorname{rad}(a_1)X/\prod_A$（恒等式，$X=\prod_Bp$，$A\sqcup C=D_1$），故连乘得
> $$X^{3-|B|}\prod_{p\in B}q_p\cdot\Bigl(\prod_{A}p\Bigr)^{|B|}<\operatorname{rad}(a_1)^{|B|}\le a_1^{|B|}.$$
> 目标 $X\le2a_1\prod_A$（它等价于 $\mu\le2a_1^2$ 的充分形式 $\mu\le a_1X/\prod_A\le2a_1^2$）。在 $|B|=2$ 时上式即 $Xq_1q_2\prod_A^2<a_1^2$，配合 $q_1q_2\prod_A^3\ge2^5$ 可得 $\mu<a_1^3/32$，从而 $|B|=2$ 且 $a_1\le64$ 时闭环；$|B|\ge3$ 时上式对 $X$ 只有下界信息，需额外输入（这是所缺的一步）。

---

## 6. 与 TCL 常数 $N=2a_1^2$ 的接口

**定理 6.1（¬H ⟹ 常数 $2a_1^2$）** 设对每个 $\mu\in\mathcal M$，或者（a）$\exists p=p(\mu)\in\operatorname{supp}(\mu)$ 使 $\mu/p<a_1$，或者（b）$\mu<2a_1^2-a_1+1$。（由定理 4.1 与引理 5.3：$|\operatorname{supp}\mu|\le3$ 及 $S\subseteq D_1$ 时 (a) 成立；$H$ 且 $|B|=1$ 时 (a) 不必成立但 (b) 由引理 5.3 成立。）则对每个 $\mu\in\mathcal M$ 都存在项 $a_t$ 使
$$D_t=\operatorname{supp}(\mu),\qquad t<2a_1^2 .$$

证明：取这样的 $p$，令 $j:=\min\{s\ge0:\mu p^{s}\ge a_1\}$、$k:=\mu p^{j}$。则 $\operatorname{supp}(k)=\operatorname{supp}(\mu)$（$p$ 已在支撑中），$k\in A_\infty$（(M)：$k$ 是 $\mu$ 的倍数），$k\ge a_1$，故由 (P5) $k=a_t$ 是项且 $D_t=\operatorname{supp}(k)=\operatorname{supp}(\mu)$。项严格递增给出 $a_t\ge a_1+(t-1)$，故 $t\le k-a_1+1$。

* 若 $j\ge1$：由 $j$ 的极小性 $\mu p^{j-1}<a_1$，故 $k=\mu p^{j-1}\cdot p<a_1p\le2a_1^2$（引理 5.2），于是 $t\le k-a_1+1<2a_1^2$。
* 若 $j=0$：$k=\mu\ge a_1$，故 $t\le\mu-a_1+1$。在情形 (a) 由 $\mu<a_1p\le2a_1^2$（引理 5.2）得 $\mu\le2a_1^2$；在情形 (b) 直接有 $\mu<2a_1^2-a_1+1$。两种情形都给出 $t\le\mu-a_1+1<2a_1^2$（$a_1\ge2$）。∎

**系 6.2（把 30-final-proof 的 $N$ 改回 $2a_1^2$ 的做法）** 在 `30-final-proof.md` 定理 6.3/注的显式常数论证中，把「实现引理」中对每个 $\mu\in\mathcal M$ 造项的那一步替换为定理 6.1 的构造（或直接把定理 6.1 当作新的实现引理）：对 $m>N:=2a_1^2$ 取极小元 $\mu\mid\operatorname{rad}(a_m)$（引理 2.2）、取定理 6.1 的项 $a_t$，则 $D_t=\operatorname{supp}(\mu)\subseteq\operatorname{supp}(\operatorname{rad}(a_m))=D_m$ 且 $t<2a_1^2=N<m$，即 TCL 成立。若只有 §4 的结论（$|\operatorname{supp}\mu|\le3$），则在 $|\operatorname{supp}\mu|\le3$ 的极小元上可直接还原常数；对 $|\operatorname{supp}\mu|\ge4$ 的极小元仍可用旧的 $\max\{2a_1^2,\prod_{p\le2a_1}p\}$ 混合常数，即 $N=\max\{2a_1^2,\prod_{p\le2a_1}p\}$ 中真正需要的部分被压缩到 $|\operatorname{supp}|\ge4$ 的极小元。

**注 6.3** ¬H 显然蕴含 (T3) 第二式对偶的形式：$\mu/p_{\max}<a_1$（因 $\mu/p_{\max}\le\mu/p$）。

---

## 7. 数值证据（精确整数，脚本 `logs/mub_*.py`）

计算方式：把序列生成到首次 $a_N>B$（$B=8a_1$ 或 $10a_1$），增量维护 $\min A_n$。事实：$a_N>B$ 时 $\min A_N\cap[2,B]$ 恰等于 $\mathcal M\cap[2,B]$（$\subseteq$：$m\in\min A_N$、$m\le B$ 必 $\in A_\infty$，否则在步 $j$ 被杀而 $a_j<m\le B<a_N$，与 $m\in A_N\subseteq A_j$ 矛盾；$\supseteq$：$\mu\in\mathcal M$、$\mu\le B$ 若在 $A_N$ 中不极小则被某 $m\in\min A_N$ 真整除，而 $m\in\mathcal M$，矛盾）。故数据是精确的。

| 检验项 | 范围 | 结果 |
|---|---|---|
| $\mu\le2a_1$ (T1) | $a_1\le3000$ | 0 反例；$\max\mu/a_1=1.4483$（$a_1=899,\mu=1302=2\cdot3\cdot7\cdot31$） |
| $\mu/p\le a_1,\ \forall p\mid\mu$（即 M1，等价 $\mu\le a_1\min S$） | $a_1\le2500$ 与 3000 | 0 反例 |
| $\mu/p_{\max}\le a_1$ (T3b) | $a_1\le1500$ | 0 反例 |
| $\mu\le2a_1^2$ | $a_1\le3000$ | 0 反例 |
| $\mathcal M$ 两两不互素 | $a_1\le3000$ | 0 反例 |
| $\max \mu/(a_1\min S)$ | $a_1\le1200$ | $0.7241$（$a_1=899,\mu=1302$，$|S|=4$）；按 $|S|$ 分：$|S|=1:0.5$、$2:0.333$、$3:0.647$、$4:0.724$ |
| T2 $\mu\le2\operatorname{rad}(a_1)$ | $a_1\le1500$ | **假**：20 个反例，如 $a_1=375,\mu=399$（$\operatorname{rad}=15$）、$a_1=175,\mu=195$（$\operatorname{rad}=35$） |

**观察**：H（$\mu/p\ge a_1$）在所有样本中都不成立，且离成立还有至少 $1/0.724=1.38$ 倍余量；极值点几乎全为 $2\in S$ 者。这支持「H 其实不可能」这一猜想，也说明 §5 的缺口是真的缺一步而非缺一个反例。

---

## 8. 已证 / 缺口清单

**已证（严格、自足，仅用 §1 引用的 (P1)–(P5)、(K)、(M)、引理 2.2/3.1/4.1/5.1/5.2 与本文 §1–§3 新引理）**

1. 引理 1.1（$D_1\subseteq S\Rightarrow S=D_1$）、引理 1.2、引理 1.3。
2. 引理 2.1（强化下降：阈值 $a_1p$）、系 2.3（链终止于 $\le a_1p$）。
3. 引理 3.2（H 严格化）、引理 3.3（T-构造）、引理 3.4（乘积界）。
4. 定理 4.1（$|S|\le3$ 时 H 不可能）与系 4.2（$|S|\le3$ 时 $\mu<2a_1^2$）。
5. 引理 5.1（$B\to D_1\setminus S$ 对应，含 $T_p\ge p^2q_p$）、引理 5.3（$B=\varnothing$ 与 $|B|=1$ 的情形闭环：后者给 $\mu<a_1^{3/2}/\sqrt2\le2a_1^2$）。
6. 定理 6.1（¬H ⟹ 存在实现项 $t<2a_1^2$）与系 6.2（TCL 常数改写接口）。

**缺口（唯一，已收缩）**

7. 【缺口】排除 H 且 $|B|\ge2$ 且 $|S|\ge4$（$B=S\setminus D_1$）。已有全部推论与可行下手的定量形式见 §5（【缺口 5.2】）；$s\le3$ 的两种计数在 $s\ge4$ 时被 $\mu\le(2a_1)^s$ 容纳（§4 注 4.3），$|B|\le1$ 的情形已由引理 5.3 排除。

**对 $a_1\ge2$ 无隐藏假设**：全部证明只用到 $a_1\ge2$、(P1)–(P5)、(K)、(M) 与上述引理；退化分支（$\mu$ 为素数即 $s=1$、$s=2$、$s=3$、$a_1=2$、$\mu\le2a_1$、$\mu/p=a_1$ 的等号情形）均单列（§4 与引理 3.2）。
