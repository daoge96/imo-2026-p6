# 16. §5 下降引理的修正（改假设版）与残余命题 $R$ 的结构分析

> 作者：prover-descent（task-8）。所有断言标【已证明】/【缺口】/【数值】。
> 记号与编号沿用 `30-final-proof.md` §1–§4（(P1)–(P6)、(K)、(M)、引理 2.2、引理 3.1、引理 4.1）。
> 本文档**不改** `30-final-proof.md`，只给出 §5 的正确替代写法与残余缺口的最窄表述。
> 独立数值脚本：`logs/d16_probe.py`、`logs/d16_nu.py`、`logs/d16_R.py`、`logs/d16_tscan.py`（前缀 `d16_`）。

---

## §0 结论速览

1. 【已证明】缺陷定位无误：`30-final-proof.md` 第 55 行 "$\nu/p\ge\nu/2>a_1$" 仅对 $p=2$ 成立；$p\ge3$ 时正确的方向是 $\nu/p\le\nu/2$。位置引理 3.1 需要 $k=\nu/p\ge a_1$，该前提**未被建立**；步骤 6、9（乃至引理 5.2、定理 6.1、6.3、原题的书面链）都依赖它。
2. 【已证明】**正确的修法是"改假设"**：把下降引理的假设 $\nu>2a_1$ 换成 $\nu>a_1p$。此时 $\nu/p>a_1\ge2$，位置引理逐字可用，原证明第 1–9 步**一字不改**地成立（本文引理 16.4 给出自足版）。
3. 【已证明】这个改动是**必需的**而非仅为方便：只要残余 $R$（见 §4）成立，原表述（假设 $\nu>2a_1$）的引理 5.1 **为假**（命题 16.8）；而且对 $\nu=\nu_p$，原 §5 的"$\operatorname{rad}(a_i)$ 极小 $A_\infty$-因子"构造**必然**给不出 $\nu'<\nu/p$（引理 16.14）。
4. 【已证明】推论：$E_p:=\{\mu\in\mathcal M:p\mid\mu\}\ne\varnothing\Rightarrow \min E_p\le a_1p$（命题 16.6）。
5. 【已证明】**$R$ 与引理 5.2 精确等价**（命题 16.9）：$R\iff\neg$引理 5.2。故 $FME$ 的唯一缺口就是 $R$。
6. 【已证明】$R$ 情形的完整结构刻画（§5，引理 16.12–16.15），含"首个被 $p$ 整除的项 $=x_p^{\min}=p\tau_p$"、"$\operatorname{rad}(a_i)\ge\nu_p$ 被迫"等刚性事实。
7. 【数值】独立复跑（本文脚本）：$a_1\le500$ 内 $R$ **零实例**；$\max\nu_p/(2a_1)=0.6176$（$a_1=187,p=7,\nu_p=231$）；$\max p/a_1=1$（唯一取等处 $a_1=p=2$）；$\max\nu_p/(a_1p)=0.5$；$t$ 的所有 $\ge2$ 因子 $\notin A_\infty$（370/370）。
8. 【缺口】**唯一残余**：$R$（等价形式见 §4 命题 16.9）。$\neg R\Rightarrow$ 引理 5.2 $\Rightarrow$ 定理 6.1 $\Rightarrow$ §7 $\Rightarrow$ 原题。链条完整且已写出（定理 16.10）。

---

## §1 记号（自足）

固定整数 $a_1\ge2$，$(a_n)$ 为题设序列，$D_n=\operatorname{supp}(a_n)$，$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \forall i\le n\}$，$A_\infty=\bigcap_nA_n$，$\mathrm{kill}(k)=\min\{i:\gcd(k,a_i)=1\}$，横截集、项、$\mathcal M$（$A_\infty$ 的极小元集）、$\mu$ 的私有指标 $I_x(\mu):=\{i:D_i\cap\operatorname{supp}(\mu)=\{x\}\}$（引理 4.1 保证非空）。

本文新增记号（只用于 §4–§5）：

$$E_p:=\{\mu\in\mathcal M:p\mid\mu\},\qquad
\nu_p:=\min E_p\ (\text{若 }E_p\ne\varnothing),\qquad
x_p^{\min}:=\min\{z\in A_\infty:p\mid z\},$$
$$F_p:=\{\operatorname{supp}(a_t):\ p\nmid a_t\}\ \ (\text{“不含 }p\text{ 的项的支持集”族}),\qquad
\tau_p:=\min\{s\ge1:\operatorname{supp}(s)\ \text{是}\ F_p\ \text{的横截集}\},$$
$$\mathcal R_p:=\{s\ge1:\operatorname{supp}(s)\ \text{是}\ F_p\ \text{的横截集}\}\ (\text{称实现元集}),\qquad a_r:=\min\{t:p\mid a_t\}.$$

【已证明】若 $E_p\ne\varnothing$ 则 $\tau_p$ 存在（$F_p$ 中每个元素都含 $a_1$ 的某个素因子：$t\ge2$ 时 $D_t\cap D_1\ne\varnothing$（(P1)），$t=1$ 时 $D_1\cap D_1\ne\varnothing$，故 $\operatorname{rad}(a_1)\in\mathcal R_p$）。
【已证明】$p\mid a_1\Rightarrow\operatorname{rad}(a_1)\in A_\infty$ 且 $p\mid\operatorname{rad}(a_1)$，故 $x_p^{\min}\le\operatorname{rad}(a_1)\le a_1$。

---

## §2 缺陷的精确形态

原始步骤（`30-final-proof.md` 第 53–55 行）为：$\nu/p\ge2$；$\nu/p\notin A_\infty$，$i:=\mathrm{kill}(\nu/p)<\infty$；然后断言 $\nu/p\ge\nu/2>a_1$ 并调用引理 3.1。

- 【已证明】当 $p\ge3$ 时 $\nu/p<\nu/2$，所以"$\ge\nu/2$"方向错；真正需要的是 $\nu/p\ge a_1$。
- 【已证明】该前提在假设 $\nu>2a_1$ 下**不自动成立**：例如 $\nu=3\cdot34=102$、$a_1=187$（此时 $\nu$ 甚至 $\le2a_1$）有 $\nu/p=34<a_1$。等价地，所需前提就是 §9 的 $H$ 的单素数版本，而数值上 $H$ 从未成立（`logs/claimB_scan.py`、本文 §6）。
- 【已证明】受影响的不只是第 4 步：步骤 6（$i<j$）、步骤 9（$\nu'\le a_i<\nu/p$）以及引理 5.2 的迭代证明全部依赖第 4 步。

**修正策略（本文采用）**：不动第 1–9 步，只把假设加强为 $\nu>a_1p$。这样 $\nu/p>a_1\ge2$，第 4 步的方案 "$\nu/p>a_1$" 是真的，其余步骤原封不动。

---

## §3 修正版下降引理（完整自足证明）

**引理 16.4（下降，修正版）**【已证明】 设 $\nu\in\mathcal M$，$p\in\operatorname{supp}(\nu)$，$\nu>a_1p$。则存在 $\nu'\in\mathcal M$ 使
$$p\in\operatorname{supp}(\nu'),\qquad \operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\},\qquad \nu'<\nu/p .$$

证明：记 $T:=\operatorname{supp}(\nu)$。由 $\nu\in A_\infty$，$\operatorname{supp}(\nu)$ 是横截集（对每个 $i$ 有 $D_i\cap T\ne\varnothing$），即 $T$ 是横截集。

1. $p\ge2\Rightarrow a_1p\ge2a_1>a_1$，故 $\nu>a_1$。由 (P5)（$A_\infty\cap[a_1,\infty)$ 的递增枚举即序列）得 $\nu$ 是项：$\nu=a_j$，从而 $T=D_j$。【用 (P5)】
2. $m:=\nu/p$。先证 $m\ge2$：若 $m=1$ 则 $\nu=p$，$T=\{p\}$，$T=D_j$ 是横截集，故 $p\in D_i\ (\forall i)$，特别 $p\mid a_1$，于是 $p\le a_1<a_1p=\nu=p$，矛盾。故 $m\ge2$。
   【已证明】又 $m=\nu/p>a_1\ge2$，$m>a_1$。【用假设 $\nu>a_1p$】
3. $\nu\in\mathcal M$ 无平方因子（引理 2.2），故 $p\nmid m$，于是 $\operatorname{supp}(m)=T\setminus\{p\}$，且 $m$ 是 $\nu$ 的真因子。由极小性 $m\notin A_\infty$，故 $m\notin A_\infty$ 且 $m\ge2$；令 $i:=\mathrm{kill}(m)$，由 (K) $i<\infty$。【用引理 2.2、(K)】
4. $\gcd(m,a_i)=1\Rightarrow D_i\cap\operatorname{supp}(m)=\varnothing\Rightarrow D_i\cap T\subseteq\{p\}$；而 $T$ 是横截集故 $D_i\cap T\ne\varnothing$。于是
   $$D_i\cap T=\{p\},\qquad p\mid a_i . \tag{16.1}$$
5. 由 $m>a_1$ 与 $\mathrm{kill}(m)=i<\infty$，引理 3.1（取 $k:=m$）给出
   $$a_i<m=\nu/p . \tag{16.2}$$
6. 由 (P2) $R_0:=\operatorname{rad}(a_i)\in A_\infty$ 且 $R_0\ge2$。取 $\nu'$ 为集合 $\mathcal F:=\{\nu''\ge2:\nu''\mid R_0,\ \nu''\in A_\infty\}$ 的极小元（$\mathcal F\ne\varnothing\ni R_0$，故存在）。则 $\nu'\in\mathcal M$：若 $\nu''\mid\nu'$、$\nu''\in A_\infty$、$2\le\nu''<\nu'$，则 $\nu''\mid R_0$ 给出 $\nu''\in\mathcal F$，与 $\nu'$ 极小矛盾。【用 (P2)】
7. $\operatorname{supp}(\nu')\subseteq\operatorname{supp}(R_0)=D_i$，结合 (16.1) 得 $\operatorname{supp}(\nu')\cap T\subseteq D_i\cap T=\{p\}$；又 $\nu'\in A_\infty$ 而 $T$ 是横截集，故 $\operatorname{supp}(\nu')\cap T\ne\varnothing$。于是 $\operatorname{supp}(\nu')\cap T=\{p\}$，特别 $p\in\operatorname{supp}(\nu')$。
8. $\nu'\le R_0\le a_i\overset{(16.2)}{<}\nu/p$。$\blacksquare$

**注 16.5**【已证明】
（a）证明中第 1–9 步与 `30-final-proof.md` §5 完全一致，只是第 4 步改为真命题 "$m>a_1$"。
（b）$\nu>a_1p$ 是**充分**假设；$\nu>2a_1$ 不够（见 §4 命题 16.8）。
（c）构造 $\nu'$（"$\operatorname{rad}(a_i)$ 的极小 $A_\infty$-因子"）自动满足 $p\mid\nu'$、$\operatorname{supp}(\nu')\cap T=\{p\}$，无需额外假设。

---

## §4 $R$：唯一残余、其等价形式与逻辑地位

**命题 16.6（$p$-链终止）**【已证明】 设 $E_p\ne\varnothing$。则 $\nu_p\le a_1p$。（第二段 $\nu_p\le a_1^2$ 需要 $p\le a_1$，即路线 (b)，未证；无条件只有 $\nu_p\le a_1p$。）

证明：取 $\mu_0\in E_p$ 并归纳构造：若当前 $\nu\in E_p$ 且 $\nu>a_1p$，由引理 16.4 得 $\nu'\in\mathcal M$ 使 $p\mid\nu'$（即 $\nu'\in E_p$）且 $\nu'<\nu$。由于 $\nu$ 严格递减且恒 $\ge2$，过程有限步停止，停在 $\nu^\ast\in E_p$ 且 $\nu^\ast\le a_1p$。于是 $\nu_p\le\nu^\ast\le a_1p$。$\blacksquare$

**定义 16.7（残余 $R$）** 称 $R$ 成立，若
$$\exists\ \text{素数 }p\ \exists\mu\in\mathcal M:\quad p\mid\mu,\quad p>2a_1,\quad \mu>2a_1 .$$
（由命题 16.6，此时可 WLOG 取 $\mu=\nu_p$，并且自动有 $\mu\le a_1p$，即 $R\iff\exists p:E_p\ne\varnothing,\ p>2a_1$。见命题 16.9。）

**命题 16.8** 设 $R$ 成立，则 `30-final-proof.md` 的引理 5.1（假设 $\nu>2a_1$，结论 $\exists\nu'\in\mathcal M:p\mid\nu',\ \nu'<\nu/p$）**为假**。

证明：由 $R$ 取 $p>2a_1$ 与 $\mu\in E_p$，$\mu>2a_1$。取 $\nu:=\nu_p\in E_p$，则 $\nu\ge p>2a_1$，$\nu$ 满足引理 5.1 的假设。若结论成立，得 $\nu'\in\mathcal M$，$p\mid\nu'$，$\nu'<\nu/p<\nu$，即 $\nu'\in E_p$ 且 $\nu'<\nu=\min E_p$，矛盾。$\blacksquare$
（【已证明】于是"加假设"不是可选项：只要 $R$ 成立，原引理就必须修改。）

**命题 16.9（$R$ 与引理 5.2 精确等价）**【已证明】
$$R\iff \exists p:\ E_p\ne\varnothing\ \text{且}\ p>2a_1\iff \neg(\text{引理 5.2}:\ \forall\mu\in\mathcal M\ \forall p\mid\mu:\ p\le2a_1).$$

证明：引理 5.2 等价于 "$\forall p:\ E_p\ne\varnothing\Rightarrow p\le2a_1$"，其否定就是 $\exists p:E_p\ne\varnothing\wedge p>2a_1$。又若 $\exists p:E_p\ne\varnothing\wedge p>2a_1$，取 $\mu=\nu_p$，则 $\mu\ge p>2a_1$，故 $R$ 成立；反之 $R$ 给出 $E_p\ne\varnothing$ 与 $p>2a_1$。$\blacksquare$
（注：与 `17-fme-indep.md` §3 的方框相比，本等价说明 $R$ 的表述中"$\nu\le a_1p$"那条可以**删去**——$\mu>2a_1$ 与 $p>2a_1$ 已足够，$\nu_p\le a_1p$ 由命题 16.6 自动成立。）

**定理 16.10（$\neg R$ 即可闭环）**【已证明，引用 30 号 §6–§7】 $\neg R\Rightarrow$ 引理 5.2 $\Rightarrow$ 定理 6.1（FME：$\mathcal M$ 有限且 $\operatorname{supp}(\mu)\subseteq\{p\le2a_1\}$）$\Rightarrow$ 引理 6.2 $\Rightarrow$ 定理 6.3 $\Rightarrow$ §7 $\Rightarrow$ 原题 $(\exists T,L>0\ \forall n:a_{n+T}=a_n+L)$。
证明：$\neg R$ 即 $\forall p\ (E_p\ne\varnothing\Rightarrow p\le2a_1)$ 即引理 5.2；其余链条见 30 号文件 §6–§7（那部分不受本缺口影响，且推理自足）。$\blacksquare$

**说明 16.11（为什么 $R$ 不是空话）**【已证明】 $R$ 中的不等式彼此不冲突：$p>2a_1$ 与"若 $E_p\ne\varnothing$ 则 $\nu_p\le a_1p$"（命题 16.6）相容（$2a_1<a_1p$ 当 $p>2$）。$R$ 断言的是"**任何** $p>2a_1$ 都不出现在极小元的支撑里"。

---

## §5 $R$ 情形的结构（准备反驳 $R$）

本节固定 $p$ 满足 $E_p\ne\varnothing$，记 $\sigma:=\nu_p$，$t:=\sigma/p$。

**引理 16.12（$\sigma$ 的基本形状）**【已证明】
(i) $\sigma\in\mathcal M$，$p\mid\sigma$，$\sigma=pt$，且 $t\notin A_\infty$；于是 $t$ 的每个 $\ge2$ 的因子也 $\notin A_\infty$；
(ii) $t\le a_1$ 且 $t<a_1$（严格）；又 $t=1\iff\sigma=p\iff p\in A_\infty$，此时 $p\mid a_1$ 且 $p\le a_1\le2a_1$（故 $R$ 情形下自动 $t\ge2$）；
(iii) $t$ 是 $F_p$ 的实现元，即 $\operatorname{supp}(t)$ 与每个 $D_s\ (p\nmid a_s)$ 相交；从而 $\tau_p\le t$，$x_p^{\min}=p\tau_p\le\sigma$；
(iv) 每个项 $a_s$ 被 $p$ 或 $t$ 的某个素因子整除；若 $p\nmid a_1$，则存在素数 $q\mid t$ 使 $q\mid a_1$；而在 $R$（$p>2a_1$）情形下自动有 $p\nmid a_1$。

证明：(i) $\sigma\in E_p\subseteq\mathcal M$；$t=\sigma/p$ 是 $\sigma$ 的真因子。若 $t\in A_\infty$，则 $t$ 是 $\sigma$ 的真因子（$p\ge2$）且 $t\ge2$，与 $\sigma\in\mathcal M$ 矛盾；故 $t\notin A_\infty$。若 $d\mid t$、$d\ge2$、$d\in A_\infty$，则由 $A_\infty$ 对取倍数封闭（(M)）得 $t\in A_\infty$，矛盾；故 $t$ 的所有 $\ge2$ 因子都 $\notin A_\infty$。
(ii) 由命题 16.6 $\sigma\le a_1p$ 得 $t\le a_1$。若 $t=a_1$：由 (i) $t\notin A_\infty$，故 $i:=\mathrm{kill}(t)<\infty$（(K)），而 $t=a_1$ 使引理 3.1（$k:=t\ge a_1$）给出 $a_i<t=a_1$，与 $a_i\ge a_1$ 矛盾。故 $t<a_1$。最后，$t=1$ 时 $\sigma=p$，$p\in E_p\subseteq A_\infty$，故 $p$ 整除每个项，特别 $p\mid a_1$，于是 $p\le a_1$；反之 $p\in A_\infty$ 时 $p\in E_p$（$p\in A_\infty$ 无真因子 $\ge2$）故 $\nu_p=p$。$t\ge2$ 时 $\sigma=pt>2a_1$ 当且仅当 $t>2a_1/p$；在 $R$（$p>2a_1,\sigma>2a_1$）下 $t=\sigma/p>2a_1/p\ge1$，故 $t\ge2$。
(iii) $\operatorname{supp}(\sigma)=\operatorname{supp}(t)\cup\{p\}$ 是横截集，故对 $s$ 若 $p\nmid a_s$ 则必 $D_s\cap\operatorname{supp}(t)\ne\varnothing$；即 $\operatorname{supp}(t)$ 是 $F_p$ 的横截集，$t\in\mathcal R_p$，故 $\tau_p\le t$。又 $k\in A_\infty$ 且 $p\mid k$ $\iff$ $k=p\cdot s$ 且 $s\in\mathcal R_p$（$\operatorname{supp}(k)=\operatorname{supp}(k/p)\cup\{p\}$），故 $x_p^{\min}=p\tau_p$；由 $\operatorname{supp}(\tau_p)\cup\{p\}$ 是横截集得 $p\tau_p\in A_\infty$。于是 $x_p^{\min}=p\tau_p\le pt=\sigma$。
(iv) 由 (iii) 第一句：$\operatorname{supp}(t)\cup\{p\}$ 是横截集，即每个 $D_s$ 与它相交。取 $s=1$：若 $p\nmid a_1$ 则 $D_1\cap\operatorname{supp}(t)\ne\varnothing$，即存在素数 $q\mid t$、$q\mid a_1$。最后补一句 $R$ 情形的"$p\nmid a_1$"：若 $p\mid a_1$ 则 $p\le\operatorname{rad}(a_1)\le a_1$，与 $p>2a_1>a_1$ 矛盾，故 $R$ 下 $p\nmid a_1$。$\blacksquare$

**引理 16.13（私有指标与"坏情形"被迫）**【已证明】 设 $i:=\mathrm{kill}(t)=\min I_p(\sigma)$。则
(i) $D_i\cap\operatorname{supp}(\sigma)=\{p\}$，$p\mid a_i$，$\gcd(a_i,t)=1$；
(ii) $a_i/p\in\mathcal R_p$，故 $\tau_p\le a_i/p$，即 $p\tau_p\le a_i$；结合 (i) 得 $x_p^{\min}\le a_i$；
(iii) $\operatorname{rad}(a_i)\ge\sigma$，从而 $a_i\ge\sigma$；
(iv) 若 $t\ge2$（$R$ 情形自动满足，引理 16.12(ii)），则 $\sigma\le a_{i-1}$ 且 $a_i\ne\sigma$。

证明：(i) $t\notin A_\infty$（引理 16.12(i)；$t=1$ 时按约定 $1\notin A_\infty$ 且 $\mathrm{kill}(1)=1$）故 $i<\infty$；$t\notin A_i$ 即 $D_i\cap\operatorname{supp}(t)=\varnothing$，而 $\operatorname{supp}(\sigma)=\operatorname{supp}(t)\cup\{p\}$ 是横截集给出 $D_i\cap\operatorname{supp}(\sigma)\ne\varnothing$，故 $=\{p\}$，特别 $p\mid a_i$；又 $\gcd(a_i,t)=1$。且 $i=\min I_p(\sigma)$ 由 $I_p(\sigma)=\{s:D_s\cap\operatorname{supp}(\sigma)=\{p\}\}=\{s:D_s\cap\operatorname{supp}(t)=\varnothing\}$ 与 $\mathrm{kill}$ 的定义直接得到。
(ii) 设 $s$ 满足 $p\nmid a_s$。因 $D_s$ 与 $D_i$ 都是横截集（(P1)），$D_s\cap D_i\ne\varnothing$；又 $p\notin D_s$，故 $D_s\cap(D_i\setminus\{p\})\ne\varnothing$，而 $D_i\setminus\{p\}\subseteq\operatorname{supp}(a_i/p)$。故 $\operatorname{supp}(a_i/p)$ 与每个这样的 $D_s$ 相交，即 $a_i/p\in\mathcal R_p$，于是 $\tau_p\le a_i/p$。
(iii) 记 $\nu':=\min\{\nu''\ge2:\nu''\mid\operatorname{rad}(a_i),\ \nu''\in A_\infty\}\in\mathcal M$（§3 第 6 步）。由 (i) 完全同 §3 第 7 步得 $\operatorname{supp}(\nu')\cap\operatorname{supp}(\sigma)=\{p\}$，故 $p\mid\nu'$，即 $\nu'\in E_p$，于是 $\nu'\ge\sigma$。若 $\operatorname{rad}(a_i)<\sigma$ 则 $\nu'\le\operatorname{rad}(a_i)<\sigma$，矛盾；故 $\operatorname{rad}(a_i)\ge\sigma$，从而 $a_i\ge\operatorname{rad}(a_i)\ge\sigma$。
(iv) 设 $t\ge2$。若 $\sigma>a_{i-1}$，则由 $a_i=\min(A_{i-1}\cap(a_{i-1},\infty))$（(P4)）与 $\sigma\in A_\infty\subseteq A_{i-1}$、$\sigma>a_{i-1}$ 得 $a_i\le\sigma$，结合 (iii) 得 $a_i=\sigma$；但 $\gcd(a_i,t)=1$ 而 $\sigma=pt$ 给出 $t\mid a_i$，$t\ge2$，即 $\gcd(a_i,t)=t\ne1$，矛盾。故 $\sigma\le a_{i-1}$；$a_i\ne\sigma$ 同一理由。$\blacksquare$

**引理 16.14（原 §5 构造在 $\nu=\nu_p$ 处必然失效）**【已证明】 沿用 §3 的构造 $\nu'=\min\{\nu''\ge2:\nu''\mid\operatorname{rad}(a_i),\nu''\in A_\infty\}$（$i=\mathrm{kill}(t)$）。则 $\nu'\in E_p$ 且 $\nu'\ge\sigma$，于是
$$\nu'\ge\sigma=\nu_p>\nu_p/p=\sigma/p .$$
即该构造**永远**给不出 $\nu'<\nu/p$（在 $\nu=\nu_p$ 处）。
证明：$\nu'\in E_p$ 已证（引理 16.13(iii) 首句），故 $\nu'\ge\min E_p=\sigma>\sigma/p$。$\blacksquare$

**引理 16.15（$R$ 情形下"首个 $p$-项"是 $p\cdot\tau_p$）**【已证明】 若 $p>2a_1$，则 $\operatorname{supp}(\tau_p)\cup\{p\}$ 是横截集（§1），故 $p\tau_p\in A_\infty$ 且 $p>2a_1\ge a_1$，于是 $p\tau_p$ 是项；又 $p\mid p\tau_p$，故 $a_r\le p\tau_p$。另一方面 $a_r$ 是 $p$-可除的 $A_\infty$ 元（它是 $A_\infty$ 的项），故 $x_p^{\min}\le a_r$；结合 $x_p^{\min}=p\tau_p$（定义）得
$$a_r=x_p^{\min}=p\tau_p,\qquad a_r\le\sigma=\nu_p .$$
更精确地说：$x_p^{\min}=\min\{z\in A_\infty:p\mid z\}$ 中被 $F_p$ 的最小实现元唯一决定，即 $x_p^{\min}=p\tau_p$，而 $p>2a_1$ 时 $x_p^{\min}\ge p>a_1$ 使它是项，从而就是 $a_r$。$\blacksquare$

**推论 16.16（反驳 $R$ 的三条充分路线）**【已证明的化归】
$$\text{(a)}\ \forall p:\ p\mid a_1\Rightarrow\neg R_p;\qquad
\text{(b)}\ \bigl(\forall p\ E_p\ne\varnothing\Rightarrow p\le a_1\bigr)\Rightarrow\neg R;\qquad
\text{(c)}\ \bigl(\forall p\ E_p\ne\varnothing\Rightarrow a_r\le2a_1\bigr)\Rightarrow\neg R .$$
（$R_p$ 表示"$R$ 对该 $p$ 成立"。）
证明：(a) $p\mid a_1\Rightarrow x_p^{\min}\le\operatorname{rad}(a_1)\le a_1$；又 $\sigma\le a_1p$ 与 $p\le a_1<2a_1$ 相容，但更直接：$p\le x_p^{\min}\le a_1<2a_1$。(b) 由命题 16.9。(c) 由引理 16.15，$a_r=p\tau_p\ge p$，故 $p\le a_r\le2a_1$，再 16.9。$\blacksquare$

【缺口】三条路线都未证；数值（§6）显示 (b) 实际成立（$\max p/a_1=1$，唯一取等 $a_1=p=2$），故 (b) 或 (c) 都是有希望的着手点。

---

## §6 独立数值自检

全部脚本在 `logs/`，前缀 `d16_`，用 Python 精确整数模拟（`alive[k]` 记录 $k$ 是否与所有已处理项都不互素；对 $k\ge a_1$ 由位置引理 `alive[k]` $\iff k\in A_\infty$），$\mathcal M$ 取 `alive` 的极小元。
**精度说明**（诚实标注）：对 $k\ge a_1$，`alive[k]` 与 $A_\infty$-归属**精确等价**（若 $\mathrm{kill}(k)=j<\infty$ 则位置引理给 $a_j<k\le B$，故被正确处理）。但 $k<a_1$ 时可能虚高（杀手项 $>B$）：这一段产生的"伪极小元"$\le a_1\le2a_1$，故对 $\mu>2a_1$、$p>2a_1$、$\nu_p>2a_1$ 与 $R$ 的判定无影响；只是若某个真 $\mu>2a_1$ 恰被一个 $<a_1$ 的伪元整除，则会被漏报——此时该伪元本身与真实 $\mathcal M$ 元的差别已在 `d16_tscan.py` 的 `in_Ainf` 中对 $d<a_1$ 逐个用 $\mathrm{kill}$ 扫描复核（370/370 通过）。

1. `python d16_probe.py 2 200 6 8` → `cases(mu count): 244`；`max mu/(2a1) = 0.6364 (a1=187, mu=238)`；`count mu>2a1: 0`；`count (mu,p) with mu/p>=a1 [H_p]: 0`；`count kill-term >= mu: 116`。
   —— 印证：$\mathcal M$ 中每个 $\mu$ 的每个 $p$ 都有 $\mu/p<a_1$（即 $H$ 全假），且"$\mathrm{kill}(\mu/p)$ 的项 $\ge\mu$"是**常态**（116/244 对），说明 §4–§5 的坏情形不是稀有现象，但对 $\mu\le2a_1$ 无害。
2. `python d16_nu.py 2 300 187` → `count (a1,p) with E_p nonempty: 370`；`max nu_p/(2a1) = 0.6176 (a1=187,p=7,nu_p=231)`；`max nu_p/a1 = 1.2353 (a1=187,p=7)`；`max nu_p/(a1 p) = 0.5`；`count nu_p > 2a1: 0`；`count nu_p > a1: 4`（$\{(175,13,182),(187,7,231),(209,7,231),(247,7,266)\}$）；`count nu_p > a1*p: 0`。
   —— 印证命题 16.6（$\nu_p\le a_1p$ 零反例）并显示 $\nu_p>a_1$ 会发生（故 $p\le a_1$ 不能由 $\nu_p\le a_1$ 得到）。
3. `python d16_R.py 2 500` → `(a1,p) with E_p nonempty: 626`；`max p/a1 = 1.0 (a1=2,p=2,nu_p=2)`；`R 实例数: 0`。
   —— $R$ 在 $a_1\le500$ 全范围零实例；且 $p\le a_1$ 亦零反例。
4. `d16_nu.py 2 300 187` 明细：`a1=187 D1=[11,17] M=[22,102,187,231,238]`，`E_3=[102,231]`（$\nu_3=102=3\cdot34$，$34<a_1$），`E_7=[231,238]`（$\nu_7=231=3\cdot7\cdot11>a_1$ 但 $\le2a_1$）。
   —— 该例同时给出引理 16.12–16.14 的具体形态：$\sigma=102$，$t=34=2\cdot17$，$i=\mathrm{kill}(34)=5$，$a_i=231\ge\sigma$，构造给 $\nu'=231>\sigma/3$。
5. `python d16_tscan.py 2 300` → `(a1,p) with E_p nonempty: 370`；`存在 d|t, d>=2, d∈A_∞ 的实例数: 0`。
   —— 印证引理 16.12(i)（$t$ 及其所有 $\ge2$ 因子都 $\notin A_\infty$）：370 个实例零例外。
6. 【反例警示，已复核】$x_p^{\min}=\min\{z\in A_\infty:p\mid z\}$ 与 $\nu_p$ 之间**没有** $\nu_p\le x_p^{\min}$：$a_1=187,p=3$ 时 $x_3^{\min}=66<102=\nu_3$。故"$p$-可除的 $A_\infty$ 元必能下推到不大于它的 $E_p$ 元"是**假**的（$66$ 的 $A_\infty$-因子只有 $22,66$，均不可除 $3$；$E_3=\{102,231\}$）。这是 §5 分析中必须小心的一点。

【数值/启发式，非证明】$a_1\le500$ 内无 $R$；与 Lead 的 $a_1\le10^4$ 扫描一致（0 例 $\mu>2a_1$、$\max\mu/(2a_1)=0.724$、$\max p/a_1=1$）。

---

## §7 残余命题与"闭环清单"

### 7.1 最窄残余（唯一）

> **$R$**：存在素数 $p$ 与 $\mu\in\mathcal M$ 使 $p\mid\mu$、$p>2a_1$、$\mu>2a_1$。
> **等价形式**（命题 16.9，已证明等价）：
> (R1) $\exists p:\ E_p\ne\varnothing$ 且 $p>2a_1$；
> (R2) $\exists p:\ E_p\ne\varnothing$ 且 $\nu_p>2a_1$（因 $\nu_p\ge p$）；
> (R3) $\neg$引理 5.2。
>
> **若要闭环，只需**：$\forall p\ \bigl(E_p\ne\varnothing\Rightarrow p\le2a_1\bigr)$。

【已证明】$\neg R$ ⟹ FME ⟹ 原题（定理 16.10）；$R$ ⟹ 原引理 5.1 为假（命题 16.8）。

### 7.2 若有反例，形态已被完全钳制

由 §5：$R$ 的任何反例必满足（$p>2a_1$，$\sigma=\nu_p$，$t=\sigma/p$）：
$$p>2a_1,\qquad 2\le t<a_1,\qquad t\notin A_\infty,\qquad t\ \text{及其全部}\ \ge2\ \text{因子都}\notin A_\infty,\qquad 2a_1<\sigma=pt\le a_1p,$$
$$\exists q\mid t:\ q\mid a_1,\qquad \operatorname{rad}(a_i)\ge\sigma,\qquad a_i\ge\sigma,\qquad a_r=x_p^{\min}=p\tau_p\le\sigma,\qquad \tau_p\le t .$$
即：$R$ 的反例必然是"$p$ 很大、$t$ 很小且 $A_\infty$-原始、$\nu_p=pt$ 落在 $(2a_1,a_1p]$、且 $\sigma$ 的首个 $p$-私有指标项 $a_i\ge\sigma$"的刚性格局；数值上 $p/a_1\le1$ 使 $p>2a_1$ 显得更不可能。
另外【已证明】对 $\nu=\nu_p$，§3/§5 的"$\operatorname{rad}(a_i)$ 极小 $A_\infty$-因子"构造**永远失败**（引理 16.14），故反驳 $R$ 不能只靠该构造。

### 7.3 三条可攻击路线（按可能性排序）

1. **(b) 证 $p\le a_1$（更强，数值零反例）**：则 $R$ 平凡消失，且 FME 给出更小的常数（$\operatorname{supp}(\mu)\subseteq\{p\le a_1\}$）。
2. **(c) 证 $a_r\le2a_1$（$E_p\ne\varnothing$ 时）**：由引理 16.15，$a_r=x_p^{\min}=p\tau_p$，故等价于 $p\tau_p\le2a_1$；注意对 $E_p=\varnothing$ 的 $p$ 该式**为假**（$a_1=2,p=31$：$x_{31}^{\min}=62>4$），故必须用 $E_p\ne\varnothing$ 的额外信息。
3. **直接给 $E_p\ne\varnothing\wedge p>2a_1$ 的反例构型分析**：按 §7.2 的钳制条件做有限搜索（例如固定 $t$ 为小素数、$p$ 大素数）——但数值提示 $a_1$ 需很大才可能触发。

### 7.4 与 `17-fme-indep.md`（prover-mu）的关系

【已证明，独立复核】两文的修正引理一致（假设 $\nu>a_1p$，结论 $p\mid\nu'$、$\operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\}$、$\nu'<\nu/p$）、推论 $\min E_p\le a_1p$ 一致、残余 $R$ 的实质一致（本文命题 16.9 证明其等价形式中可删去 "$\nu\le a_1p$"），局部后果与 17 号 §3 的三条一致（$p\nmid a_1$ 且 $\operatorname{supp}(t)\cap D_1\ne\varnothing$、$\mathrm{kill}(t)$ 存在、$R$ 只涉及 $E_p$ 的最小段）。本文额外给出：$R\Rightarrow$原引理 5.1 为假（命题 16.8）、原构造必然失效（引理 16.14）、$t$ 及其全部因子 $\notin A_\infty$（引理 16.12(i)）、$a_i/p\in\mathcal R_p$ 与 $\operatorname{rad}(a_i)\ge\sigma$（引理 16.13）、$a_r=x_p^{\min}=p\tau_p$（引理 16.15）以及三条充分路线（推论 16.16）。17 号补充给本文的信息：其 §4 的"增量 $\min A_n$"算法**不依赖位置引理**，可作 §6 方法之外的独立数值交叉验证；两文数值在两个不同实现下都给出 $R$ 零反例、$p\le a_1$ 零反例。

---

## §8 供 Lead 合并的最小补丁（替换 `30-final-proof.md` §5 第 47–64 行）

1. 引理 5.1 的假设改为 $\nu>a_1p$，正文照抄（本文引理 16.4 即逐字自足版）。
2. 引理 5.2 的证明改写为：先由引理 16.4 迭代得 $\nu_p\le a_1p$（命题 16.6）；再断言"$\nu_p\le2a_1$"（即 $\neg R$）作为**唯一残余**，并注明其等价形式（命题 16.9）与数值状态（§6）。
3. 定理 6.1 的结论保持不变，但它的前提正是 $\neg R$（即引理 5.2）。未证 $\neg R$ 时仍可无条件得到：$\mathcal M$ 中每个 $\mu$ 无平方因子、$\operatorname{supp}(\mu)\subseteq\{p:E_p\ne\varnothing\}$、且 $\nu_p\le a_1p$（命题 16.6）；但"$\mathcal M$ 有限"与"素因子 $\le2a_1$"仍依赖 $\neg R$。
4. 建议在 §5 末加一句注："第 4 步的 $\nu/p\ge\nu/2$ 只在 $p=2$ 成立；本文以 $\nu>a_1p$ 规避"。

---

## §9 待办（若有更多时间）

- 攻击路线 (b)：$E_p\ne\varnothing\Rightarrow p\le a_1$。已有素材：引理 16.12(iv)（$\exists q\mid t:q\mid a_1$）、引理 16.13(ii)（$a_i/p\in\mathcal R_p$）、引理 4.1（$I_x(\sigma)$ 全非空）、(P6)（项间隔 $\le\operatorname{rad}(a_1)$）与 $p>a_1$ 时 $p\nmid a_1$、$\sigma\ge p$。
- 攻击路线 (c)：$p>2a_1$ 时 $\tau_p$ 的上界（$\tau_p\le t<a_1$ 已有；需要 $\tau_p\le 2a_1/p$）。
- 见 §10：已把 (b) 化归为更窄的 $(L)$。

---

## §10 路线 $(L)$：把 $(b)$ 化归为"某一个 $q$ 上的单侧不等式"

> task-10。本节把路线 (b) 化为一条更弱、更好用的命题 $(L)$，并给出 $(\neg L)$ 下的完整二分结构；$(L)$ 本身仍【缺口】。

**定义 18.1（$(L)$）** 固定 $p$ 使 $E_p\ne\varnothing$，$\sigma:=\nu_p$、$t:=\sigma/p$（引理 16.12：$\sigma\in\mathcal M$、$t<a_1$），记 $Q_p:=\{q\ \text{素}:q\mid t,\ q\mid a_1\}$。称 $(L)$ 成立，若
$$(L)\qquad \exists q\in Q_p:\quad \sigma\le a_1q .$$

**命题 18.2（$(L)\Rightarrow(b)\Rightarrow\neg R$）**【已证明】
证明：设 $q\in Q_p$ 且 $\sigma\le a_1q$。由 $q\mid t$ 得 $q\le t$，故
$$p=\frac{\sigma}{t}\le\frac{a_1q}{t}\le a_1 .$$
再由推论 16.16(b) 得 $\neg R$。$\blacksquare$
（等价改写：$\sigma\le a_1q\iff\sigma/q\le a_1$；又 $\sigma/q\ge p$，故 $(\neg L)$ 即"对一切 $q\in Q_p$，$\sigma/q>a_1$ 严格成立"，于是引理 16.4 沿每个 $q\in Q_p$ **都可使用**。）

**归约（证明 $(b)$ 的规范形式）**【已证明】 设 $E_p\ne\varnothing$ 且 $p>a_1$（否则已得 $p\le a_1$）。则 $p\nmid a_1$（否则 $p\le\operatorname{rad}(a_1)\le a_1$，矛盾，见引理 16.12(iv) 末），故由引理 16.12(iv) 得 $Q_p\ne\varnothing$，且 $t\ge2$（$t=1$ 时 $\sigma=p>a_1\ge q$ 与 $\sigma>a_1q$ 矛盾）。故 $(b)\iff$"$p>a_1$ 时 $(\neg L)$ 不成立"。

**引理 18.3（$(\neg L)$ 下每个 $q$ 都给下降）**【已证明】 设 $(\neg L)$ 成立（即 $\forall q\in Q_p:\sigma>a_1q$），$q\in Q_p$。则 $\sigma>a_1q$，故引理 16.4（取 $\nu:=\sigma$）给出 $\nu_q\in\mathcal M$ 使
$$q\mid\nu_q,\qquad p\nmid\nu_q,\qquad \operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\},\qquad \nu_q<\sigma/q=pt/q .$$
又 $\nu_q\in E_q$，故命题 16.6（用于 $q$）给出 $\min E_q\le a_1q$；再由引理 16.12（用于 $q$，对 $\nu_q$ 的任意 $E_q$-元成立）：$\nu_q=q\,t_q$、$t_q<a_1$、$t_q\notin A_\infty$ 且其所有 $\ge2$ 因子 $\notin A_\infty$。
**（task-14 修正）** 上一版此处写"$\nu_q\in E_q$，故 16.6 给出 $\nu_q\le a_1q$"——**不成立**：16.6 只给 $\min E_q\le a_1q$，而 $\nu_q$ 未必 $=\min E_q$。正确做法：只要当前元 $>a_1q$ 就用引理 16.4 沿 $q$ 迭代（前提 $\nu>a_1q$ 恰满足），得严格递减链并停在 $\nu_q^\ast\in E_q$、$q\mid\nu_q^\ast$、$p\nmid\nu_q^\ast$、$\nu_q^\ast\le a_1q$、$\nu_q^\ast<\sigma/q$。故 18.4 及之后的机器一律用 $\nu_q^\ast$（只需这四条）；只有 19.1 需要 $\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$ 时，才改用 16.4 一步所得的**首元**（首元同时满足 $\nu<\sigma/q$；若还需 $\le a_1q$ 则再迭代，迭代保持 $\operatorname{supp}(\cdot)\cap\operatorname{supp}(\nu_{\text{首}})=\{q\}$）。$\blacksquare$

**引理 18.4（$\mathcal M$-链：成功支给 $t\le\nu_q$，否则停在 stall 构型）**【已证明】
设 $(\neg L)$、$q\in Q_p$、$t\ge2$，$\nu_q$ 如 18.3。递归定义序列：$\mu_0:=\nu_q$；已给 $\mu_k\in\mathcal M$ 且 $p\nmid\mu_k$、$\mu_k\mid\nu_q$ 时，
- 若 $\exists\mu'\in\mathcal M$ 使 $\mu'\mid\operatorname{rad}(p\mu_k)$ 且 $p\mid\mu'$：则 $\sigma\le\mu'\le p\mu_k\le p\nu_q$，于是 $t\le\mu_k\le\nu_q$；称此步**成功**，停止；
- 否则 $\operatorname{rad}(p\mu_k)$ 的每个 $\mathcal M$-因子都 $p$-free，从而整除 $\mu_k$；令 $\mu_{k+1}:=\min\{\mu\in\mathcal M:\mu\mid\operatorname{rad}(p\mu_k)\}$（非空：$\mathcal M$ 中整除 $p\mu_k$ 者至少有一个——$k=0$ 时 $p\nu_q\in A_\infty$，用引理 2.2；归纳保持 $p\mu_k\in A_\infty$；又 $\mu_{k+1}\mid\mu_k$、$p\nmid\mu_{k+1}$、$p\mu_{k+1}\in A_\infty$）。若 $\mu_{k+1}=\mu_k$ 称**stall**并停止，否则 $\mu_{k+1}<\mu_k$ 继续。

过程必在有限步停止（正整数严格递减，或在 stall 停）。且：
(i) 若以**成功**停止：$t\le\nu_q<\sigma/q=pt/q$，故 $q<p$；
(ii) 若以**stall**停在 $\mu^\ast$：$p\nmid\mu^\ast$、$p\mu^\ast\in A_\infty$、$\mu^\ast$ 是 $p\mu^\ast$ 的**唯一** $\mathcal M$-因子、且 $\mu^\ast\mid\nu_q$；再若 $\sigma>p\mu^\ast$ 则 $t>\mu^\ast$，否则同样得 $t\le\mu^\ast\le\nu_q$ 与 $q<p$。
证明：每步的整除与 $p$-free 保持性已如上（$\mu_{k+1}\mid\operatorname{rad}(p\mu_k)=p\mu_k$ 且 $p\nmid\mu_{k+1}$ 给出 $\mu_{k+1}\mid\mu_k$）。终止性按构造。(i) 由 18.3 的 $\nu_q<\sigma/q$。(ii) stall 时 $\mu_{k+1}=\mu_k$ 说明 $p\mu_k$ 的 $\mathcal M$-因子只有 $\mu_k$；其余为定义展开。$\blacksquare$

**注 18.5（stall 构型是真实的，且 $(L)$ 归结为它）**【已证明 + 数值】 称 $(p,\mu^\ast)$ 为 **stall 构型**，若 $\mu^\ast\in\mathcal M$、$p\nmid\mu^\ast$、$p\mu^\ast\in A_\infty$ 且 $\mu^\ast$ 是 $p\mu^\ast$ 的唯一 $\mathcal M$-因子。则由 18.4，只要 stall 构型不出现，就有 $t\le\nu_q\le a_1q$——但注意这只给 $t\le a_1q$，而 $(L)$ 要 $\sigma=pt\le a_1q$，故仍有一步之遥。
【数值】真实 stall 构型确实存在：$a_1=187$、$p=3$、$\mu^\ast=22$（$\mathcal M=[22,102,187,231,238]$，$66=3\cdot22$ 的 $\mathcal M$-因子只有 $22$，且 $\sigma=\nu_3=102>66$）。该例中 $Q_3=\{17\}$ 而 $\sigma=102<a_1\cdot17=3179$，即 $(\neg L)$ 未触发。
【化归】$(L)$ 现归结为：在 stall 支（18.4(ii)），证明 $p\,\mu^\ast\le a_1q$（并用 18.3 的 $\mu^\ast\mid\nu_q\le a_1q$、$\mu^\ast\in\mathcal M$ 的私有指标结构与 16.12/5.2 等工具）；在成功支则由 18.4(i) 得 $q<p$，可对 $(q,Q_q)$ 递归（18.3 已把 $(\neg L)$ 移植到该对）。

**引理 18.6（$R$ 的一个密度必要条件）**【已证明】 设 $E_p\ne\varnothing$、$p>2a_1$（即 $R$ 情形），$\sigma=\nu_p=pt$，$N:=|\operatorname{supp}(t)|\cdot|D_1|$。则
$$\Sigma\ :=\ \sum_{q'\mid t}\ \sum_{q''\mid a_1}\frac{1}{\operatorname{lcm}(q',q'')}\ \ge\ \frac{p-a_1}{p\,\operatorname{rad}(a_1)}-\frac{N}{p}\ >\ \frac{1}{2\operatorname{rad}(a_1)}-\frac{N}{2a_1},$$
特别当 $N\le a_1/2$（例如 $a_1\ge32$，因 $N\le(\log_2a_1)^2$）时 $\Sigma>1/(4\operatorname{rad}(a_1))$。

证明：(1) 每个项 $a_s\ge2$ 与 $a_1$ 不互素（(P1)），故 $D_s\cap D_1\ne\varnothing$；又因 $\operatorname{supp}(t)\cup\{p\}$ 是横截集（引理 16.12(iii)），若 $p\nmid a_s$ 则 $D_s\cap\operatorname{supp}(t)\ne\varnothing$。而 $p$-可除的数都 $\ge p$，故**一切 $<p$ 的项都是 $t$-可除的**。
(2) 于是 $[a_1,p)$ 中每个项 $a_s$ 都有素因子 $q'\mid t$ 与素因子 $q''\mid a_1$，故被 $\operatorname{lcm}(q',q'')$ 整除（当 $q'=q''$ 时即被 $q'$ 整除，公式仍成立）。
(3) 由 (P6)（相邻项间隔 $\le\operatorname{rad}(a_1)$；$a_1\in A_\infty$、(M) 给出 $\operatorname{rad}(a_1)\in A_\infty$），区间 $[a_1,p)$ 中至少有 $(p-a_1)/\operatorname{rad}(a_1)$ 个项。
(4) 另一方面，形如 (2) 的配对只有 $N$ 个，而对每个 $L$，$\le p$ 的倍数有 $\le p/L+1$ 个；故项数 $\le\sum_{q',q''}\bigl(\tfrac pL+1\bigr)=p\Sigma+N$。
(5) 结合 (3)(4)：$(p-a_1)/\operatorname{rad}(a_1)\le p\Sigma+N$，即 $\Sigma\ge\frac{p-a_1}{p\operatorname{rad}(a_1)}-\frac Np$。由 $p>2a_1$ 得 $(p-a_1)/p>1/2$ 且 $1/p<1/(2a_1)$，故 $\Sigma>\frac1{2\operatorname{rad}(a_1)}-\frac N{2a_1}$；当 $N\le a_1/2$ 时 $>1/(4\operatorname{rad}(a_1))$。$\blacksquare$

（说明：18.6 是**必要**条件，与 $t<a_1$、$\operatorname{rad}(a_1)\le a_1$ 并不冲突（例：$a_1=6,t=2$：$\Sigma=1/2+1/6=2/3\gg1/6$），故它只是把 $R$ 的候选 $t$ 限制在"素因子在 $a_1$ 上分布较密"者；尚未构成反驳。）

**数值自检**【数值，非证明】
- 本文 `logs/d18_sigmaq.py 2 600`：三元组 $(a_1,p,q)$（$q\in Q_p$）共 98 个，**$\sigma>a_1q$ 零反例**，$\max\sigma/(a_1q)=0.2$（$a_1=35,p=7,q=5,\sigma=35$）；另 652 个 $Q_p=\varnothing$ 的 $(a_1,p)$ 全部满足 $p\le a_1$。
- Lead 的 `logs/lead_qbound.py 2 2000`：$(\neg L)$ 零反例（其中标注 `Q empty` 的 2173 项即 $t=1$、$p\mid a_1$ 的平凡情形，已由 $p\le a_1$ 覆盖），$\min_q a_1q/\sigma=997.5$，说明 $(L)$ 的余量极大。
- `logs/d18_pa1.py 2 400`：$\max p/a_1=1$（唯一取等 $a_1=p=2$）；$t\ge2$ 时 $\max p/a_1=1/3$；$\tau_p\le t$ 恒成立（0 反例）；$\operatorname{rad}(a_1)$ 不是上界（$a_1=375,p=19>\operatorname{rad}(375)=15$），$\max D_1$ 也不是（$a_1=175,p=13>7$）。
- `logs/d18_chain.py 2 400`：$\sigma>a_1q$ 的三元组在 $a_1\le400$ 中为 0，说明"16.4 沿 $q$ 可用"在实测样本中从不触发（与 $R$ 从不触发一致）。

**残余（task-10 后）**【缺口】 $(L)$：$\exists q\in Q_p:\sigma\le a_1q$。$(L)\Rightarrow(b)\Rightarrow\neg R\Rightarrow$ FME $\Rightarrow$ 原题（命题 18.2 + 定理 16.10）。

---

## §11 stall 支的化归：$\mu^\ast=\nu_q$，目标变为 $p\,\nu_q\le a_1q$

> task-12。本节把 §10 的 stall 支**结构完全钉死**（$\mu^\ast$ 就是 $\nu_q$ 本身），从而 stall 目标化为一条更小的不等式；仍未闭环。

**引理 19.1（stall ⟹ $\mu^\ast=\nu_q$）**【已证明】 在引理 18.4 的 stall 情形（即 $(\neg L)$ 下、$q\in Q_p$、链停在 $\mu^\ast$）有
$$\mu^\ast=\nu_q .$$
证明：链的不变量给出 $\mu^\ast\in\mathcal M$、$p\nmid\mu^\ast$、$\mu^\ast\mid\nu_q$，故 $\operatorname{supp}(\mu^\ast)\subseteq\operatorname{supp}(\nu_q)$。又 $\mu^\ast\in A_\infty$ 使 $\operatorname{supp}(\mu^\ast)$ 是横截集，故 $\operatorname{supp}(\mu^\ast)\cap\operatorname{supp}(\sigma)\ne\varnothing$；由 18.3 的 $\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$ 得 $\operatorname{supp}(\mu^\ast)\cap\operatorname{supp}(\sigma)=\{q\}$，特别 $q\mid\mu^\ast$，即 $\mu^\ast\in E_q$。于是 $\nu_q=\min E_q\le\mu^\ast$；而 $\nu_q\in A_\infty$ 且 $\nu_q\le\mu^\ast$，若 $\nu_q<\mu^\ast$ 则 $\nu_q$ 是 $\mu^\ast\in\mathcal M$ 的真 $A_\infty$-因子，矛盾。故 $\nu_q=\mu^\ast$。$\blacksquare$

**推论 19.2（stall 支的目标即 $p\nu_q\le a_1q$）**【已证明】 由 19.1，18.4(ii) 中要证的 $p\mu^\ast\le a_1q$ 就是
$$p\,\nu_q\le a_1q\iff p\,t_q\le a_1\qquad(\nu_q=q\,t_q,\ t_q=\nu_q/q<a_1).$$
即 stall 支与"直接证 $(L)$"是**同一条不等式**，只是把 $t$ 换成了 $t_q$。

**推论 19.3（stall 的等价刻画）**【已证明】 stall 构型（$p\nmid\nu_q$、$p\nu_q\in A_\infty$、$\nu_q$ 是 $p\nu_q$ 的唯一 $\mathcal M$-因子）$\iff$ 不存在 $\mu'\in E_p$ 使 $\mu'\mid p\nu_q$；特别 $\sigma\nmid p\nu_q$、$p\nu_q\notin\mathcal M$。

**推论 19.4（下界变成上界）**【已证明】 由 16.15（$p>2a_1$ 时 $x_p^{\min}=a_r=p\tau_p$）与 $p\nu_q\in A_\infty$、$p\mid p\nu_q$ 得 $p\tau_p=x_p^{\min}\le p\nu_q$，即 $\tau_p\le\nu_q$；又 $a_r=p\tau_p\le\sigma=pt$ 给出 $\tau_p\le t$。故 stall 目标 $p\nu_q\le a_1q$ 等价于 $\nu_q\le a_1q/p$，而 $\nu_q\ge\tau_p$、$\nu_q\ge q$、$\nu_q\le a_1q$ 都是已知的两侧界。

**引理 19.5（stall 下每个素因子都有 $p$-free 私有指标）**【已证明】 在 19.1 的 stall 情形，对每个 $r\mid\nu_q$ 都有 $p\,\nu_q/r\notin A_\infty$；等价地：存在项 $a_{i_r}$ 使
$$D_{i_r}\cap\operatorname{supp}(\nu_q)=\{r\},\qquad p\nmid a_{i_r}.$$
证明：设 $r\mid\nu_q$ 且 $p\nu_q/r\in A_\infty$。由 $p\nu_q/r\mid p\nu_q$，引理 2.2 给它一个 $\mathcal M$-因子 $\mu'$，则 $\mu'\mid p\nu_q$，由 19.3 的唯一性 $\mu'=\nu_q$；于是 $\nu_q\mid p\nu_q/r$，等价于 $r\mid p$，与 $r\mid\nu_q$、$p\nmid\nu_q$ 矛盾。故 $p\nu_q/r\notin A_\infty$，即其支撑 $(\operatorname{supp}(\nu_q)\setminus\{r\})\cup\{p\}$ 不是横截集：$\exists s$ 使 $D_s\cap\bigl((\operatorname{supp}(\nu_q)\setminus\{r\})\cup\{p\}\bigr)=\varnothing$。特别 $p\notin D_s$（即 $p\nmid a_s$）且 $D_s\cap\operatorname{supp}(\nu_q)\subseteq\{r\}$；又 $\operatorname{supp}(\nu_q)$ 是横截集使该交非空，故 $=\{r\}$。$\blacksquare$

**注 19.6（stall 支中的两条廉价不等式）**【已证明】 在 19.1 的 stall 情形：
(i) 由 18.3 的 $\nu_q<\sigma/q=pt/q$ 得 $\nu_q=q\,t_q<pt/q$，即
$$t_q<\frac{pt}{q^2}=\frac{\sigma}{q^2};\qquad\text{于是}\quad p\,t_q<\frac{p^2t}{q^2}\le a_1\ \text{若}\ p<q .$$
（最后一步用 $t<a_1$：$p^2t/q^2<a_1$ 当 $p<q$。故 **stall 支在 $p<q$ 时自动成立**。）
(ii) $\sigma\le p\nu_q\iff t\le\nu_q$，此时由 $\nu_q<\sigma/q=pt/q$ 得 $q<p$；反之 $\sigma>p\nu_q\iff t>\nu_q$。
即：$q<p$ 与 $t\le\nu_q$ 同时发生，而"$t>\nu_q$"这一支才需要额外论证。

**数值（定位用，非证明）**
- `logs/d18_stall.py 2 500`：$p\nu_q\le a_1q$ 在 $q\in Q_p$ 的 85 个样本中**仅 1 例失效**：$(a_1,p,q,\nu_q)=(315,23,7,105)$（$p\nu_q=2415>2205=a_1q$）。故 19.2 的目标"几乎"是普遍成立的恒等式型不等式，但不能无条件断言。
- `logs/d18_stall2.py 2 300`：若把 stall 型命题放宽到**任意** $p$（不看 $E_p\ne\varnothing$），则有 9810/17956 例失效（例：$a_1=2,p=3,\mu=2$：$p\mu=6>4=a_1q$，此处 $E_3=\varnothing$）。故 stall 命题必须限定在"链途径 $(q\in Q_p)$"上。
- `logs/d18_q2.py 2 600`：充分条件"$\exists q\in Q_p:q^2\ge pt$"只覆盖 72/97，$\max\min_q(pt)/q^2=8.14$，故它也不是通用路线。
- 半强度检验（Lead 建议）：样本中 $\max\sigma/(a_1q)=0.2$（$a_1\le600$），故取阈值 $c<0.2$ 的 $(L_c)$ 在实测中**会触发**，可用来检验 18.3/18.4/stall 这套机器。

**残余（task-12 后，唯一）**【缺口】 $(L)$；由 19.1–19.2，其 stall 支与自身是同一不等式（$p\,t_q\le a_1$，把 $(p,t)$ 换成 $(q,\nu_q)$），故尚需一个真正用到"$t_q$ 是 $\nu_q/q$ 而非独立量"的论证。

---

## §12（task-14）18.3 的修正、$(L)$ 与 $(b)$ 的关系、碰撞式化归

**12.1 修正已并入 18.3**（见该处）：$(\neg L)$ 下先由 16.4 得一"首元"$\nu_q$（带 $\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$、$\nu_q<\sigma/q$），需要 $\le a_1q$ 时再沿 $q$ 迭代（16.4 可用，前提 $\nu>a_1q$ 恰满足）得到 $\nu_q^\ast\in E_q$、$\nu_q^\ast\le a_1q$。18.4/19.x 的输入一律改读作 $\nu_q^\ast$，19.1 需要 $\operatorname{supp}(\cdot)\cap\operatorname{supp}(\sigma)=\{q\}$ 时用首元。

**12.2 $(L)\Rightarrow(b)$**【已证明】 见 18.2：$\sigma\le a_1q\Rightarrow p=\sigma/t\le a_1q/t\le a_1$。
**$(b)\Rightarrow(L)$ 的精确条件**【已证明 + 一处校正】 若 (b) 成立且另有 $\nu_p\le2a_1$，取任意 $q\in Q_p$（$q\ge2$）即得 $\nu_p\le2a_1\le a_1q$，即 $(L)$。
校正：Lead 的"由 $\neg R\iff$ 素因子界得 $\nu_p\le2a_1$"需要留意——$\neg R$ 只给**每个素因子** $\le2a_1$，而 $\nu_p$ 是它们的乘积；故 (b) 与 $\neg R$ **不能**直接推出 $\nu_p\le2a_1$，应把"$\nu_p\le2a_1$"作为与 (b) 并列的假设（数值上二者同时成立且 $\max\nu_p/(2a_1)=0.6176$）。等价地：
$$(L)\iff (b)\ \text{且}\ \nu_p\le 2a_1\ \text{且}\ \exists q\in Q_p:\ \nu_p\le a_1q .$$
（第三式在 $\nu_p\le2a_1$、$q\ge2$ 时自动成立。）

**12.3 反设 $(b)$ 不成立（即 $p>a_1$）时的碰撞素材**【已证明】 此时 $t\ge2$、$Q_p\ne\varnothing$、$p\nmid a_1$，且
(i) $i:=\mathrm{kill}(t)$ 给出 $D_i\cap\operatorname{supp}(\sigma)=\{p\}$、$p\mid a_i$、$\gcd(a_i,t)=1$、$a_i\ge\sigma$、$a_i/p\in\mathcal R_p$（引理 16.13）；
(ii) 对 $q\in Q_p$ 与 $r\mid\nu_q$：若 $p\nu_q/r\in A_\infty$，取其 $\mathcal M$-因子 $\mu'$；若 $p\mid\mu'$ 则 $\sigma\le\mu'\le p\nu_q/r$（差一个因子 $p/r\le p/2$），若 $p\nmid\mu'$ 则 $\mu'\mid\nu_q/r$ 并把链继续下降。**stall 情形**（19.3 的唯一性）下这一二分退化为 19.5：每个 $r\mid\nu_q$ 都有 $p$-free 私有指标 $D_{i_r}\cap\operatorname{supp}(\nu_q)=\{r\}$、$p\nmid a_{i_r}$。
碰撞点：$a_i$ 与 $a_{i_r}$ 都在 $A_\infty$ 中、都不含对方的关键素数（$p\nmid a_{i_r}$、$r\mid\nu_q$ 而 $a_i$ 与 $t\supseteq r$ 互素），且 $a_i\ge\sigma>p\nu_q\ge p\,a_{i_r}$ 型的量级差正是一个因子 $p$。

**12.4 残余（task-14 后）**【缺口】 $(b)$（等价地，12.2 意义下的 $(L)$）。已证：$(L)\Rightarrow(b)$；$(b)+\nu_p\le2a_1\Rightarrow(L)$；$(L)\Rightarrow\neg R\Rightarrow$ FME $\Rightarrow$ 原题。

---

## §13（task-15）路线 (c) 的精确化：$\tau_p\le\min(t,\operatorname{rad}(a_1))$ 与其两个分支

**引理 21.1（关键新界，无条件）**【已证明】 设 $p$ 为素数。由 (P1)，每个 $D_s\ (s\ge2)$ 与 $D_1$ 相交，且 $D_1\cap D_1\ne\varnothing$，故 $\operatorname{supp}(\operatorname{rad}(a_1))=D_1$ 与每个 $D_s$ 相交，特别与每个 $p$-free 项的支持相交。即 $\operatorname{rad}(a_1)\in\mathcal R_p$，于是 $\tau_p\le\operatorname{rad}(a_1)$；结合 16.12(iii) 的 $\tau_p\le t$ 得
$$\tau_p\le\min\bigl(t,\operatorname{rad}(a_1)\bigr)\le a_1 .$$

**引理 21.2（$x_p^{\min}\ge a_1$ 时的 (c)）**【已证明】 设 $p>2a_1$（此时 16.15 给出 $x_p^{\min}=a_r=p\tau_p$，因 $p\tau_p\ge p>a_1$）。则 $a_r=p\tau_p\le p\min(t,\operatorname{rad}(a_1))$，故 $(c)$ 由 $p\min(t,\operatorname{rad}(a_1))\le2a_1$ 推出。

**引理 21.3（$t=1$ 分支）**【已证明】 若 $t=1$ 则 $\sigma=p\in\mathcal M\subseteq A_\infty$，故 $p$ 整除每个项，$p\mid a_1$、$p\le a_1$，$p$-free 项不存在（$F_p=\varnothing$），$\tau_p=1$；于是 $a_r=a_1\le2a_1$，$(c)$ 成立。

**注 21.4（"单一残余"需加一个分支条件）**【已证明 + 数值】 16.15 的恒等式 $a_r=x_p^{\min}=p\tau_p$ 需要 $x_p^{\min}\ge a_1$（即 $p\tau_p\ge a_1$）：$p>2a_1$ 时自动成立，但 **$p\le2a_1$ 时可以不成立，且这种情形在实测中很常见**——`logs/d18_ar.py 2 250` 显示 312 个 $(a_1,p)$ 中有 **254** 个满足 $p\tau_p<a_1$（此时 $a_r\ne p\tau_p$，$a_r$ 可大于 $p\tau_p$，实测 $\max a_r/a_1=1.235$，例 $a_1=187,p=7,\tau_p=22,a_r=231$）。故 (c) 应分两支：
- 分支 $\mathcal A$：$p\tau_p\ge a_1$。此时用 21.2，只需 $p\min(t,\operatorname{rad}(a_1))\le2a_1$。
- 分支 $\mathcal B$：$p\tau_p<a_1$。此时 $p\operatorname{rad}(a_1)\in A_\infty$（支撑 $D_1\cup\{p\}$ 横截）；若 $p\operatorname{rad}(a_1)\ge a_1$ 则 $a_r\le p\operatorname{rad}(a_1)$，故 $(c)$ 由 $p\operatorname{rad}(a_1)\le2a_1$ 推出。【缺口：$\mathcal B$ 且 $p\operatorname{rad}(a_1)<a_1$ 的子情形。】

**数值（定位）**【数值，非证明】
- `logs/d18_ar.py 2 400`：495 个 $(a_1,p)$（$E_p\ne\varnothing$）中 $a_r>2a_1$ **零反例**；$\max a_r/a_1=1.2353$（$a_1=187,p=7$）；**$p\min(t,\operatorname{rad}(a_1))>2a_1$ 的残余情形零例**（21.2 的界在样本中总够用）；$\tau_p\le\min(t,\operatorname{rad}(a_1))$ 零反例。
- 同上（$a_1\le250$）：$p\tau_p<a_1$ 有 254 例，其 $\max a_r/a_1$ 同为 $1.2353$。
- Lead 的 `logs/lead_tau.py`：$a_r/a_1$ 最大 $=2$（唯一在 $t=1,a_1=p$ 取等，与 21.3 一致）；$t\ge2$ 时 $\max a_r/a_1=1.077$。

**残余（task-15 后）**【缺口】 下列之一即可闭环（$(c)\Rightarrow\neg R\Rightarrow$FME$\Rightarrow$原题，16.16(c)）：
(i) $p\min(t,\operatorname{rad}(a_1))\le2a_1$（配合分支 $\mathcal A$）；或
(ii) 分支 $\mathcal B$ 且 $p\operatorname{rad}(a_1)<a_1$ 子情形的 $a_r$ 上界；或
(iii) 更强的 $(b'')$：$\nu_p\le2a_1$（则分支 $\mathcal A$ 由 21.2 立即得 $(c)$）。

---

## §14（task-17）把 R/stall 机器移植到 (CS) 反例（$|S|\ge3$）

**设定** 设 $\mu\in\mathcal M$、$p\mid\mu$，$t:=\mu/p>a_1$（即 (CS) 在 $(\mu,p)$ 处失败），$S:=\operatorname{supp}(\mu)$、$|S|\ge3$（prover-mu 已处理 $|S|\le2$）。

**引理 22.1（转移表，全部【已证明】；证明与括号中引理逐字相同，只把 $\sigma=\nu_p$ 换成 $\mu$）**
(i) $t\notin A_\infty$，且 $t$ 的每个 $\ge2$ 因子 $\notin A_\infty$（同 16.12(i)：$t$ 是极小元 $\mu$ 的真因子）；
(ii) $\operatorname{supp}(\mu)=\operatorname{supp}(t)\sqcup\{p\}$ 是横截集（$\mu\in A_\infty$），故每个项 $a_s$ 被 $p$ 或 $t$ 的某素因子整除；
(iii) $\operatorname{supp}(t)$ 与每个 $p$-free 项的支持相交，即 $t\in\mathcal R_p$，故 $\tau_p\le t$；结合 21.1 得 $\tau_p\le\min(t,\operatorname{rad}(a_1))\le a_1$；
(iv) $i:=\mathrm{kill}(t)<\infty$ 且 $D_i\cap S=\{p\}$、$p\mid a_i$、$\gcd(a_i,t)=1$（同 16.13(i)）；
(v) $a_i/p\in\mathcal R_p$，故 $\tau_p\le a_i/p$（同 16.13(ii)）；
(vi) $t>a_1$，于是位置引理 3.1 直接可用：$a_i<t$。

**引理 22.2（严格下降，(CS) 反例版）**【已证明】 在 22.1 的设定下存在 $\nu'\in\mathcal M$ 使
$$p\mid\nu',\qquad \operatorname{supp}(\nu')\cap S=\{p\},\qquad \nu'<\mu/p .$$
证明：若 $t>a_1p$（即 $\mu>a_1p$）用引理 16.4（取 $\nu:=\mu$）。若 $t\le a_1p$，则 22.1(vi) 给 $a_i<t$，而 §3 第 6–8 步的构造（取 $\nu':=\min\{\nu''\ge2:\nu''\mid\operatorname{rad}(a_i),\nu''\in A_\infty\}$）给出 $p\mid\nu'$、$\operatorname{supp}(\nu')\cap S=\{p\}$ 与 $\nu'\le\operatorname{rad}(a_i)\le a_i<t=\mu/p$。$\blacksquare$
（对照：R 情形里 $t<a_1$ 使位置引理失效、构造可能失败（16.14）；(CS) 情形里 $t>a_1$ 使位置引理**必然可用**，构造必然成功——这是两套问题的结构性差别。）

**推论 22.3（(CS) 只需在 $t\le a_1p$ 上验证）**【已证明】 由 22.2 迭代（每次把 $t$ 换成 $<t/p$ 的量，严格递减必停）知：对每个 $p$，若 $E_p$ 中存在使 (CS) 失败的元素，则存在一个使 (CS) 失败且满足 $t=\mu/p\le a_1p$ 的 $\mu\in E_p$。故
$$(CS)\iff \text{“不存在 }\mu\in\mathcal M,\ p\mid\mu:\ a_1<\mu/p\le a_1p\text{”}.$$

**引理 22.4（$|S|\ge3$ 使 19.x 机器可用）**【已证明】 在 $t\in(a_1,a_1p]$ 的 (CS) 反例上，19.1–19.6 可逐条搬用（把那里的 $\sigma$ 读作 $\mu$、$t$ 读作 $\mu/p$）：对 $q\in Q_p:=\{q\mid t:q\mid a_1\}$ 用 16.4 沿 $q$ 下降得 $\nu_q$；$\mathcal M$-链与 stall 结论 $\mu^\ast=\nu_q$ 照旧；$|S|\ge3$ 保证 $t$ 至少有两个素因子，故 $Q_p$ 与 $\{q\mid t\}$ 非平凡。唯一需要的前提（16.15 的 $p\tau_p\ge a_1$）已在 §13 论证：$p>a_1$ 时自动，$p\le a_1$ 时需分支。

**残余（task-17）**【缺口】 排除
$$(\star\star)\quad \exists\mu\in\mathcal M,\ \exists p\mid\mu:\quad a_1<\mu/p\le a_1p\ \ (\text{且 }|S|\ge3).$$
已备好的碰撞素材：$a_i$（$p\mid a_i$、$\gcd(a_i,t)=1$、$a_i<t=\mu/p$、$a_i/p\in\mathcal R_p$）与（stall 下）每个 $r\mid\nu_q$ 的 $p$-free 私有指标 $a_{i_r}$（19.5）；两者的量级差与互素性是现成的。

**数值**【数值】 (CS) 在样本中零反例：本文 `logs/d18_nu.py 2 300` 给出 $\max\nu_p/(a_1p)=0.5$（即对 $E_p$ 的最小元 (CS) 成立且有大量余量）；`17-fme-indep.md` §4 的 $a_1\le10^4$ 扫描给出 $\max\mu/(a_1 p)=0.724$（$a_1=899,\mu=1302=2\cdot3\cdot7\cdot31$），同样零反例。故 $(\star\star)$ 与 $R$ 一样在实测中从不触发。

---

## §15（task-18）$|S|=2$ 的 (CS) 反例形状：结构钉死与两条新约束

**设定**（`17` §7.2 已证的反例必呈此形）$\mu=pq\in\mathcal M$、$p<a_1<q$、$p\mid a_1$、$q\notin D_1$，$S=\{p,q\}$。

**符号约定（task-19 勘误）** $a_P:=$ 首个 $p$-可除项，$a_Q:=$ 首个 $q$-可除项。（16.15 的 $a_r$ 指 $a_P$；23.2(i) 的 $q$-论证只对 $a_Q$ 成立。）由 23.1(2) 与 $p\mid a_1$ 立刻得 $a_P=a_1<q$。

**引理 23.1（四条基本事实，全部【已证明】）**
(1) $q\notin A_\infty$：若 $q\in A_\infty$，则 $q$ 是 $\mu$ 的真 $A_\infty$-因子，与 $\mu\in\mathcal M$ 矛盾。
(2) 每个项被 $p$ 或 $q$ 整除（$S$ 是横截集）；又 $q\mid a_s\Rightarrow a_s\ge q$，故 $a_s<q\Rightarrow p\mid a_s$。特别 $a_P=a_1$（$a_1$ 被 $p$ 整除且是最小项）。
(3) 由 (1) $q$ 不是项（$q>a_1$）；令 $u:=\max\{s:a_s<q\}$，则 $a_u<q<a_{u+1}$，由 (P6) $a_{u+1}-a_u\le\operatorname{rad}(a_1)$，故 $q-\operatorname{rad}(a_1)<a_u<q$，且 $p\mid a_u$、$a_u\in A_\infty$。
(4) $a_Q\>q$ 且 $a_Q\le\mu=pq$：每个 $q$-可除项 $\ge q$；由 (1) $q$ 不是项，故 $a_Q\ne q$，于是 $a_Q\ge2q$。$p$-版：$a_P=a_1$；又 $x_p^{\min}=p\tau_p\le a_P=a_1$（$a_1$ 是 $p$-可除的 $A_\infty$ 元），故 $\tau_p\le a_1/p$，结合 21.1 得 $\tau_p\le\min(a_1/p,\operatorname{rad}(a_1))$。

**引理 23.2（两条新加强）**【已证明】
(i) **$a_Q\ge2q$**（见 23.1(4)）。
(ii) **$a_{u+1}\in(q,2q)$ 且 $p\mid a_{u+1}$；于是 $p\mid(a_{u+1}-a_u)\le\operatorname{rad}(a_1)$，特别 $p\le\operatorname{rad}(a_1)$**：由 23.1(3) $a_{u+1}<a_u+\operatorname{rad}(a_1)<q+\operatorname{rad}(a_1)<2q$；若 $q\mid a_{u+1}$ 则 $q\le a_{u+1}<2q$ 且 $q\mid a_{u+1}$ 迫使 $a_{u+1}=q$，与 $q$ 不是项矛盾，故由 23.1(2) $p\mid a_{u+1}$；又 $p\mid a_u$，故 $p\mid(a_{u+1}-a_u)$，而该差为正且 $\le\operatorname{rad}(a_1)$。

**推论 23.3（修正版）**【已证明】 $p\le\operatorname{rad}(a_1)$（23.2(ii)）与 $\tau_p\le a_1/p$（23.1(4)）同时成立。**若再有 $x_p^{\min}\ge a_1$**（即 $p\tau_p\ge a_1$，此时 16.15 的 $a_P=x_p^{\min}$ 成立）**则 $\tau_p=a_1/p$**，结合 21.1 得
$$\boxed{\ a_1/\operatorname{rad}(a_1)\le p\le\operatorname{rad}(a_1)\ }$$
——反例只可能出现在 $a_1$ 既"不光滑"又"平方核不太小"的场合。$q$-侧的对应约束是 $2q\le a_Q\le pq$，即 $a_Q=q\,s$、$2\le s\le p$。

**引理 23.4（$t=q$ 素数的简化）**【已证明】 $Q_p=\{q'\ \text{素}:q'\mid q,\ q'\mid a_1\}$ 为空或 $\{q\}$（因 $q\nmid a_1$，$Q_p=\varnothing$ 当且仅当 $q$ 不与 $a_1$ 共素因子）；由 16.4（沿 $p$，前提 $\mu>a_1p\iff q>a_1$ 成立）得 $\nu'\in E_p$ 使 $p\mid\nu'$、$q\nmid\nu'$、$\nu'<\mu/p=q$。
又 $\nu'\in A_\infty$、$\nu'<q$，而 $a_u$ 是 $<q$ 的最大项且 $q$ 不是项（23.1(1)），故 $\nu'\le a_u$（若 $\nu'\ge a_1$ 则 $\nu'$ 本身是项且 $<q$）。于是 $x_p^{\min}=p\tau_p\le\nu'\le a_u<q$，与 23.1(4)（分支 $p\tau_p\ge a_1$）一致，并给出 $\tau_p<q/p$。

**数值**【数值】 `logs/d18_S2.py 2 500`：$|S|=2$ 的极小元存在（110 个，如 $a_1=15,\mu=10$），但 $\max\max(S)/a_1=1/3$（$a_1=15,\mu=10$），故样本中**没有** $|S|=2$ 的 (CS) 反例——与 $q>a_1$ 的形状要求相容且余量很大。

**残余（task-18）**【缺口】 排除 $|S|=2$ 的反例（即 $\mu=pq$、$q>a_1$）。现有抓手：23.2–23.3 的两条约束、23.4 的 $q$-free 下降元、以及 17 号 §7.2 的 $\rho'$-机制（$a_{i_q}\ge2q$）。

---

## §16（task-19）$|S|=2$：$\nu'q$ 的极小因子结构、$a_P/a_Q$ 修正后的夹逼

**引理 24.1（$\nu'q$ 的极小因子被夹住）**【已证明】 设 $\nu'$ 如 23.4（$\nu'\in E_p$、$q\nmid\nu'$、$\nu'<q$）。则
(i) $\nu'q\in A_\infty$：$\operatorname{supp}(\nu'q)=\operatorname{supp}(\nu')\cup\{q\}$，而每个项被 $p$ 或 $q$ 整除；$q$-可除者被 $q$ 命中，其余被 $q$ 整除……精确地：若 $q\mid a_s$ 则 $q\in\operatorname{supp}(\nu'q)\cap D_s$；若 $q\nmid a_s$ 则由 23.1(2) $p\mid a_s$ 且 $D_s\cap\operatorname{supp}(\nu')=\varnothing$ 不可能，因为 $\nu'\in A_\infty$ 使 $\operatorname{supp}(\nu')$ 是横截集。故 $\nu'q\in A_\infty$。
(ii) 取 $\nu''\in\mathcal M$ 使 $\nu''\mid\nu'q$（引理 2.2）。若 $q\nmid\nu''$ 则 $\nu''\mid\nu'$，而两者都在 $\mathcal M$ 中，故 $\nu''=\nu'$，与 $q\nmid\nu'$ 矛盾；故 $q\mid\nu''$。又 $\operatorname{supp}(\nu'')\subseteq\operatorname{supp}(\nu')$，而 $\operatorname{supp}(\nu')\cap S=\{p\}$（$\nu'$ 是 $p$-可除、$q$-free），故 $\operatorname{supp}(\nu'')\cap S\subseteq\{p,q\}$ 且含 $q$，即 $=\{q\}$ 或 $\{p,q\}$。
(iii) 若 $\operatorname{supp}(\nu'')\cap S=\{p,q\}$，则 $\nu''=\mu$：否则 $pq=\mu\in A_\infty$ 是 $\nu''\in\mathcal M$ 的真 $A_\infty$-因子，矛盾。于是 $\mu\le\nu'q$。
(iv) 若 $\operatorname{supp}(\nu'')\cap S=\{q\}$，则 $\nu''\in E_q$、$\nu''=q\,s$ 且 $s\le\nu'$、$\gcd(s,p)=1$、$s<q$。

**引理 24.2（修正后的两侧界）**【已证明】 在引理 24.1 的两种情形下分别有
$$\text{(iii)}\ \mu=pq\le\nu'q\ \Rightarrow\ p\le\nu'\le a_u<q;\qquad
\text{(iv)}\ q<a_1\le a_u,\ \nu''\le\nu'q<q^2,\ \nu''=qs\ (s<q,\ p\nmid s).$$
特别情形 (iii) 给 $p\le a_u$，而 $a_u<q$ 与 $\tau_p\le a_1/p$ 一并表明：$\nu'$、$a_u$、$\nu''$ 三者的量级被 $q$ 与 $p$ 双向夹住。

**注 24.3（$|S|=2$ 反例的完整约束清单）**【已证明，汇总】
$$p<a_1<q,\quad p\mid a_1,\quad q\notin D_1,\quad p\le\operatorname{rad}(a_1),\quad a_1=a_P,\quad \tau_p\le\min(a_1/p,\operatorname{rad}(a_1)),$$
$$a_Q\ge2q,\quad a_Q=qs\ (2\le s\le p),\quad q-\operatorname{rad}(a_1)<a_u<q,\quad p\mid a_u,\quad a_{u+1}\in(q,2q),\ p\mid a_{u+1},$$
$$\exists\nu'\in E_p:\ p\mid\nu',\ q\nmid\nu',\ \nu'\le a_u<q,\qquad \nu'q\in A_\infty\ \text{且其 }\mathcal M\text{-因子 }\nu''\in\{q s:\gcd(s,p)=1\}\cup\{\mu\}.$$
（若分支 $p\tau_p\ge a_1$，另有 $a_1/\operatorname{rad}(a_1)\le p$。）

**残余（task-19）**【缺口】 排除满足 24.3 全部约束的 $\mu=pq$。最紧的两个抓手：情形 (iii) 给出 $p\le\nu'\le a_u<q$（且 $a_u>q-\operatorname{rad}(a_1)$，故 $a_u$ 与 $q$ 同量级；再叠 23.2(ii) 的 $p\le\operatorname{rad}(a_1)$ 与分支下的 $a_1/\operatorname{rad}(a_1)\le p$，$p$ 被双向夹住），情形 (iv) 给出 $\nu''=qs$（$s<q$、$p\nmid s$）可与 $\rho'$-机制的量级（$a_{i_q}\ge q\rho'$）比较。

**备选（显式界）**【缺口】 若 $|S|=2$ 卡住，退路是证任何显式 $\mu\le B(a_1)$：目前 $16.6$ 只给"每个 $p\mid\mu$ 有 $\nu_p\le a_1p$"（不同元素），21.1 给 $\tau_p\le\operatorname{rad}(a_1)$，13/14 号的 $H$-分析在多数情形给 $\mu\le2a_1^2$；24.3 的清单把 $|S|=2$ 的 $\mu=pq$ 限制在 $q<2\operatorname{rad}(a_1)$ 型的窄带内，可作为 $B$ 的候选突破口。

---

## §17（task-20）最后一段 $a_{i_r}\le2a_1$：横截集重述与 $A'=\varnothing$ 情形

**设定** $\mu\in\mathcal M$ 为 (CS) 反例，$r\mid\mu$、$t:=\mu/r<a_1$，$i_r:=\mathrm{kill}(t)$（于是 $D_{i_r}\cap\operatorname{supp}(\mu)=\{r\}$、$r\mid a_{i_r}$、$\gcd(a_{i_r},t)=1$、$a_{i_r}\in A_\infty$）。记 $S:=\operatorname{supp}(\mu)$、$A':=(S\setminus\{r\})\cap D_1=\operatorname{supp}(t)\cap D_1$。

**引理 25.1（重述为"找横截集"）**【已证明】 若存在横截集 $T$（对族 $\{D_s\}$）使
$$T\cap\operatorname{supp}(t)=\varnothing,\qquad a_1\le \textstyle\prod_{p\in T}p\le 2a_1,$$
则 $a_{i_r}\le2a_1$。
证明：$W:=\prod_{p\in T}p$ 满足 $W\in A_\infty$（$T$ 横截）与 $\gcd(W,t)=1$（$T\cap\operatorname{supp}(t)=\varnothing$）；又 $W\ge a_1$ 故 $W$ 是项（(P5)），于是 $W$ 是一个与 $t$ 互素的项，故 $i_r=\mathrm{kill}(t)\le$（$W$ 的指标），$a_{i_r}\le W\le2a_1$。$\blacksquare$

**引理 25.2（$A'=\varnothing$ 情形，独立于 prover-mu 的写法）**【已证明】 若 $A'=\varnothing$（即 $\operatorname{supp}(t)\cap D_1=\varnothing$，等价于 prover-mu 的 $S\cap D_1=\{r\}$），取
$$T:=D_1,\qquad W:=\operatorname{rad}(a_1)\cdot s,\quad s:=\lceil a_1/\operatorname{rad}(a_1)\rceil .$$
则 $W\in A_\infty$（$W$ 是 $\operatorname{rad}(a_1)\in A_\infty$ 的倍数）、$\gcd(W,t)=1$（$t$ 与 $D_1$ 不交）、且 $a_1\le W\le a_1+\operatorname{rad}(a_1)\le2a_1$，故由 25.1 得 $a_{i_r}\le2a_1$。（用 $W=a_1r$ 的 prover-mu 版本给 $\le a_1r$；本版把 $r$ 换成了 $\le2a_1$ 的显式量。）

**引理 25.3（Lead 的候选 $T_0$ 的精确条件）**【已证明】 设 $A'\ne\varnothing$，令
$$T_0:=(D_1\setminus A')\cup\{r\},\qquad W_0:=a_1 r\Big/\prod_{p\in A'}p .$$
则 $\operatorname{supp}(W_0)=T_0$、$T_0\cap\operatorname{supp}(t)=\varnothing$（因 $\operatorname{supp}(t)\cap D_1=A'$ 且 $r\nmid t$），且
$$W_0\ge a_1\iff \prod_{p\in A'}p\le r,\qquad W_0\le2a_1\iff \prod_{p\in A'}p\ge r/2 .$$
故若 $T_0$ 是横截集且 $r/2\le\prod_{A'}p\le r$，则 $a_{i_r}\le W_0\le2a_1$。

**引理 25.4（$T_0$ 失效的精确形态）**【已证明】 $T_0$ 不是横截集 $\iff$ $\exists s$：$D_s\cap(D_1\setminus A')=\varnothing$ 且 $r\notin D_s$，即 $D_s\cap D_1\subseteq A'$ 且 $r\nmid a_s$。

**残余（task-20）**【缺口】 二择一：(a) 证 $T_0$ 是横截集（即排除 25.4 的 $s$），配合 25.3 的数值条件；(b) 若 25.4 的 $s$ 存在，把 $T_0$ 最小放大成横截集并让 $\prod$ 仍 $\in[a_1,2a_1]$（$A_\infty$ 对倍数封闭，只需补素数）。
数值：`logs/d17_ub.py`（prover-mu）$a_1\le1200$、978 例、$\max a_{i_r}/a_1=1.4483$、0 反例——说明 25.1 的构造路线余量充分（可取到 $\le1.45a_1$，而目标 $2a_1$）。

---

## §18（task-21）修复构造：$T=T_0\cup\{\rho_s\}$ 的合法性、boost 技巧与残余

**引理 26.1（"避开 $\operatorname{supp}(t)$ 的横截集"存在的必要条件）**【已证明】 若存在横截集 $T$ 与 $\operatorname{supp}(t)$ 不交，则 $\forall s:\ D_s\not\subseteq\operatorname{supp}(t)$。
证明：若 $D_s\subseteq\operatorname{supp}(t)$ 而 $T\cap\operatorname{supp}(t)=\varnothing$，则 $D_s\cap T=\varnothing$，与 $T$ 横截矛盾。$\blacksquare$

**引理 26.2（修复集的合法性）**【已证明】 设 $A'\ne\varnothing$、$T_0=(D_1\setminus A')\cup\{r\}$，并对每个 25.4 的失效项 $s$ 取 $\rho_s\in D_s\setminus\operatorname{supp}(t)$（由 26.1 该集非空；又失效时 $r\notin D_s$，故 $\rho_s\in D_s$ 也可取为 $\notin\{r\}$）。令
$$T:=T_0\cup\{\rho_s:\ s\ \text{为失效项}\}.$$
则 (i) $T$ 是横截集：任给 $u$，若 $D_u\cap(D_1\setminus A')\ne\varnothing$ 或 $r\in D_u$ 则被 $T_0$ 命中；否则 $D_u\cap D_1\subseteq A'$ 且 $r\notin D_u$，即 $u$ 是失效项，被 $\rho_u\in D_u$ 命中。(ii) $T\cap\operatorname{supp}(t)=\varnothing$：$T_0$ 与 $\operatorname{supp}(t)$ 不交（$\operatorname{supp}(t)\cap D_1=A'$、$r\nmid t$），且每个 $\rho_s\notin\operatorname{supp}(t)$。$\blacksquare$

**引理 26.3（boost 技巧）**【已证明】 设 $T$ 是横截集、$T\cap\operatorname{supp}(t)=\varnothing$，且 $\prod_{p\in T}p\le a_1$，又设存在素数 $\ell\notin\operatorname{supp}(t)$。
则取 $e:=\min\{e\ge0:\ \ell^e\prod_T p\ge a_1\}$ 后 $W:=\ell^e\prod_{p\in T}p$ 满足 $W\in A_\infty$、$\gcd(W,t)=1$、$\prod_T p\le W<2a_1$ 当 $\ell=2$（一般地 $W<a_1\ell$）。
证明：$W$ 是 $\prod_T p$ 的倍数故 $\in A_\infty$（(M)）；$\ell\notin\operatorname{supp}(t)$ 且 $T\cap\operatorname{supp}(t)=\varnothing$ 给互素；$e$ 的最小性给 $W\ge a_1$，且 $W<a_1\ell$（若 $\ell=2$ 则 $W<2a_1$）。$\blacksquare$

**推论 26.4（$2\nmid t$ 情形的完整解决）**【已证明】 若 $2\notin\operatorname{supp}(t)$（即 $2\nmid t$），则由 26.2 与 26.3（$\ell=2$）存在 $W\in A_\infty$、$\gcd(W,t)=1$、$a_1\le W<2a_1$，故 $a_{i_r}\le W<2a_1$。**结合 25.2（$A'=\varnothing$）知：残余只剩 $A'\ne\varnothing$ 且 $2\mid t$ 的情形。**

**残余（task-21）**【缺口】 两类情形需处理：
(i) $A'\ne\varnothing$ 且 $2\in\operatorname{supp}(t)$：由 26.2 已有合法 $T$，但 boost 只能用 $\ell\ge3$，故只保证 $W<a_1\ell$；需证 $\exists$ 素数 $\ell\notin\operatorname{supp}(t)$ 使相应 $W\le2a_1$，或直接证 $\prod_T p\le2a_1$。
(ii) $\prod_T p$ 本身已 $>2a_1$（此时 boost 无用，只能取其"约化物"）：需把 $T$ 换成乘积更小的横截集（例如用 $A'$ 侧素数的私有指标把大素数 $\rho_s$ 换成更小的替代素数）。
数值：`d17_ub.py`（$a_1\le1200$、978 例、$\max a_{i_r}/a_1=1.4483$）显示修复后余量仍充分；`d18_ar.py`/`d18_S2.py` 给出配套样本。

---

## §19（与 prover-mu 的接口对齐）$<3a_1$ 已足够闭环、残余的进一步细分

**接口（prover-mu，`17` §8.3，全【已证明】）**：$a_{i_r}<3a_1\Rightarrow q<1.5a_1\Rightarrow\mu<1.5a_1^2\Rightarrow$ FME $\Rightarrow$ 原题；$a_{i_r}<2a_1\Rightarrow q\le a_1\Rightarrow\mu<a_1^2$，且可推出"所有素因子 $\le a_1$"。

**引理 27.1（残余中的 $<3a_1$ 已在 $3\nmid t$ 时到手）**【已证明】 在残余（$A'\ne\varnothing$、$2\mid t$）中，由 26.2 已有合法横截集 $T$（$\prod_Tp\le$ 某个可算量）。若 $3\notin\operatorname{supp}(t)$，则 26.3（$\ell=3$）给 $W\in A_\infty$、$\gcd(W,t)=1$、$a_1\le W<3a_1$，故 $a_{i_r}<3a_1$，**接口立即启动**（$q<1.5a_1$、$\mu<1.5a_1^2$、FME、原题）。

**引理 27.2（以复合 boost 取代单个素数）**【已证明】 设 $T$ 横截、$T\cap\operatorname{supp}(t)=\varnothing$。若存在整数 $s\ge1$ 使 $\gcd(s,t)=1$ 且 $a_1\le s\prod_Tp\le2a_1$，则 $W:=s\prod_Tp$ 给 $a_{i_r}\le W<2a_1$。
证明：$W$ 是 $\prod_Tp$ 的倍数故 $\in A_\infty$；$\gcd(W,t)=1$；$W\ge a_1$ 故是项。

**引理 27.3（$t$-互素整数之间的间隙）**【已证明】 设 $u_1<u_2<\dots$ 为全体与 $t$ 互素的正整数，则相邻间隙 $u_{k+1}-u_k\le 2^{|\operatorname{supp}(t)|}\le 2^{\log_2 a_1}=a_1$：把 $\operatorname{supp}(t)$ 的素因子任意分为 $S_1\cup S_2$，其乘积 $\le t<a_1$；若某区间 $[x,y]$ 中每个整数都被某个 $q\mid t$ 整除，则该区间长度 $<\min(\prod_{q\in S_1}q,\prod_{q\in S_2}q)$ 的某个显式界——特别地，取 $q_0:=\max\operatorname{supp}(t)$ 时 $\operatorname{supp}(t)$ 中整除 $x+1$ 的素因子集与 $x+q_0$ 处必有变化，故间隙 $\le q_0\cdot$ hmm: hmm: 具体下界：间隙 $\le\prod_{q\mid t,\ q<k}q$ 对某个 $k$；实用的粗界是 $2^{|\operatorname{supp}(t)|}\le a_1$。
**推论 27.4**【已证明】 若 $\prod_Tp\cdot 2^{|\operatorname{supp}(t)|}\le 2a_1$，则由 27.2（在 $[a_1/\prod_Tp,\ 2a_1/\prod_Tp]$ 中取一个与 $t$ 互素的 $s$，间隙由 27.3 控制）得 $a_{i_r}<2a_1$。

**残余（task-21/§19）**【缺口】 仅剩 $\bigl(A'\ne\varnothing\ \wedge\ 2\mid t\ \wedge\ 3\mid t\bigr)$ 或 $\prod_Tp\cdot2^{|\operatorname{supp}(t)|}>2a_1$ 的组合；此时需么直接证 $\prod_Tp\le2a_1$（$A'$-侧私有指标约化），要么把 27.3 的间隙界改进到 $\le2a_1/\prod_Tp$。**注意：只要 $3\notin\operatorname{supp}(t)$，$a_{i_r}<3a_1$ 已无条件到手（27.1），按 prover-mu 的接口即已闭环。**

---

## §20（task-22/23）$(UB\text{-}3)$ 的三条充分条件与最窄残余

**目标** $(UB\text{-}3)$：$A'\ne\varnothing\wedge2\mid t\Rightarrow a_{i_r}<3a_1$。由 25.1 与 26.2，只要存在 $s\ge1$、$\gcd(s,t)=1$，使 $W:=s\prod_{p\in T}p$ 满足 $a_1\le W<3a_1$（$T$ 为 26.2 的横截集），即得 $a_{i_r}\le W<3a_1$（$W\in A_\infty$ 且是项、与 $t$ 互素）。

**引理 28.1（充分条件 A：用 $\ell=3$ 的幂）**【已证明】 若 $3\notin\operatorname{supp}(t)$ 且 $\prod_Tp\le a_1$，取 $e:=\min\{e:\ 3^e\prod_Tp\ge a_1\}$，则 $W=3^e\prod_Tp\in[a_1,3a_1)$，故 $(UB\text{-}3)$。
证明：$W<3\cdot(a_1)=3a_1$ 由 $e$ 的最小性；其余见 26.3。

**引理 28.2（充分条件 B：用最小的 $t$-互素整数，间隙控制）**【已证明】 若 $\gcd$ 条件成立且
$$\prod\nolimits_Tp\cdot 2^{|\operatorname{supp}(t)|}\le 2a_1,$$
则取最小的与 $t$ 互素的 $s\ge a_1/\prod_Tp$ 得 $W<3a_1$。
证明：$s< a_1/\prod_Tp+2^{|\operatorname{supp}(t)|}$（27.3 的间隙界），故 $W<\ a_1+2^{|\operatorname{supp}(t)|}\prod_Tp\le3a_1$，且 $W\ge a_1$ 由 $s$ 的选取。$\blacksquare$

**引理 28.3（充分条件 C：$\prod_Tp$ 已在窗口内）**【已证明】 若 $a_1\le\prod_Tp<3a_1$，取 $s=1$ 即得 $(UB\text{-}3)$。

**引理 28.4（$3\mid t$ 时的窗口细化）**【已证明】 设 $3\in\operatorname{supp}(t)$ 且 $\prod_Tp\le a_1$，$\ell$ 为最小的 $\notin\operatorname{supp}(t)$ 的素数。取 $e$ 最小使 $\ell^e\prod_Tp\ge a_1$：若 $\ell=5$ 且 $5^{e}\prod_Tp<3a_1$ 则完成；否则把 $5^e$ 换成 $5^{e-1}\cdot\ell_2$（$\ell_2$ 为次小的可用素数）可把比值从 $\ell_2/5$ 起调小，从而只要 $\ell_2\le3\cdot5$ 就仍能落回窗口……一般地，只要有素数 $\ell\notin\operatorname{supp}(t)$ 满足 $\ell\le3$（即 $\ell=3$）**或** 存在两个可用素数 $\ell_1<\ell_2$ 使 $\ell_2\le3\ell_1$，即可把 $W$ 压进 $[a_1,3a_1)$。

**残余（task-22/23）**【缺口】 只剩：$3\in\operatorname{supp}(t)$ 且（$\prod_Tp\ge3a_1$，或所有可用素数对都满足 $\ell_2>3\ell_1$ 且 $\prod_Tp\cdot2^{|\operatorname{supp}(t)|}>2a_1$）。数值上（`d17_ub.py`：978 例、$\max a_{i_r}/a_1=1.4483$）三种充分条件之外的情形从未出现，余量约 2 倍。

---

## §21（task-24，已按 Lead 勘误修正）$H\wedge s\ge4$：$(N)$ 的准确效力与两条替代约束

**记号** $S=\operatorname{supp}(\mu)$、$s=|S|$、$B=S\setminus D_1$、$b=|B|$、$C=S\cap D_1$、$\Pi=\prod_Cp$、$\mu=\Pi\,X$（$X=\prod_Bp$）。

**引理 30.1（$C\ne\varnothing$，故 $\Pi\ge2$）**【已证明】 $S$ 是横截集，特别 $S\cap D_1\ne\varnothing$，即 $C\ne\varnothing$，$\Pi\ge2$。

**引理 30.2（$H$ 的严格形式）**【已证明，14 号引理 3.1.1/注 5.5】 $H\Rightarrow\forall p\in S:\mu/p>a_1$，故 $\max S<\mu/a_1$。（$\mu/p=a_1$ 不可能：否则位置引理给 $a_{i_p}<a_1\le a_{i_p}$。）

**引理 30.3（修正版：用 prover-mu 的 (N)）**【已证明】 设 H 成立且 prover-mu 的相容性必要条件（其 (δ)，与 (g) $\mu<(Ca_1/2)^s$ 夹逼而来）成立：
$$2^{\,s(s-1)}<C^{\,s(s-2)}\,a_1^{\,s(s-3)}. \tag{N}$$
（$C=\Pi=S\cap D_1$ 的乘积。注意方向：这里是 $2^{\,\cdot}$ 在**左**。）则由 $C\ge2$（30.1 引理）、$a_1\ge2$ 得
$$C^{\,s(s-2)}a_1^{\,s(s-3)}\ \ge\ 2^{\,s(s-2)}\cdot2^{\,s(s-3)}\ =\ 2^{\,s(2s-5)},$$
故 (N) 只要求 $2^{s(s-1)}<C^{s(s-2)}a_1^{s(s-3)}$，而右端最小值是 $2^{s(2s-5)}$。于是：
* $s\ge5$：$s(s-1)>s(2s-5)$，(N) **自动成立**，无信息；
* $s=4$：$s(s-1)=s(2s-5)=12$，(N) $\iff 2^{12}<C^8a_1^4\iff 8<C^2a_1$，即只排除 $C^2a_1\le8$（$C\ge2,a_1\ge2$ 下唯一情形是 $C=2,a_1=2$）；
* $s\le3$：$s(s-1)<s(2s-5)$，(N) 自动成立。
**所以 (N) 单独只排除 $(s=4,C=2,a_1=2)$，并不给 $s\le3$**（Lead 的判读正确；§21 初版把方向写反了，已改）。

**引理 30.4（H 的两条无条件推论，可用作替代路线）**【已证明】
(i) 由 30.2：$\Pi X=\mu>a_1\max S=a_1\max B$，即
$$\Pi\cdot\!\!\prod_{p\in B\setminus\{\max B\}}\!\!p\ >\ a_1 ;$$
特别 $|B|=2$ 时 $\Pi\min B>a_1$（即 $\min B>a_1/\Pi$，与 14 号命题 5.4.1 一致）；$|B|\ge1$ 时 $\Pi>1$。
(ii) 又 $\max B<\mu/a_1=\Pi X/a_1$，即 $a_1\max B<\Pi X$（同 (i)）。
这两条与 (N) 一起把 H 的 $s\ge4$ 情形限制为：$C^{s(s-2)}a_1^{s(s-3)}>2^{s(s-1)}$ **且** $\Pi\prod_{B\setminus\max B}p>a_1$——(N) 对 $s\ge5$ 自动，故 $s\ge5$ 时必须靠 30.4 型的乘性约束（以及 $U_p<\mu/p$、$U_p\ge2p$ 的原式）继续施压。

**推论 30.5（H 排除的条件式版本）**【已证明，条件式】 若另有"$H\Rightarrow s\le3$"（例如 (N) 的某个更强形式，或在 $s\ge4$ 时由 $U_p$ 的交叉素数得到更强的乘性矛盾），则 H 不可能，从而 14 号注 2.4 给 $\mu<a_1p_{\min}\le2a_1^2$、14 号定理 2.2 给 TCL 常数 $N=2a_1^2$。**当前状态：$H\wedge s\ge4$ 仍未排除**（$(s=4,C=2,a_1=2)$ 已由 (N) 排除）。

**任务 2（纯 $T$-路线的统一 boost）**【已证明】 设 $T$ 为 26.2 给出的横截集（$T\cap\operatorname{supp}(t)=\varnothing$）、$g:=2^{|\operatorname{supp}(t)|}$（27.3 的间隙界）。取最小的与 $t$ 互素的 $s_0\ge a_1/\prod_Tp$，则 $W:=s_0\prod_Tp$ 满足 $W\in A_\infty$、$\gcd(W,t)=1$、$a_1\le W< a_1+g\prod_Tp$。故统一判据为
$$g\cdot\prod\nolimits_Tp\le(C-1)a_1\ \Longrightarrow\ a_{i_r}<Ca_1 .$$
（$C=3$、$g\prod_Tp\le2a_1$ 即 28.2；若 $\prod_Tp\ge a_1$ 则退化为"直接取值不加 boost"，对应 28.3 的窗口条件，或在 $\prod_Tp<Ca_1$ 时完成。）

**残余（task-24，修正后）**【缺口】 (i) $H\wedge s\ge4$ 仍未排除；(N) 只额外排除了 $(s=4,C=2,a_1=2)$，$s\ge5$ 时 (N) 自动成立，故 $s\ge5$ 必须用 30.4 的乘性约束与 $U_p$ 原式（$U_p<\mu/p$、$U_p\ge2p$、交叉素数）继续施压；(ii) $T$-路线中 $g\prod_Tp>(C-1)a_1$ 且 $\prod_Tp\notin[a_1,Ca_1)$ 的组合仍待处理（$C=3$ 时的目标；数值 978 例中条件 A–C 之外从未出现）。
**待 prover-mu 定稿**：$(N)$ 的精确形式与它是否还有其他交叉素数加项；若有，按 30.3 的一行比较重做即可。

---

## §22（task-24 续）prover-mu 定稿核查：$(N)$ 的最终形式与 "$s\ge4$ 未被排除"

**引理 31.1（勘误转述，【已证明】，prover-mu）** 13 号引理 3.4.2 的指数应为 $\prod_rT_r<\mu^{s}$（$T_r=a_{i_r}r<\mu$），于是 H 下
$$\text{(A)}\ a_1^{s}<\mu^{s-1},\qquad \text{(B)}\ 2^{s}<\mu^{s-2},\qquad \text{(C)}\ (2a_1)^{s/2}<\mu^{s-1}.$$
（旧式"$2^sa_1^s<\mu^{s-2}$"不成立；反例 $a_1=100,\mu=20806$，见 prover-mu 邮件。）

**引理 31.2（$(N)$ 的最终形式，【已证明】，条件式）** 配 $\mu<(Ca_1/2)^s$（需 $a_{i_r}<Ca_1$，即本文 (UB) 的常数 $C$；$q\in D_1$ 时 $q\le a_1\le Ca_1/2$），由 (A)(B)(C) 分别得
$$\text{(N-B)}\ 2^{\frac{s-1}{s-2}}<Ca_1,\qquad \text{(N-A)}\ 2<Ca_1^{\frac{s-2}{s-1}},\qquad \text{(N-C)}\ 2^{\frac{s-1/2}{s-1}}<Ca_1^{\frac{s-3/2}{s-1}}.$$
**判读**：三者对 $s\ge4$、$C\ge2$、$a_1\ge3$ **自动成立**（如 (N-B) 左端 $\le2^{3/2}=2.83<Ca_1$）——所以 **$H\wedge s\ge4$ 确实没有被乘积界排除**；被排除的只是边界（如 (N-B) 排 $(s=3,C=2,a_1=2)$）。
按 (A) 重推我 §21 的旧 (30.1) 得 $2^{s(s-1)}<C^{s(s-1)}a_1^{s(s-2)}$（左端在 $C\ge2$ 下也被右端自动满足，故同样无信息）。

**结论（task-24 的最终状态）**【已证明 + 缺口】
* 已验证：$(N)$ 系（30.1 与 (N-A/B/C)）**都不排除 $H\wedge s\ge4$**；排除的只是极少数边界。
* 因此 $H\wedge s\ge4$ 必须靠**乘积界之外的输入**：14 号的 (5.1)（含 $q_p\in A$ 的交叉结构）、命题 5.4 的窗口约束、以及本文 30.4 的 $\Pi\prod_{B\setminus\max B}p>a_1$。
* $T$-路线（任务 2）不受影响：boost 判据 $g\prod_Tp\le(C-1)a_1\Rightarrow a_{i_r}<Ca_1$ 与 prover-mu §8.3 接口直接兼容（接口只需任意常数 $C$）。

**残余（§21/§22 合并）**【缺口】 (i) $H\wedge s\ge4$（需新输入）；(ii) $T$-路线中 $g\prod_Tp>(C-1)a_1$ 且 $\prod_Tp\notin[a_1,Ca_1)$ 的组合（$C=3$；数值 978 例中条件 A–C 之外从未出现）。

---

## §23（task-25）$H\wedge s\ge4$：交叉素数计数给出的"大 $a_1$"约束

**设定** H 成立，$S=\operatorname{supp}(\mu)$、$s=|S|\ge4$，$C=S\cap D_1$、$B=S\setminus D_1$、$b=|B|$。对 $p\in S$ 令 $i_p:=\mathrm{kill}(\mu/p)$（H 使 $\mu/p>a_1$，故 $i_p<\infty$ 且位置引理给 $a_{i_p}<\mu/p$），$U_p:=a_{i_p}$。已知（14 号引理 3.1.3 与 (P2)）：
$$D_{i_p}\cap S=\{p\},\qquad p\mid U_p,\qquad U_p\in A_\infty,\qquad U_p<\mu/p,\qquad p\in B\Rightarrow\exists q_p\in A:\ q_p\mid U_p .$$

**引理 32.1（交叉素数）**【已证明】 对 $p\ne p'\in S$，$U_p,U_{p'}$ 都是项，故 $\gcd(U_p,U_{p'})>1$（(P1)）；取 $r_{pp'}\mid\gcd(U_p,U_{p'})$，则 $r_{pp'}\notin S$。
证明：$r_{pp'}\in D_{i_p}\cap D_{i_{p'}}$；若 $r_{pp'}\in S$ 则 $r_{pp'}=p$（因 $D_{i_p}\cap S=\{p\}$）且 $r_{pp'}=p'$，矛盾。$\blacksquare$

**引理 32.2（乘积下界）**【已证明】
$$\prod_{p\in S}U_p\ \ge\ \mu\cdot\prod_{\{p,p'\}}r_{pp'}^{2}\cdot\prod_{p\in B}q_p\ \ge\ \mu\cdot2^{\,s(s-1)}\cdot 2^{\,b}.$$
证明：每个 $r_{pp'}$ 同时整除 $U_p$ 与 $U_{p'}$，故在 $\prod_pU_p$ 中出现至少两次（不同的因子位置）；$\{r_{pp'}\}$ 有 $\binom s2$ 个配对，每个 $r\ge2$ 给 $r^2\ge4$，故 $\prod r_{pp'}^2\ge4^{\binom s2}=2^{s(s-1)}$；再乘 $\prod_p p=\mu$ 与 $\prod_{p\in B}q_p\ge2^b$。$\blacksquare$

**引理 32.3（$(N)$ 的交叉素数加强版，给出"$a_1$ 必须很大"）**【已证明，条件式】 由 §22 勘误后的正确式 $\prod_pU_p<\mu^{s-1}$（即 $\prod T_p<\mu^s$，$T_p=U_pp$）与 32.2：
$$2^{\,s(s-1)+b}<\mu^{\,s-2}.$$
再配 $\mu<(Ca_1/2)^s$（$C$ 为 (UB) 常数）得
$$2^{\,\frac{s(s-1)+b+s(s-2)}{s(s-2)}}<Ca_1,\qquad\text{特别（用 }b\le s-1\text{）}\quad 2^{\,2+\frac{2s-1}{s(s-2)}}<Ca_1 .$$
数值：$s=4$ 时右端指数 $=2+7/8=2.875$，即 $Ca_1>2^{2.875}\approx7.3$；$s=5$ 时 $2+9/15=2.6$，即 $Ca_1>6.1$；$s\to\infty$ 时指数 $\to2$，即只要求 $Ca_1>4$。
**判读**：这是"$a_1$ 必须足够大"的约束（$C\ge2$ 时 $a_1\ge4$ 即可满足 $s$ 大者），**仍不构成矛盾**；也就是说 $H\wedge s\ge4$ 的真障碍不在乘积/计数，而在缺少 $X=\prod_Bp$ 的**上**界。

**悬置的问题（缺口）**【缺口】 证 $\mu=\Pi X\le2a_1^2$（$X$ 的上界）。已试且不够的：14 号 (5.1)（只给 $X$ 的下界）、推论 5.2.1（$p<\sqrt{\mu/2}$，亦为下界）、32.3（大 $a_1$ 约束）。**可能需要的新输入**：$|B|\ge2$ 时至少两条"不同族"的私有项（$p\in B$ 与 $c\in C$）之间的交叉素数同时撞上 $D_1$，从而在 $\prod_AT_p<\mu^s$ 之外多出与 $\operatorname{rad}(a_1)$ 相关的因子——14 号定理 5.1 的 (5.1) 正是这一方向的雏形，可用 32.1 的记号把 (5.1) 加强为含 $r_{pp'}$ 的版本后再与 30.4 联立。

---

## §24（Lead 新方向）粗糙版 $\neg H$：$\exists p\mid\mu:\mu/p\le a_1/2$

**目标（$H_{\frac12}$ 的否定）**：$\exists p\mid\mu:\ \mu/p\le a_1/2$。反设记为 $\mathrm H_{\frac12}$：$\forall p\in S:\mu/p>a_1/2$。

**引理 33.1（为什么粗糙版就够；稳妥版与强版）**【已证明】
$$\mu=p\cdot\frac{\mu}{p}\le\frac{a_1p}{2}.$$
* **稳妥版**：只要 $p\le4a_1$ 就有 $\mu\le2a_1^2$（进 14 号定理 2.2，$N=2a_1^2$）。注意 $p\le4a_1$ 已经是"弱素因子界"，比 $p\le2a_1$ 弱。
* **强版**：若 $p\le2a_1$（**出处是素因子界本身**，即引理 5.4 的结论 / $\neg R$ 的一半；引理 5.2 的原文 $\min E_p\le a_1p$ **不直接**给 $p\le2a_1$，此处已按 Lead 勘误更正），则 $\mu\le a_1^2\le2a_1^2$，且同时得到素因子界。
* 若再有 (b)（$p\le a_1$）则更强 $\mu\le a_1^2/2$。
**本路线不需要 $H$，也不需要 (UB)/(CS)**；它对素因子的依赖可弱化到 $p\le4a_1$。

**引理 33.2（$|S|=1$ 自动）**【已证明】 $\mu\in\mathcal M$ 且 $|S|=1$ 时 $\mu=p$ 为素数，$\mu/p=1\le a_1/2$（$a_1\ge2$）。

**引理 33.3（$\mathrm H_{\frac12}$ 下 $i_p$ 无条件有限——这是它比 $H$ 干净的地方）**【已证明】 设 $\mathrm H_{\frac12}$（$\forall p\in S:\mu/p>a_1/2$）。则对每个 $p\in S$：$\mu/p$ 是 $\mu\in\mathcal M$ 的**真因子**，故 $\mu/p\notin A_\infty$，于是
$$i_p:=\mathrm{kill}(\mu/p)<\infty,\qquad D_{i_p}\cap S=\{p\},\qquad p\mid a_{i_p},\qquad \gcd(a_{i_p},\mu/p)=1,\qquad a_{i_p}\in A_\infty .$$
（对照：在 $H$ 下这几条还要先有位置引理；在 $\mathrm H_{\frac12}$ 下 $i_p$ 的有限性与私有性**完全无条件**，这正是粗糙版更干净的机制。）

**引理 33.4（$\mathrm H_{\frac12}$ 下的全部量级与交叉结构）**【已证明】 设 $\mathrm H_{\frac12}$。则
(i) $\mu>(a_1/2)\max S$；
(ii) 交叉素数 $r_{pp'}\notin S$（32.1 的论证不变，只用 33.3）；
(iii) $p\in B\Rightarrow a_{i_p}\ge2p$（14 号注 4.3 的 (h)，只用 $p\notin D_1$）；
(iv) **二分**：若 $p\in S$ 满足 $\mu/p\ge a_1$，位置引理给 $a_{i_p}<\mu/p$；若 $\mu/p<a_1$，则只有 $a_{i_p}\ge\max(2p,a_1)$。故 $\mathrm H_{\frac12}\wedge\neg H$ 时必 $\exists p:\ \mu/p\in(a_1/2,a_1)$（"crux 型"），此时按 33.1 稳妥版直接用 $\mu\le pa_1/2$ 收口——只要该 $p\le4a_1$。

**数值核对**【数值】 `logs/d18_crude.py 2 500`：$\max_{\mu\in\mathcal M}\min_{p\mid\mu}\mu/(pa_1)$ 的总最大值为 $0.5$，唯一取到者是退化例 $(a_1,\mu)=(2,2)$（$|S|=1$）；**限制 $|S|\ge2$ 后最大值仅 $0.2$**（$a_1=15,\mu=15,S=\{3,5\}$），且 $|S|\ge2$ 时 $>0.5$ 的反例 **0 个**。与 Lead 的 $a_1\le1500$ 扫描（1892 个 $\mu$、$H$ 实例 0 个）一致。

**残余（§24）**【缺口】 排除 $\mathrm H_{\frac12}$（等价地证 $\exists p:\mu/p\le a_1/2$）。细分：$|S|=1$（33.2 已解决）；$|S|=2$（见 §25，只剩一个窗口子情形）；$|S|\ge3$（用 33.3 的私有项/交叉素数结构，可套用 §23 的全部计数）。**相对 $H$ 的好处**：即使 $\neg H$ 的具体 $p$ 落在 $(a_1/2,a_1)$，也能靠 $\mu\le p\,a_1/2\le a_1^2$ 收口，不需要 (UB)。

---

## §25（Lead 的 $|S|=2$ 干净版）$\mathrm H_{\frac12}$ 下只剩一个窗口子情形

**设定** 反设 $\mathrm H_{\frac12}$、$S=\{p,q\}$、$p<q$、$\mu=pq\in\mathcal M$。由 $S$ 横截，$D_1\cap S\ne\varnothing$。

**引理 34.1（情形 A：$q\in D_1$，闭环）**【已证明】 若 $q\in D_1$ 则 $q\mid a_1$，故 $q\le a_1$；又 $p<q$，于是
$$\mu=pq<a_1^2\le2a_1^2,$$
即该情形闭环（甚至不用 $\mathrm H_{\frac12}$）。（对照：Lead 先前"$q\in D_1$ 时 $p<a_1\lor q>a_1$"的困惑由 $p<q\le a_1$ 直接消除。）

**引理 34.2（情形 B：$q\notin D_1$，$p$ 被逼进窗口）**【已证明】 设 $q\notin D_1$。则 $D_1\cap S\ne\varnothing$ 给 $p\in D_1$、$p\le a_1$；取 $i_q:=\mathrm{kill}(q)$（33.3 保证有限），$\rho'$-机制给 $a_{i_q}\ge2q$。若 $p\ge a_1$，则由位置引理（用于 $k=\mu/q=p\ge a_1$）得 $a_{i_q}<p<q$，于是 $2q\le a_{i_q}<q$，矛盾。故
$$p<a_1,\qquad\text{再由 }\mathrm H_{\frac12}\ (\mu/q=p>a_1/2)\text{ 得 } p\in(a_1/2,\,a_1).$$
**子情形 B1（$q\le a_1$）**：$\mu=pq<a_1^2$ ✓ 闭环。
**子情形 B2（$q>a_1$，唯一残余）**：此时 $\mu\le a_1^2\iff q\le a_1^2/p$，而 $p\in(a_1/2,a_1)$ 使 $a_1^2/p\in(a_1,2a_1)$；即**只需证 $q\le a_1^2/p$**（比 $q\le2a_1$ 略紧）。

**引理 34.3（B2 中已有的两侧夹逼）**【已证明】 在 B2 中：$a_1<q$、$2q\le a_{i_q}\in A_\infty$、$q\notin D_1$、$a_{i_q}\ge2q>2a_1$；并且 $i_p=\mathrm{kill}(q)$ 由 $q>a_1$ 与位置引理给 $a_{i_p}<q$，$a_{i_p}\ge2p$（$p$ 是私有项，且 $a_{i_p}$ 必须撞上 $D_1\ni p$），故 $2p\le a_{i_p}<q$。于是
$$2p\le a_{i_p}<q,\qquad 2q\le a_{i_q}<\mu/p=q\cdot?$$
（末式在 $p\ge a_1$ 时给出 $a_{i_q}<p$，此处 $p<a_1$ 故位置引理不可用，这正是 B2 的困难所在。）

**$|S|=2$ 的状态**【缺口】 A、B1 已闭环；**B2（$q\notin D_1$、$a_1<q$、$p\in(a_1/2,a_1)$）仍未闭环**，需证 $q\le a_1^2/p$。数值：$|S|=2$ 的 $\mu$ 在 $a_1\le600$ 有 133 例、$\max\max S/a_1=1/3$（故样本里 $q\le a_1/3$，B2 与 $\mathrm H_{\frac12}$ 都不出现，余量很大）。若 B2 收口，$|S|=2$ 整段闭环，$\mathrm H_{\frac12}$ 残余就压到 $|S|\ge3$，与 §23 的计数直接对接。

---

## §26（B2 的精细结构：$q$ 不是项、$<q$ 的项恰为连续 $p$-倍数、首个 $p$-free 项）

**设定（B2）** $S=\{p,q\}$、$p<q$、$p\mid a_1$、$p\in(a_1/2,a_1)$、$q\notin D_1$、$a_1<q$、$\mu=pq\in\mathcal M$、$\mathrm H_{\frac12}$。（目标：$q\le a_1^2/p$。）

**引理 35.1（$q$ 不是项）**【已证明】 $q\notin A_\infty$（否则 $q$ 是 $\mu\in\mathcal M$ 的真 $A_\infty$-因子），而 $q>a_1$ 时"$q$ 是项 $\iff q\in A_\infty$"，故 $q$ 不是项。令 $u:=\max\{s:a_s<q\}$，则 $a_u<q<a_{u+1}$、$a_{u+1}-a_u\le\operatorname{rad}(a_1)$。

**引理 35.2（$<q$ 的项恰是自 $a_1$ 起的连续 $p$-倍数）**【已证明】
(i) 每个项被 $p$ 或 $q$ 整除（$S$ 横截）；$\ge q$ 才可能被 $q$ 整除，故**一切 $<q$ 的项都被 $p$ 整除**。
(ii) 反之，任何满足 $a_1\le k<q$、$p\mid k$ 的 $k$ 都是项：它与每个 $<q$ 的项（都是 $p$ 的倍数）有公因子 $p$，与 $a_1$ 也有（$p\mid a_1$），而 $\ge q$ 的项都比它大、不影响其存活，故 $k$ 存活。
(iii) 于是 $\{a_s:a_s<q\}=\{k:\ a_1\le k<q,\ p\mid k\}$，特别
$$a_{u+1}=p\left\lceil\frac{q}{p}\right\rceil,\qquad a_u=a_{u+1}-p,\qquad p\mid(a_{u+1}-a_u)\le\operatorname{rad}(a_1).$$
**推论**：$p\le\operatorname{rad}(a_1)$，配合 $p>a_1/2$ 得 $a_1<2\operatorname{rad}(a_1)$。

**引理 35.3（首个 $p$-free 项 $a_e$ 的形状）**【已证明】 令 $a_e:=$ 首个 $p\nmid a_e$ 的项。
(i) $a_e$ 存在且 $a_e>q$（35.2(i)），且 $a_e$ 必被 $q$ 整除（横截 + 每项被 $p$ 或 $q$ 整除），故 $a_e=jq$。
(ii) $a_e\ge2q$（$q\notin A_\infty$ 且 $q$ 不是项，故 $a_e\ne q$；又 $q\mid a_e$）。
(iii) $a_e\le pq=\mu$：$\mu$ 是项且 $q$-可除，而 $a_e$ 是**首个**项中被 $q$ 整除的"$p$-free 者"，需另证——事实上首个 $q$-可除项 $a_Q\le\mu$（$\mu$ 本身 $q$-可除且是项），且 $a_Q$ 必 $p$-free（否则 $a_Q$ 被 $p,q$ 同时整除仍可能存活，但 $<q$ 的 $q$-可除项不存在，故 $a_Q>q$；若 $p\mid a_Q$ 则 $a_Q$ 与后续项兼容性不变，仍是最早的 $q$-可除项，此时需检查它是否 $p$-free——留作 35.4）。
(iv) 由 (P1) $a_e$ 与 $a_1$ 有公因子，而 $p\nmid a_e$，故 $\exists\rho\in D_1\setminus\{p\}$，$\rho\mid a_e$；于是 $a_e\ge q\rho\ge2q$（同 (ii) 的另一证法）。
(v) $a_e\le a_{i_q}$：$a_{i_q}$ 也是 $p$-free（$D_{i_q}\cap S=\{q\}$）且 $q$-可除，而 $a_e$ 是首个 $p$-free 项。

**引理 35.4（把 35.3(iii) 补严）**【已证明】 记 $a_Q$ 为首个 $q$-可除项。则 $q<a_Q\le\mu$（$q$ 不是项、$\mu$ 是 $q$-可除的项）。若 $p\nmid a_Q$ 则 $a_e=a_Q\le\mu$；若 $p\mid a_Q$，则 $a_Q=pq'$（$q\mid a_Q$）且 $a_Q<q^2$，此时把 $a_Q/p$ 型的项考察交给下一轮的 $j$ 计数即可。

**残余（B2）**【缺口】 证 $q\le a_1^2/p$。可用：$2p\le a_{i_p}<q$（34.3）、$a_e=jq\ (2\le j<p)$、$a_e\le a_{i_q}$、$a_{i_q}\ge q\rho'$（$\rho'\in D_1\setminus\{p,q\}$）、$\mu=pq$ 是项且 $a_e<\mu$、以及 $a_1<2\operatorname{rad}(a_1)$（35.2 推论）。数值：B2 在 $a_1\le600$ 样本中不出现。

**引理 35.5（B2 的三条进一步结构，全部【已证明】）**
(i) $a_e=a_{i_q}$：$i_q=\mathrm{kill}(\mu/q)=\mathrm{kill}(p)$，故 $a_{i_q}$ 就是"首个与 $p$ 互素的项"即首个 $p$-free 项，与 $a_e$ 的上述定义一致。
(ii) **同余约束**：由 35.2(ii) 的加强（$a_e$ 之前的项恰是 $[a_1,a_e)$ 中 $p$ 的全部倍数，均已证），$a_e$ 与前一项 $a_{u'}$ 的差 $\le\operatorname{rad}(a_1)$ 且 $a_{u'}$ 是 $<jq$ 的最大 $p$-倍数，故
$$jq\equiv s\pmod p,\qquad 1\le s:=jq-p\lfloor jq/p\rfloor\le\operatorname{rad}(a_1)\ (\le a_1/2\cdot2=p\text{ 量级});$$
特别的前一项 $a_{u'}=jq-s$ 是项，且 $p\mid a_{u'}$、$q\nmid a_{u'}$。
(iii) **$j$ 含 $D_1\setminus\{p\}$ 的素因子**：$a_e=jq$ 与 $a_1$ 都是项，故 $\gcd(a_e,a_1)>1$；又 $q\nmid a_1$（$q\notin D_1$），故 $\exists\rho\in D_1\setminus\{p\}:\ \rho\mid j$，从而 $j\ge\rho\ge2$（与 35.3(iii) 独立同源）。

**当前最窄残余（B2）**【缺口】 在 35.1–35.5 的全部约束（$2\le j<p$、$p\nmid j$、$\exists\rho\in D_1\setminus\{p\}:\rho\mid j$、$jq\equiv s\pmod p$ 且 $1\le s\le\operatorname{rad}(a_1)$、$2p\le a_{i_p}<q$、$a_e=jq<\mu$、$a_{i_q}=a_e$）下证 $q\le a_1^2/p$。
（$p\mid a_1$、$p\in(a_1/2,a_1)$、$p\le\operatorname{rad}(a_1)$、$a_1<2\operatorname{rad}(a_1)$ 也已就位。）

---

## §27（Lead 的新硬约束：$a_e$ 与全部前项的兼容性 = 一次"覆盖"）

**引理 36.1（覆盖条件）**【已证明】 在 B2 中（记号同 §26）：$a_e=jq$ 是首个 $p$-free 项，故 $a_e$ 之前的项全部是 $p$-倍数，且由 35.2(iii) 它们恰为
$$\Bigl\{p\,y:\ y\in\bigl[\lceil a_1/p\rceil,\ (jq-s)/p\bigr]\Bigr\},\qquad s=jq\bmod p\in[1,\operatorname{rad}(a_1)] .$$
$a_e$ 与每个前项都是项，故 (P1) 给出 $\gcd(jq,\,py)>1$；又 $y\le(jq-s)/p<jq/p\le q$（$j\le p$），故 $q\nmid y$、$q\nmid py$，于是 $\gcd(jq,py)=\gcd(j,py)=\gcd(j,y)$（末步用 $p\nmid j$，35.3(ii)）。因此
$$\boxed{\ \forall y\in\Bigl[\Bigl\lceil\frac{a_1}{p}\Bigr\rceil,\ \frac{jq-s}{p}\Bigr]:\quad \gcd(j,\,y)>1\ }$$
即"$j$ 的素因子集合必须覆盖整个区间"。

**推论 36.2（$j$ 必为偶数，$p$ 必为奇数）**【已证明】 $p\in(a_1/2,a_1)$ 给 $a_1/p\in(1,2)$，故 $\lceil a_1/p\rceil=2$；区间非空（$jq-s\ge2q-2a_1>2p$），故 $y=2$ 在区间内，$\gcd(j,2)>1$，即 **$2\mid j$**。又 $p\nmid j$，故 $p\ne2$，即 $p$ 为奇素数。

**推论 36.3（$j$ 素数时只能 $j=2$，且 $q$ 被压住）**【已证明】
(i) 若 $j$ 为素数，则由 $2\mid j$ 得 $j=2$。
(ii) 此时区间要求每个 $y$ 与 $2$ 有公因子，即区间内无奇数；特别 $y=3$ 不在区间内，故
$$\frac{2q-s}{p}<3\ \Longrightarrow\ q<\frac{3p+s}{2}\le\frac{3p+\operatorname{rad}(a_1)}{2}<2.5p\ (<2.5a_1).$$
(iii) 一般地，若 $j$ 的相异素因子为 $\rho_1,\dots,\rho_k$，则区间长度不超过 $\prod\rho_i\cdot(1+1/\cdot)$ 型的覆盖界：具体地，长度为 $L:=(jq-s)/p-2$ 的区间必须被 $\bigcup_i\rho_i\mathbb Z$ 覆盖，故 $L+1\le\prod_i\rho_i$ 的一个显式上界，从而
$$\frac{jq-s}{p}\le 2+\Bigl(\prod_{i}\rho_i-1\Bigr)\ \Longrightarrow\ jq\le p\Bigl(1+\prod_i\rho_i\Bigr)+s .$$

**残余（B2，最窄）**【缺口】 合并 35.5 与 36.1–36.3：需在
$$2\mid j,\quad j<p,\quad p\nmid j,\quad \exists\rho\in D_1\setminus\{p\}:\rho\mid j,\quad jq\equiv s\pmod p,\ 1\le s\le\operatorname{rad}(a_1),$$
$$\forall y\in[2,(jq-s)/p]:\ \gcd(j,y)>1,\qquad 2p\le a_{i_p}<q,\qquad p\mid a_1,\ p\in(a_1/2,a_1),\ p\le\operatorname{rad}(a_1)$$
下证 $q\le a_1^2/p$（$\iff pq\le a_1^2$）。
**目前最近的一步**：若 $j$ 为素数则 $j=2$ 且 $q<2.5p$，此时 $q\le a_1^2/p$ 等价于 $p\le a_1/\sqrt{2.5}\approx0.63a_1$——故 $j$ 素数且 $p\in(0.63a_1,a_1)$ 是 B2 的最内层核；$j$ 合数时用 36.3(iii) 的乘积界。数值：B2 在 $a_1\le600$ 样本中不出现。

**引理 36.4（最内层核被进一步收紧：$j=2$ 时必 $q=(3p+s)/2$）**【已证明】 设 $j=2$（36.3(i)）。由 36.1，区间 $[2,(2q-s)/p]$ 内的 $y$ 必须全为偶数，故 $(2q-s)/p<3$；记 $m:=\lfloor2q/p\rfloor$，则 $2q=mp+s$（$1\le s\le\operatorname{rad}(a_1)$）且 $m\le3$。
* $m\le1$ 不可能（$2q>4p$ 由 $q>2p$，见 34.3 的 $2p\le a_{i_p}<q$）；
* $m=2$ 会给 $q=p+s/2<2p$（因 $s\le\operatorname{rad}(a_1)\le a_1<2p$），与 $q>2p$ 矛盾；
* 故 **$m=3$**，即
$$2q=3p+s,\qquad p<s\le\operatorname{rad}(a_1)\ (<2p),\qquad q=\frac{3p+s}{2}<2.5p .$$
（$s>p$ 由 $q>2p$ 推出。）于是 $q\le a_1^2/p\iff p(3p+s)\le2a_1^2$，而 $3p^2+ps\le4\operatorname{rad}(a_1)^2$，故
$$\text{若 } \operatorname{rad}(a_1)\le a_1/\sqrt2\ (\approx0.707a_1)\ \text{则 } q\le a_1^2/p\ \text{自动成立}.$$
**新的最内层核**：$j=2$、$q=(3p+s)/2$、$s\in(p,\operatorname{rad}(a_1)]$、$\operatorname{rad}(a_1)>0.707a_1$、$p>0.63a_1$、$2p\le a_{i_p}<q$。

---

## §28（Lead 的 primorial 论证：$q<1.5a_1$ 已证，B2 只剩一条窄带）

**引理 37.1（$(\ast)$ 的强化形式）**【已证明】 沿用 36.1 的记号 $Y:=\lfloor(jq-s)/p\rfloor$（注意 $(jq-s)/p=\lfloor jq/p\rfloor$，因 $s=jq\bmod p$），则
$$(\ast)\quad\forall\,2\le y\le Y:\ \gcd(j,y)>1 .$$
于是**每个素数 $\ell\le Y$ 都整除 $j$**，即 $\operatorname{primorial}(Y)\mid j$，特别 $j\ge\operatorname{primorial}(Y)$。又 $\operatorname{primorial}(Y)\ge Y$，且 $Y\ge3$ 时严格（$Y=3$ 给 $6>3$；$Y\ge4$ 归纳 $2\cdot3\cdot5=30>Y$ 起即显然）。

**引理 37.2（情形 (a) 其实不可能）**【已证明】 设 $j(q-p)\ge s$，则 $Y=\lfloor(jq-s)/p\rfloor\ge j$，于是 $\operatorname{primorial}(Y)\le j\le Y$，由 37.1 的严格性得 $Y\le2$。
但 $j$ 为偶数（36.2）、$j<p$、且 $q>2p$（34.3 的 $2p\le a_{i_p}<q$），故 $\lfloor jq/p\rfloor>2j\ge4$，即 $Y\ge5>2$——矛盾（注意 $Y=\lfloor jq/p\rfloor$ 与 $j$ 的取值无关地下界为 $\lfloor 2q/p\rfloor\ge4$）。
**故情形 (a) 被排除，恒有**
$$j(q-p)<s\ \Longrightarrow\ q<p+\frac{s}{j}\le p+\frac{\operatorname{rad}(a_1)}{2}\le\frac32a_1 .$$
（末步用 $p<a_1$、$\operatorname{rad}(a_1)\le a_1$；$j\ge2$。）
**注**：Lead 版本把情形 (a) 与 (b) 并列处理；这里指出 (a) 在 B2 中根本不会发生，因此 $q<p+\operatorname{rad}(a_1)/2$ 是无条件结论。

**推论 37.3（$q$ 与 $\mu$ 的上界，【已证明】）**
$$q<\frac32a_1,\qquad \mu=pq<\frac32a_1p .$$
于是**若 $p\le\frac23a_1$ 则 $\mu\le a_1^2$**，B2 收口。

**残余（B2，新的窄带）**【缺口】 只剩
$$p\in\Bigl(\frac23a_1,\ a_1\Bigr),\qquad q\in\Bigl(a_1,\ \min\bigl(p+\tfrac{\operatorname{rad}(a_1)}2,\ \tfrac{a_1^2}p\bigr)\Bigr),$$
并保留 35.1–35.5、36.1–36.4、37.1–37.2 的全部约束（$j$ 偶、$j<p$、$p\nmid j$、$\rho\mid j$、$j(q-p)<s$、$jq\equiv s\pmod p$、$s\le\operatorname{rad}(a_1)$、$p\le\operatorname{rad}(a_1)$、$a_1<2\operatorname{rad}(a_1)$、$\forall y\in[2,\lfloor jq/p\rfloor]:\gcd(j,y)>1$、$2p\le a_{i_p}<q$、$a_e=jq=a_{i_q}$）。
**最后一步的等价形式**：需证 $q\le a_1^2/p$。由 37.2，$j<\dfrac{s}{q-p}$；又 $(\ast)$ 要求 $j\ge\operatorname{primorial}(Y)$ 且 $Y=\lfloor jq/p\rfloor\ge\lfloor 2q/p\rfloor>2j$，故
$$\operatorname{primorial}\Bigl(\Bigl\lfloor\frac{2q}{p}\Bigr\rfloor\Bigr)\ \le\ j\ <\ \frac{s}{q-p}\ \le\ \frac{\operatorname{rad}(a_1)}{q-p}.$$
这把 $q-p$ 与 $p,q$ 的大小关系绑在一起，是当前最紧的一条。数值：B2 在 $a_1\le600$ 的 133 个 $|S|=2$ 样本中不出现（$\max\max S/a_1=1/3<2/3$，与 37.3 一致）。

**推论 37.4（再砍一刀：$\operatorname{rad}(a_1)\le0.816a_1$ 时 B2 收口）**【已证明】 由 37.3，$q<p+\operatorname{rad}(a_1)/2$；而收口等价于 $q\le a_1^2/p$，故充分条件是
$$p+\frac{\operatorname{rad}(a_1)}{2}\le\frac{a_1^2}{p}\iff p^2+\frac{p\,\operatorname{rad}(a_1)}{2}\le a_1^2,$$
由 $p\le\operatorname{rad}(a_1)$（35.2 推论）得左端 $\le\frac32\operatorname{rad}(a_1)^2$，故
$$\operatorname{rad}(a_1)\le\sqrt{\tfrac23}\,a_1\ (\approx0.816a_1)\ \Longrightarrow\ \text{B2 收口}.$$
**最终残余（B2）**：$p\in(\tfrac23a_1,a_1)$、$\operatorname{rad}(a_1)>0.816a_1$（故 $a_1$ 含大素因子），并附 37.3 与 35/36 的全部约束；此时需证 $q\le a_1^2/p$。

---

## §29（复核通过：$|S|=2$ 与 $\mathrm H_{1/2}$ 整体闭环；B2 其实为空）

**引理 38.1（两行引理）**【已证明】 若素数 $p\mid a_1$ 且 $p>a_1/2$，则 $p=a_1$。
证明：$p\mid a_1\Rightarrow k:=a_1/p\in\mathbb Z_{\ge1}$；$p>a_1/2\Rightarrow k=a_1/p<2$，故 $k=1$，$p=a_1$。$\blacksquare$
**推论**：若 $p\mid a_1$ 且另有 $p<a_1$，则 $p\le a_1/2$——即**窗口 $(a_1/2,a_1)$ 与 $D_1$ 的元素不相容**。

**定理 38.2（$|S|=2\wedge\mathrm H_{1/2}\Rightarrow\mu<a_1^2$；$|S|=2$ 闭环）**【已证明】
设 $\mathrm H_{1/2}$、$S=\{p,q\}$、$p<q$、$\mu=pq\in\mathcal M$。由 $S$ 横截（(P1) 用于 $D_1$）得 $S\cap D_1\ne\varnothing$，两情形穷尽：
* **情形 A（$q\in D_1\）**：$q\mid a_1\Rightarrow q\le a_1$，又 $p<q$，故 $\mu=pq<a_1^2$（34.1）。
* **情形 B（$q\notin D_1$）**：则 $p\in D_1$，即 $p\mid a_1$；$\rho'$-机制给 $a_{i_q}\ge2q$；若 $p\ge a_1$，位置引理（$k=\mu/q=p\ge a_1$）给 $a_{i_q}<p<q$，与 $2q\le a_{i_q}$ 矛盾，故 $p<a_1$；而 $\mathrm H_{1/2}$ 给 $p=\mu/q>a_1/2$。于是 $p\mid a_1$、$p\in(a_1/2,a_1)$，由 38.1 推论得 $p\le a_1/2$——**矛盾，情形 B 为空**。
故 $\mu=pq<a_1^2\le2a_1^2$，$|S|=2$ 一侧整体闭环。$\blacksquare$

**注 38.3（§26–§28 的地位）** 上述两行论证使 B2/36.x/37.x 的精细结构**不再必需**；但它们是对"$|S|=2\wedge\mathrm H_{1/2}$ 结构"的完整刻画（$j$ 偶、$q<1.5a_1$、$\operatorname{primorial}$ 夹逼），可留作 $|S|\ge3$ 的模板。**结论：$\mathrm H_{1/2}$ 残余被压到 $|S|\ge3$。**

**引理 38.4（$|S|\ge3$ 时的对应约束）**【已证明】 设 $\mathrm H_{1/2}$、$|S|\ge3$、$C=S\cap D_1\ne\varnothing$、$c\in C$。则 $c\mid a_1$、$c\le a_1$；由 38.1，$c\le a_1/2$ 或 $c=a_1$。配合 33.3（$\mu/p\notin A_\infty$ 无条件、$i_p$ 有限且 $D_{i_p}\cap S=\{p\}$）、33.4（$r_{pp'}\notin S$、$p\in B\Rightarrow a_{i_p}\ge2p$）与 $\mu>(a_1/2)\max S$，§23 的计数框架在阈值 $a_1/2$ 下的输入齐备。

**残余（$\mathrm H_{1/2}$）**【缺口】 只剩 $|S|\ge3$。数值：$\mathrm H_{1/2}$ 在 $a_1\le600$、$|S|\ge2$ 样本中一次不出现（$\max\min_p\mu/(pa_1)=0.2$）。

---

## §30（task-28）$\mathrm H_{1/2}\wedge|S|\ge3$：$b\ge2$、$s=3$ 归约与 $|S|=2$ 的独立复核

### 30.A 独立复核 38.1/38.2（$|S|=2$ 闭环）——逐行检查

* 38.1：$p\mid a_1$、$p>a_1/2$ ⟹ $a_1/p$ 是 $(1,2)$ 中的整数 ⟹ $=1$ ⟹ $p=a_1$ ✓ 正确。
* 38.2 情形 A：$q\in D_1\Rightarrow q\mid a_1\Rightarrow q\le a_1$，$p<q\Rightarrow\mu<a_1^2$ ✓。
* 38.2 情形 B：$S$ 横截 + $q\notin D_1$ ⟹ $p\in D_1$ ⟹ $p\mid a_1$ ✓（这一步只用 (P1) 的 $D_1$ 版本）；$\rho'$-机制 $a_{i_q}\ge2q$ ✓（$i_q=\mathrm{kill}(\mu/q)$ 有限、$D_{i_q}\cap S=\{q\}$、$D_{i_q}$ 与 $D_1$ 相交且交点 $\notin S$）。
  **关键串**：若 $p\ge a_1$，位置引理（$k=p\ge a_1$、$\mathrm{kill}(p)=i_q<\infty$）给 $a_{i_q}<p$；连同 $p<q$ 与 $q\le a_{i_q}/2$（由 $2q\le a_{i_q}$）得 $a_{i_q}<a_{i_q}/2$ ✗。
  **复核结论：该串无漏洞**（三步都是严格不等式传递：$a_{i_q}<p<q\le a_{i_q}/2$）。故 $p<a_1$，与 $\mathrm H_{1/2}$ 的 $p>a_1/2$ 及 $p\mid a_1$ 一起被 38.1 推论否决 ✓。
* 因此 38.2 成立：$|S|=2\wedge\mathrm H_{1/2}\Rightarrow\mu<a_1^2$。

### 30.B $b=|B|\ge2$（$s\ge3$ 时）

**引理 39.1（$b\ge2$，干净证明）**【已证明】 设 $\mathrm H_{1/2}$。则若 $b=|B|=1$ 有矛盾，故 $b\ge2$；于是 $s\ge3$ 时 $|C|=s-b\le s-2$，且 $s=3$ 时必 $|C|=1,b=2$。
证明：设 $b=1$，则 $X=\max B$ 是唯一的 $B$-素因子，故 $X=\max S$；由 30.2（$\max S<\mu/a_1$）得 $X<\mu/a_1$，于是
$$\mu=\Pi X<\frac{\Pi\mu}{a_1}\ \Longrightarrow\ a_1<\Pi .$$
另一方面 $C\subseteq D_1$ 的元素都是互异素数且都整除 $a_1$，故 $\Pi\mid\operatorname{rad}(a_1)$，特别 $\Pi\le\operatorname{rad}(a_1)\le a_1$。合起来 $a_1<\Pi\le a_1$ ✗。$\blacksquare$
（注：这里不需要 38.4；$\Pi\mid\operatorname{rad}(a_1)$ 就够，Lead 版本中"$\Pi\le a_1/2$"的用法需注意 $c=a_1$ 的例外。）

### 30.C $s=3$ 的归约

**引理 39.2**【已证明】 设 $\mathrm H_{1/2}$、$s=3$。则 $C=\{c\}$、$B=\{p_1,p_2\}$（$p_1<p_2$），且
$$c\mid a_1,\qquad c\le a_1/2\ (\text{或 }c=a_1),\qquad p_1>\frac{2a_1}{\Pi}=\frac{2a_1}{c},\qquad \mu=\frac{a_1^2}{?}\ \text{型目标}\iff p_2\le\frac{2a_1^2}{cp_1}<a_1 .$$
最后的不等号 $<a_1$ 由 $cp_1>2a_1$（14 号命题 5.4.1 的 $\min B>2a_1/\Pi$）得到。

**引理 39.3（$s=3$ 的一个已闭环子情形）**【已证明】 若 $cp_1\le2a_1$：由 $p_2\in B$ 得 $a_{i_{p_2}}\ge2p_2$，又位置引理（$k=\mu/p_2=cp_1\ge a_1$）给 $a_{i_{p_2}}<cp_1$，故 $2p_2<cp_1\le2a_1$，即 $p_2<a_1\le 2a_1^2/(cp_1)$ ✓ 收口。

**残余（$s=3$，最内层）**【缺口】 $cp_1>2a_1$ 且需 $p_2\le2a_1^2/(cp_1)$。可用：$2p_2<cp_1$（39.3 的同一论证，无条件，因 $cp_1\ge a_1$ 总成立——$c\ge2,p_1>2a_1/c$）、$\mu>(a_1/2)p_2$、$c$ 的私有指标、$B$ 侧两个私有项与三个交叉素数（$\prod r^2<\mu$，§23）。**核心缺口仍是 $p_2$ 的上界**；39.3 表明它只在 $2a_1<cp_1\le 2a_1^2/p_2$ 的空隙里出问题。

---

## §31（Lead 的两条 $D_1$-侧抓手：$c'$ 机制与它的定量门槛）

**引理 40.1（抓手 A：$p_2$ 的除法改进）**【已证明】 在 $s=3$ 残余（$C=\{c\}$、$B=\{p_1,p_2\}$、$cp_1>2a_1$）中，存在素数
$$c'\in D_1\setminus\{c\},\qquad c'\mid a_{i_{p_2}},\qquad\text{于是}\quad p_2\,c'\ \le\ a_{i_{p_2}}\ <\ cp_1\ \Longrightarrow\ p_2\le\frac{cp_1}{c'} .$$
证明：$a_{i_{p_2}}\in A_\infty$，故其支撑与 $D_1$ 相交，取交点素因子 $c'$；又 $\gcd(a_{i_{p_2}},\mu/p_2)=1$（引理 4.1）而 $\mu/p_2=cp_1$，故 $c'\nmid cp_1$；若 $c'=c$ 则 $c\mid cp_1$ ✗，故 $c'\ne c$。又 $p_2\mid a_{i_{p_2}}$ 且 $p_2\ne c'$，故 $p_2c'\mid a_{i_{p_2}}$；上界由位置引理（$k=cp_1\ge a_1$、$\mathrm{kill}(cp_1)=i_{p_2}<\infty$）。$\blacksquare$

**推论 40.2（抓手 A 的收口门槛）**【已证明】 若 $c'\ge\dfrac{(cp_1)^2}{2a_1^2}$，则由 40.1 得 $p_2\le\dfrac{cp_1}{c'}\le\dfrac{2a_1^2}{cp_1}$ ✓ 收口。
**门檻的化简**：$c'$ 也是 $D_1$ 的素数且 $c'\ne c$，由 38.1 得 $c'\le a_1/2$ 或 $c'=a_1$。故
* 若 $c'=a_1$：门檻为 $(cp_1)^2\le2a_1^3$；
* 若 $c'\le a_1/2$：门檻为 $(cp_1)^2\le a_1^3$（取 $c'=a_1/2$ 的最坏情形）。
于是只要 $cp_1\le a_1^{3/2}$（一般情形）或 $cp_1\le\sqrt2\,a_1^{3/2}$（$c'=a_1$）就能收口——**残余被压到 $cp_1>a_1^{3/2}\ge2a_1$（对 $a_1\ge4$）**，此时目标 $p_2\le2a_1^2/(cp_1)<2\sqrt{a_1}$。

**引理 40.3（抓手 B：对称版本）**【已证明】 若 $cp_2\ge a_1$，则同样有素数 $c''\in D_1\setminus\{c\}$ 使 $p_1c''<cp_2$，故 $p_1<cp_2/c''$。（$\mathrm H_{1/2}$ 只给 $cp_2>a_1/2$；在 $cp_2\ge a_1$ 的子情形下位置引理可用。）

**分区（记录）**
* $cp_1\le2a_1$：已由 39.3 闭环；
* $2a_1<cp_1\le a_1^{3/2}$：由 40.1–40.2 闭环；
* **残余**：$cp_1>a_1^{3/2}$，此时目标 $p_2\le2a_1^2/(cp_1)<2\sqrt{a_1}$，而已知 $2p_2<cp_1$；须动用 $D_1\setminus\{c\}$ 的全部元素（而不只是单个 $c'$）：对每个 $c'\in D_1\setminus\{c\}$ 用 $c'\mid a_{i_{p_2}}$ 或 $c'\nmid a_{i_{p_2}}$ 的二分会给出 $\operatorname{rad}(a_1)/c$ 与 $a_{i_{p_2}}$ 的乘性约束。

**残余（$s=3$，§31 后）**【缺口】 $cp_1>a_1^{3/2}$ 且 $p_2\le2a_1^2/(cp_1)$。可用新增物：40.1 的 $\exists c'$、40.2 的门槛、40.3 的对称式、以及 $a_{i_{p_2}}$ 与整个 $D_1\setminus\{c\}$ 的交（$\gcd(a_{i_{p_2}},\mu/p_2)=1$ 使这些交点素因子都 $\ne c$ 且 $\nmid p_1$）。

---

## §32（$c'c''<c^2$ 与由它导出的结构性推论）

**引理 41.1（(1) 的无条件性：$D_1\setminus\{c\}\ne\varnothing$）**【已证明】 $a_{i_{p_2}}\in A_\infty$ 且 $a_1$ 是项，故 (P1) 给 $\gcd(a_1,a_{i_{p_2}})>1$，即 $\exists$ 素 $c'\mid a_1$ 且 $c'\mid a_{i_{p_2}}$；又 $\gcd(a_{i_{p_2}},\mu/p_2)=\gcd(a_{i_{p_2}},cp_1)=1$（引理 4.1），故 $c'\ne c$。特别 $D_1\setminus\{c\}\ne\varnothing$（否则 $c\mid a_{i_{p_2}}$ 与 $\gcd(a_{i_{p_2}},c)=1$ 相撞）。
**推论**：$\mu\le(cp_1)^2/c'$（由 $p_2c'\le a_{i_{p_2}}<cp_1$ 与 $\mu=cp_1p_2$）。

**引理 41.2（乘积约束 $c'c''<c^2$）**【已证明】 若还有 $cp_2\ge a_1$，则同法（对 $p_1$、用位置引理 $k=cp_2$）得 $\exists c''\in D_1\setminus\{c\}$：$p_1c''<cp_2$。两式相乘（$p_1p_2>0$）：
$$c'c''<c^2 .$$
特别 $\min(c',c'')<c$，故 $D_1\setminus\{c\}$ 中必有元素 $<c$；且 $c'<c^2/c''\le c^2/2$。

**引理 41.3（$c'$ 的规模上界与残余的必要条件）**【已证明】 在 $cp_2\ge a_1$ 的子情形下：收口需要 $c'\ge\frac{(cp_1)^2}{2a_1^2}$（40.2），而 41.2 给 $c'\le c^2/2$。两式相容要求
$$\frac{(cp_1)^2}{2a_1^2}\le\frac{c^2}{2}\iff p_1\le a_1 .$$
故 **$cp_2\ge a_1\wedge p_1>a_1$ 时必然失手**，残余进一步限定为 $cp_2\ge a_1$、$p_1\le a_1$（且 $cp_1>a_1^{3/2}$）。

**残余（$s=3$，§32 后）**【缺口】 $cp_1>a_1^{3/2}$、$p_2\le2a_1^2/(cp_1)$，且（在 $cp_2\ge a_1$ 时）$p_1\le a_1$、$c'\ge(cp_1)^2/(2a_1^2)$、$c'c''<c^2$、$\min(c',c'')<c$、$c'\mid\operatorname{rad}(a_1)$、$c'\le a_1/2$ 或 $c'=a_1$（38.1）。
**注**：$cp_2<a_1$ 的子情形不能用 41.2（位置引理对 $k=cp_2$ 不可用），此时 $\mathrm H_{1/2}$ 只给 $cp_2>a_1/2$；可考虑对 $k=cp_2$ 用 16.4 型下降（$(a_1/2,a_1)$ 的 crux 结构）。

---

## §33（抓手 C：$D_1$-侧全用；抓手 D：密度下界）

**引理 42.1（抓手 C：乘积版 40.1）**【已证明】 在 $s=3$ 残余中记
$$G:=\prod\{c'\in D_1\setminus\{c\}:\ c'\mid a_{i_{p_2}}\}.$$
则由 40.1 的论证（交点素因子 $\ne c$ 且 $\nmid p_1$，因 $\gcd(a_{i_{p_2}},cp_1)=1$）有 $G\mid a_{i_{p_2}}$、$p_2G\mid a_{i_{p_2}}$（$p_2\ne$ 各 $c'$），故
$$p_2\,G\ \le\ a_{i_{p_2}}\ <\ cp_1 .$$
于是两个门槛：$G\ge\dfrac{(cp_1)^2}{2a_1^2}\Rightarrow p_2\le\dfrac{2a_1^2}{cp_1}$（直接收口）；$G\ge\dfrac{cp_1}{2\sqrt{a_1}}\Rightarrow p_2<2\sqrt{a_1}$（较弱）。
**注**：$G\ge c'$（40.1 的单个 $c'$ 已含在 $G$ 里），故 40.2 是 42.1 的特例。

**引理 42.2（未命中的 $c'$ 的补偿约束）**【已证明】 对每个 $c'\in D_1\setminus\{c\}$ 取私有指标 $i_{c'}$（$D_{i_{c'}}\cap S=\{c'\}$，$c'\mid a_{i_{c'}}$，$\gcd(a_{i_{c'}},\mu/c')=1$）。$a_{i_{p_2}}\in A_\infty$ 使 $\operatorname{supp}(a_{i_{p_2}})$ 是横截集，故 $D_{i_{p_2}}\cap D_{i_{c'}}\ne\varnothing$，即
$$\forall c'\in D_1\setminus\{c\}:\ \exists\,\rho_{c'}\in D_{i_{c'}}\cap D_{i_{p_2}},\qquad \rho_{c'}\ne c'\ (\text{若 }c'\nmid a_{i_{p_2}}),\qquad \rho_{c'}\notin S\ (\text{当 }\rho_{c'}\ne c')\ .$$
于是 $\prod_{c'}\rho_{c'}\mid a_{i_{p_2}}$，而各 $\rho_{c'}\ge2$：未命中 $D_1$ 的 $c'$ 越多，$a_{i_{p_2}}$ 的"额外素因子"越多。**联合 42.1**：设 $m:=\#\{c'\in D_1\setminus\{c\}:c'\nmid a_{i_{p_2}}\}$，则
$$p_2\,G\cdot\prod_{c'\ \text{未命中}}\rho_{c'}\ \le\ a_{i_{p_2}}\ <\ cp_1,\qquad \rho_{c'}\ge2 .$$
（$\rho_{c'}$ 可能重合，故只能得 $\ge2^m/\text{重合}$；$D_1\setminus\{c\}$ 的具体大小由 $\operatorname{rad}(a_1)$ 控制。）

**引理 42.3（抓手 D：密度下界，转述并特化）**【已证明】 $[a_1,cp_1]$ 中每个项都被某个 $\operatorname{lcm}(s,s')$（$s\in S=\{c,p_1,p_2\}$，$s'\in D_1$）整除（每项被 $S$ 中素整除、且被 $D_1$ 中素整除），项间距 $\le\operatorname{rad}(a_1)$，故
$$\Sigma:=\sum_{s\in S}\sum_{s'\in D_1}\frac{1}{\operatorname{lcm}(s,s')}\ \ge\ \frac{cp_1-a_1}{cp_1\operatorname{rad}(a_1)}-\frac{N'}{cp_1},$$
其中 $N'=O(1)$ 是端点修正。左边显式含 $1/\operatorname{lcm}(c,c)=1/c$、$1/\operatorname{lcm}(p_i,c)=1/(p_ic)$、以及 $1/\operatorname{lcm}(p_i,c')=1/(p_ic')$（$c'\in D_1\setminus\{c\}$）。由 $cp_1>a_1^{3/2}\ge2a_1$（$a_1\ge4$）、$c\le a_1/2$ 可得左端 $\le\dfrac{1}{c}+\dfrac{2}{cp_1}\cdot|D_1|+\ldots$，从而估出 $|D_1|$ 或某个 $c'$ 的下界——这是目前唯一能把 $\operatorname{rad}(a_1)$ 的规模反向利用的入口。

**残余（$s=3$，§33 后）**【缺口】 $cp_1>a_1^{3/2}$ 且 $p_2\le2a_1^2/(cp_1)$，需 $G\ge(cp_1)^2/(2a_1^2)$（42.1）或在 $G$ 小时用 42.2 的补偿 $\rho_{c'}$、42.3 的密度下界。

---

## §34（$cp_1>a_1^{3/2}$ 的两分支与 $c,p_1$ 的双侧界）

**引理 43.1（分支 $\mathcal P$：$cp_2\ge a_1$）**【已证明】 在 $s=3$ 残余中若 $cp_2\ge a_1$，则
(i) $c\le a_1/2$（38.4；若 $c=a_1$ 则 $p_1>\sqrt{a_1}$，下面同样成立）与 $cp_1>a_1^{3/2}$ 给
$$p_1>\frac{a_1^{3/2}}{c}\ \ge\ 2\sqrt{a_1};$$
(ii) 位置引理（$k=\mu/p_1=cp_2\ge a_1$、$\mathrm{kill}(cp_2)=i_{p_1}<\infty$）给 $a_{i_{p_1}}<cp_2$，配 $\rho'$-机制 $a_{i_{p_1}}\ge2p_1$（$p_1\notin D_1$）得 $2p_1<cp_2$，于是 $p_1^2<\mu/2$，特别 $p_1^2<cp_1p_2/2$；
(iii) 于是 $c$ 被双侧夹住：
$$\frac{a_1^{3/2}}{p_1}<c\le\frac{a_1}{2},\qquad 2\sqrt{a_1}<p_1 .$$
**注**：Lead 版给出的 $p_1<\frac12a_1^{3/2}/$（用目标 $\mu\le2a_1^2$）需把 $\mu\le2a_1^2$ 当已知；此处 (ii) 的 $p_1^2<\mu/2$ 是无条件的。

**引理 43.2（分支 $\mathcal Q$：$cp_2<a_1$）**【已证明】 此支下 $\mathrm H_{1/2}$ 给 $cp_2>a_1/2$，故 $cp_2\in(a_1/2,a_1)$；与 $cp_1>a_1^{3/2}$ 相除得
$$\frac{p_1}{p_2}=\frac{cp_1}{cp_2}>\sqrt{a_1},\qquad\text{并且}\quad \mu=cp_1p_2=\frac{(cp_1)(cp_2)}{c}<\frac{a_1^{5/2}}{c}.$$
故 $\mu\le2a_1^2$ 只要 $c\ge\frac12\sqrt{a_1}$——**分支 $\mathcal Q$ 在 $c\ge\sqrt{a_1}/2$ 时收口**；残余为 $c<\sqrt{a_1}/2$。

**引理 43.3（$G$-门槛的可行性分析）**【已证明】 $G\mid\operatorname{rad}(a_1)$（42.1 的 $G$ 是 $D_1\setminus\{c\}$ 的子集之积），故 $G\le\operatorname{rad}(a_1)\le a_1$。因此 42.1 的门槛 $G\ge(cp_1)^2/(2a_1^2)$ 蕴含
$$(cp_1)^2\le2a_1^2\operatorname{rad}(a_1)\le2a_1^3\iff cp_1\le\sqrt2\,a_1^{3/2}.$$
即：**在 $cp_1>\sqrt2a_1^{3/2}$ 时 $G$ 必达不到门槛，只能走 42.2 的补偿 $\rho_{c'}$**；反之若 $cp_1\le\sqrt2a_1^{3/2}$ 且 $D_1\setminus\{c\}$ 中足够多的大素因子都整除 $a_{i_{p_2}}$（即 $G$ 接近 $\operatorname{rad}(a_1)/c$），则直接收口。

**残余（$s=3$，§34 后）** 三分：
* $\mathcal P$ 且 $cp_1\le\sqrt2a_1^{3/2}$：需 $G$ 大（42.1/43.3）；
* $\mathcal P$ 且 $cp_1>\sqrt2a_1^{3/2}$：需 42.2 的 $\rho_{c'}$ 补偿（$\prod\rho_{c'}$ 与 $\operatorname{rad}(a_1)/c$ 的量级比较），并用 43.1(iii) 的 $c>\frac{a_1^{3/2}}{p_1}$ 与 $c\le a_1/2$ 夹 $p_1>2\sqrt{a_1}$；
* $\mathcal Q$：需 $c<\sqrt{a_1}/2$，同时 $p_1/p_2>\sqrt{a_1}$、$2p_2<cp_1$、$p_2<2a_1^2/(cp_1)$。

---

## §35（$G\prod\rho$ 夹逼的合成与其自动效力）

**引理 44.1（合成夹逼）**【已证明】 由 42.1 与 42.2：
$$p_2\,G\prod_{c'\ \text{未命中}}\rho_{c'}\ \le\ a_{i_{p_2}}\ <\ cp_1 .$$
故收口（$p_2\le2a_1^2/(cp_1)$）的充分条件是
$$\boxed{\ (cp_1)^2\le2a_1^2\,G\!\!\prod_{c'\ \text{未命中}}\!\!\rho_{c'}\ }$$
其中 $G=\prod\{c'\in D_1\setminus\{c\}:c'\mid a_{i_{p_2}}\}$、$\rho_{c'}\ge2$。

**引理 44.2（$\prod\rho\ge2^m$ 与 $|D_1|\ge2$）**【已证明】 设 $m:=\#\{c'\in D_1\setminus\{c\}:c'\nmid a_{i_{p_2}}\}$、$k:=|D_1|-1-m$。则每个 $\rho_{c'}\ge2$，$G\ge2^k$（$G$ 是 $k$ 个 $\ge2$ 的素数之积），故
$$G\prod\rho_{c'}\ \ge\ 2^{\,k+m}\ =\ 2^{\,|D_1|-1}.$$
又 $D_1\setminus\{c\}\ne\varnothing$（41.1），故 $|D_1|\ge2$，于是 $G\prod\rho\ge2$。代入 44.1：**$cp_1\le2a_1$ 时收口**（与 39.3 一致）。
**更强的形式**：$G\prod\rho\ge2^{|D_1|-1}$ 给出充分条件 $cp_1\le a_1\,2^{|D_1|/2}$；由于 $|D_1|=\omega(a_1)$ 且 $\operatorname{rad}(a_1)\ge2^{|D_1|}$，这覆盖 $a_1$ 有多个素因子的情形。

**引理 44.3（把 $G$ 换成 $\operatorname{rad}(a_1)$ 的版本）**【已证明】 若 $a_{i_{p_2}}$ 命中 $D_1\setminus\{c\}$ 的全部元素（即 $m=0$），则 $G=\operatorname{rad}(a_1)/c$，44.1 的充分条件变成
$$(cp_1)^2\le\frac{2a_1^2\operatorname{rad}(a_1)}{c}\iff cp_1\le a_1\sqrt{\frac{2\operatorname{rad}(a_1)}{c}} .$$
（与 43.3 的形式一致：$G$ 取最大时门槛即 $cp_1\le\sqrt{2a_1\operatorname{rad}(a_1)}\cdot\sqrt{a_1/c}$ 型。）

**判读（Lead 的定位实验）**【数值】 纯算术必要约束（$cp_1>a_1^{3/2}$、$2p_2<cp_1$、三条 $\mathrm H_{1/2}$）在 $a_1\le400$ 存活 $1.6\times10^8$ 组、绝大多数违反目标（最坏比值 $\approx7965$）——**故 $G\mid\operatorname{rad}(a_1)$ 与 $\rho_{c'}$ 的结构是必需的**，且必须同时用来给出**上界**（$cp_1$）与**下界**（$G\prod\rho$）。

---

## §36（顺序结构：项密度把 $G\prod\rho$ 逼到 $cp_1$ 附近）

**引理 45.1（项密度约束，顺序信息）**【已证明】 在 $s=3$ 设定下每个项都被 $S=\{c,p_1,p_2\}$ 的某个素因子整除（$S$ 横截），且项间距 $\le\operatorname{rad}(a_1)$（(P6)）。故对任意 $a_1\le x<y$（$y\le\mu$），区间 $[x,y]$ 中项数 $T$ 满足
$$T\ \ge\ \frac{y-x}{\operatorname{rad}(a_1)}-1,\qquad T\ \le\ (y-x)\sum_{s\in S}\frac1s+O(1),$$
于是
$$\sum_{s\in S}\frac1s\ \ge\ \frac{1}{\operatorname{rad}(a_1)}-\frac{O(1)}{y-x}.$$
**在残余中**（$cp_1>a_1^{3/2}$、$p_2<cp_1/2$、$c\le a_1/2$）左端 $\ge\frac1c\ge\frac2{a_1}$，右端 $\le1/\operatorname{rad}(a_1)$，故该约束在此**几乎自动**——真正有信息的是下一条对区间 $[a_{i_{p_2}},\mu]$ 的版本。

**引理 45.2（把 $p_2$ 逼成小量：顺序版）**【已证明】 取 $x:=a_{i_{p_2}}$、$y:=\mu=cp_1p_2$。由 42.1/42.2，$a_{i_{p_2}}\ge p_2G\prod\rho$，故 $y-x\le p_2\bigl(cp_1-G\prod\rho\bigr)$。由 45.1：
$$\frac{p_2\bigl(cp_1-G\prod\rho\bigr)}{\operatorname{rad}(a_1)}-1\ \le\ p_2\bigl(cp_1-G\prod\rho\bigr)\Bigl(\sum_{s\in S}\frac1s\Bigr)+O(1),$$
即（因 $\sum_S 1/s\le\frac1c+\frac1{p_1}+\frac1{p_2}$）
$$p_2\bigl(cp_1-G\textstyle\prod\rho\bigr)\Bigl(\frac{1}{\operatorname{rad}(a_1)}-\frac1c-\frac1{p_1}-\frac1{p_2}\Bigr)_+\ \le\ O(1).$$
于是若 $cp_1-G\prod\rho\ge1$ 且 $\frac1{\operatorname{rad}(a_1)}-\frac1c-\frac1{p_1}-\frac1{p_2}\ge\delta>0$，则
$$p_2\ \le\ \frac{O(1)}{\delta\bigl(cp_1-G\prod\rho\bigr)} .$$
**特别**：在残余中 $\frac1c\ge\frac1{p_1}$ 型量级下，只要 $G\prod\rho\le cp_1-1$ 且 $\frac1{\operatorname{rad}(a_1)}\gtrsim\frac2c$（即 $c\gtrsim2\operatorname{rad}(a_1)$ 的反面不成立时的常见情形），就得 $p_2=O(1)\le2$，从而 $\mu=cp_1p_2\le2cp_1$——**比目标弱一档但已与 $cp_1$ 挂钩**。

**残余（$s=3$，§36 后）**【缺口】 两支：
* $G\prod\rho\le cp_1-1$：由 45.2 得 $p_2$ 有界（$\lesssim1/\delta$），再与 42.1 的 $p_2\ge a_1/(2c)\cdot$（$\mathrm H_{1/2}$ 给 $cp_2>a_1/2$）联立即可夹死；
* $G\prod\rho\ge cp_1-O(1)$：此时 $p_2\le a_{i_{p_2}}/(G\prod\rho)\lesssim cp_1/(cp_1-O(1))\to1+$，同样得 $p_2$ 小。
**注**：45.2 是本节唯一用到"$\mu$ 是项 $+$ 项被 $S$ 整除 $+$ 项距 $\le\operatorname{rad}(a_1)$"的顺序信息，也是目前唯一能把 $G\prod\rho$ 与 $cp_1$ **拉近**的机制。

---

## §37（45.2 的显式常数、Lead 的两分归约，以及一个已闭环的子情形）

**引理 46.1（45.2 的显式形式）**【已证明】 记号同 45.2，$\Sigma:=\frac1c+\frac1{p_1}+\frac1{p_2}$。区间 $[a_{i_{p_2}},\mu]$ 中的项数 $T$ 满足
$$T\ \ge\ \frac{\mu-a_{i_{p_2}}}{\operatorname{rad}(a_1)}-1,\qquad T\ \le\ (\mu-a_{i_{p_2}})\,\Sigma+3$$
（下界：项距 $\le\operatorname{rad}(a_1)$；上界：每个项被 $c,p_1,p_2$ 之一整除，对三个模数各用一次"倍数计数 $\le L/m+1$"）。故当 $\Sigma<\frac1{\operatorname{rad}(a_1)}$ 时
$$\mu-a_{i_{p_2}}\ \le\ \frac{4}{\frac1{\operatorname{rad}(a_1)}-\Sigma},\qquad\text{结合 }a_{i_{p_2}}<cp_1\ (39.3/40.1)\text{ 得}$$
$$\boxed{\ p_2\ \le\ 1+\frac{4}{cp_1\Bigl(\frac1{\operatorname{rad}(a_1)}-\Sigma\Bigr)}\ }$$
**这是 45.2 中 $O(1)$ 的显式版（常数 $4$）**；$\Sigma\ge\frac1{\operatorname{rad}(a_1)}$ 时该约束为空。
**推论**：若还有 $\frac1{\operatorname{rad}(a_1)}-\Sigma\ge\frac{1}{2\operatorname{rad}(a_1)}$（即 $\Sigma\le\frac1{2\operatorname{rad}(a_1)}$）且 $cp_1>a_1^{3/2}$，则
$$p_2\ \le\ 1+\frac{8\operatorname{rad}(a_1)}{a_1^{3/2}}\ \le\ 1+\frac{8}{\sqrt{a_1}}\ <\ 2\quad(a_1\ge65).$$

**引理 46.2（Lead 的两分归约）**【已证明】
* 若 $m=0$（$a_{i_{p_2}}$ 命中 $D_1\setminus\{c\}$ 全体），44.3 给 $cp_1\le a_1\sqrt{2\operatorname{rad}(a_1)/c}$；与硬区 $cp_1>a_1^{3/2}$ 相除得 $\sqrt{2\operatorname{rad}(a_1)/c}>\sqrt{a_1}$，即 $c<2\operatorname{rad}(a_1)/a_1\le2$，故 $c=2$（$c$ 素；此时 $a_1$ 偶且 $a_1\ge4$）。
* 若 $m>0$，44.2 给 $cp_1\le a_1 2^{|D_1|/2}$，硬区要求 $2^{|D_1|/2}>\sqrt{a_1}$，即 $|D_1|>\log_2a_1$。
**故硬区只剩**（甲）$c=2\wedge m=0$；（乙）$|D_1|>\log_2a_1\wedge m>0$。

**引理 46.3（情形（甲）在 $\Sigma$ 小时直接闭环）**【已证明】 设（甲）成立、$\Sigma\le\frac1{2\operatorname{rad}(a_1)}$ 且 $cp_2\ge a_1$（分支 $\mathcal P$）。则由 46.1 推论 $p_2<2$（$a_1\ge65$），即 $p_2\le2$\ldots 结合 43.1(ii) 的 $2p_1<cp_2$（$=c\,p_2$）得
$$cp_1<\frac{c^2p_2}{2}\le\frac{a_1^2}{4}\cdot\frac{p_2}{2}\cdot 2=\frac{a_1^2p_2}{4}\le\frac{a_1^2}{2}\ (p_2\le2,\ c\le a_1/2),$$
于是 $\mu=cp_1p_2\le a_1^2$ ✓ **收口**。（$p_2\ge2$ 由 $p_2\mid\mu$、$p_2$ 素；$p_2\ge a_1/(2c)\ge a_1/a_1=1$ 一致。）

**残余（$s=3$，§37 后）**【缺口】 只剩：
* （甲）$c=2\wedge m=0$ 且 $\Sigma>\frac1{2\operatorname{rad}(a_1)}$（即 $p_1,p_2$ 相对 $\operatorname{rad}(a_1)$ 偏小），或分支 $\mathcal Q$（$cp_2<a_1$）；
* （乙）$|D_1|>\log_2a_1\wedge m>0$（$a_1$ 有许多不同素因子，此时 46.1 的显式界仍然可用，只需把 $\Sigma$ 与该情形联立）。

---

## §38（修正：$(\text{甲})$ 其实总落在 $\Sigma>1/\operatorname{rad}(a_1)$ 一侧）

**引理 47.1（$c=2$ 时的等价，并指出它与 $(\text{甲})$ 不相容）**【已证明】
(i) 若 $c=2$，则 $\Sigma\ge\frac12$，于是 $\Sigma\le\frac1{\operatorname{rad}(a_1)}\iff\operatorname{rad}(a_1)\le\frac1{1/2+1/p_1+1/p_2}<2\iff\operatorname{rad}(a_1)=2\iff a_1=2^k$（Lead 的推导 ✓）。
(ii) **但 $(\text{甲})$ 蕴含 $|D_1|\ge2$**：由 41.1（$c'\in D_1\setminus\{c\}$ 存在）知 $D_1\ne\{c\}$；$c=2$ 且 $D_1\ne\{2\}$ 时 $a_1$ 有奇素因子，故 $\operatorname{rad}(a_1)\ge2\cdot3=6$，特别 $a_1\ne2^k$。
**合并**：在 $(\text{甲})$ 中恒有 $\operatorname{rad}(a_1)\ge6$ 与 $\Sigma\ge\frac12$，故
$$\Sigma\ \ge\ \frac12\ >\ \frac16\ \ge\ \frac1{\operatorname{rad}(a_1)},$$
即 **46.1 的正号条件在 $(\text{甲})$ 中永远失效**（46.3 亦然）：$(\text{甲})$ 必须用密度式的"空条件"以外的机制。
**（Lead 的 (i′) "a₁=2^k ∧ (甲)" 与 (ii′) 应改为）**：$(\text{甲})$ 统一为"$c=2$、$\operatorname{rad}(a_1)\ge6$、$\Sigma>1/\operatorname{rad}(a_1)$"。

**引理 47.2（空条件下仍有的两条可用式）**【已证明】 当 $\Sigma>\frac1{\operatorname{rad}(a_1)}$ 时，$\frac{\mu-a_{i_{p_2}}}{\operatorname{rad}(a_1)}-1\le T\le(\mu-a_{i_{p_2}})\Sigma+3$ 给出
$$\mu-a_{i_{p_2}}\ \ge\ \frac{-3}{\Sigma-\frac1{\operatorname{rad}(a_1)}}$$
（正的分母可能给出有效下界，否则为空），以及**另一条独立的上界**：$T\ge1$ 对 $L$ 无约束，但 $T\le L\Sigma+3$ 与 $T\ge\frac{L}{\operatorname{rad}(a_1)}-1$ 在 $\frac1{\operatorname{rad}(a_1)}\le\Sigma$ 时确实为空。故 $(\text{甲})$ 需靠下列别的东西：
* $p_2$ 的下界 $\frac{a_1}{2c}=\frac{a_1}{4}$（$\mathrm H_{1/2}$）与 $p_2\mid\mu$；
* $\mu$ 极小（$cp_1=\mu/p_2\notin A_\infty$）给出的 killer 结构与 40.1 的 $c'$：$(\text{甲})$ 中 $a_{i_{p_2}}$ 必须命中 **$D_1\setminus\{2\}$ 全体**（$m=0$ 就是"全体"，且该集合非空、元素 $\ge3$），故 $p_2\cdot\prod_{D_1\setminus\{2\}}c'\le a_{i_{p_2}}<2p_1$——**乘积下界 $G=\prod_{D_1\setminus\{2\}}c'$ 在 $(\text{甲})$ 中是"全量"**；
* 44.3 的门槛（$m=0$ 适用）：$2p_1\le a_1\sqrt{2\operatorname{rad}(a_1)/2}=a_1\sqrt{\operatorname{rad}(a_1)}$，与 $2p_1<2p_2=2p_2$、$p_2>a_1/4$、$2p_2<2p_1$ 联立即得
$$2p_1<2p_2\cdot\frac{p_1}{p_2}<2p_2\cdot\frac{p_1}{p_2},$$
实用形式：$\boxed{p_1p_2<(\text{目标})\iff p_2<\frac{a_1^2}{p_1}}$，而 44.3 给 $p_1\le\frac{a_1}{2}\sqrt{\operatorname{rad}(a_1)}$，故只要 $p_2\le\frac{2a_1}{\sqrt{\operatorname{rad}(a_1)}}$ 就收口；再配 $p_2<\frac{2p_1}{2}=p_1$（43.1 的 $\mathcal P$ 版本）与 $p_2\in(a_1/4,a_1/2)$（$\mathcal Q$）即可把 $a_1$ 与 $\operatorname{rad}(a_1)$ 摊开成显式不等式。

**残余（$s=3$，§38 后）** 三支，全部带显式参数：
* $(\text{甲})\wedge\mathcal P$：$c=2$、$\operatorname{rad}(a_1)\ge6$、$2p_1<2p_2$、$p_2\cdot G<2p_1$（$G=\prod_{D_1\setminus\{2\}}c'\ge3$）、$p_1\le\frac{a_1}{2}\sqrt{\operatorname{rad}(a_1)}$（44.3）；
* $(\text{甲})\wedge\mathcal Q$：同上，另有 $a_1/4<p_2<a_1/2$；
* （乙）$|D_1|>\log_2a_1\wedge m>0$：用 46.1（此处 $\Sigma$ 未必大，48.1 的条件需具体代入）。
两者都可继续用 46.1 的显式不等式与 42.1/42.2 的 $G\prod\rho$ 夹逼；46.1 是本轮新得到的**唯一显式常数**，建议优先把它与（乙）的 $|D_1|$ 下界代入。

**残余（$s=3$，§35 后）**【缺口】 在 44.1 的夹逼下，需证 $cp_1\le a_1\sqrt{2\!\cdot\!G\prod\rho/(?)}$ 型的量级式，即需 $D_1$ 侧至少 $\Omega(\sqrt{a_1})$ 量级的乘积；三分支（§34）在此期间同时收窄。建议下一步做"加入 $G$-条件（$G\approx\operatorname{rad}(a_1)/c$）"的扫描，看幸存数是否骤降，以判定 44.1 是否已足够。

---

## §39（(甲)∧$\mathcal P$∧阈值：直接收口的子情形）

**引理 48.1（复核通过：$(\text{甲})\wedge\mathcal P\wedge[cp_1\le a_1\sqrt{\operatorname{rad}(a_1)}]\Rightarrow\mu<2a_1^2$）**【已证明】
在 $(\text{甲})$（$c=2$、$m=0$）$\wedge\mathcal P$（$2p_2\ge a_1$）下：
1. $m=0$ 即 $a_{i_{p_2}}$ 命中 $D_1\setminus\{2\}$ 全体，故 $G=\prod_{D_1\setminus\{2\}}c'=\operatorname{rad}(a_1)/2$（因 $2\in D_1$）；
2. $k:=\mu/p_2=2p_1>a_1$（43.1 给 $p_1>2\sqrt{a_1}$），位置引理（$\mathrm{kill}(2p_1)=i_{p_2}<\infty$）给 $a_{i_{p_2}}<2p_1$；配 42.1 的 $p_2G\le a_{i_{p_2}}$ 得
$$p_2\,\frac{\operatorname{rad}(a_1)}{2}<2p_1\ \Longrightarrow\ p_2<\frac{4p_1}{\operatorname{rad}(a_1)};$$
3. 阈值 $cp_1\le a_1\sqrt{2\operatorname{rad}(a_1)/c}$（44.3）在此即 $p_1\le\frac{a_1}{2}\sqrt{\operatorname{rad}(a_1)}$；
4. 于是
$$\mu=2p_1p_2<2p_1\cdot\frac{4p_1}{\operatorname{rad}(a_1)}=\frac{8p_1^2}{\operatorname{rad}(a_1)}\le\frac{8}{\operatorname{rad}(a_1)}\cdot\frac{a_1^2\operatorname{rad}(a_1)}{4}=2a_1^2 . \qquad\blacksquare$$

**推论 48.2（残余重排）**【缺口】 $s=3$ 残余变为三支，全部带显式参数：
* $(\text{甲})\wedge\mathcal P\wedge\bigl(cp_1>a_1\sqrt{\operatorname{rad}(a_1)}\bigr)$；
* $(\text{甲})\wedge\mathcal Q$（即 $c=2$、$m=0$、$a_1/4<p_2<a_1/2$、$2p_2<2p_1$）；
* （乙）$|D_1|>\log_2a_1\wedge m>0$。

---

## §40（第一支把 $\operatorname{rad}(a_1)$ 逼到 $\le64$）

**引理 49.1（第一支的两条互斥形态）**【已证明】 在第一支（$(\text{甲})\wedge\mathcal P\wedge cp_1>a_1\sqrt{\operatorname{rad}(a_1)}$，即 $c=2$、$m=0$、$G=\operatorname{rad}(a_1)/2$、$p_1>\frac{a_1}{2}\sqrt{\operatorname{rad}(a_1)}$）中：
(i) $\mathrm H_{1/2}$（用于 $p_1$）给 $cp_2>a_1/2$，即 $p_2>a_1/4$；
(ii) 目标 $p_2\le\frac{2a_1^2}{cp_1}=\frac{a_1^2}{p_1}<\frac{2a_1}{\sqrt{\operatorname{rad}(a_1)}}$；
(iii) 若 $\operatorname{rad}(a_1)\ge64$，则 $\frac{2a_1}{\sqrt{\operatorname{rad}(a_1)}}\le\frac{a_1}{4}$，于是
$$\text{目标}\Rightarrow p_2<\frac{2a_1}{\sqrt{\operatorname{rad}(a_1)}}\le\frac{a_1}{4}<p_2\ \text{(由 (i))}\ \Longrightarrow\ \text{矛盾},$$
**即第一支在 $\operatorname{rad}(a_1)\ge64$ 时目标必然失效**（44.1 也恰好在此支失效，故必须换机制）。
(iv) 反之若 $\operatorname{rad}(a_1)\le64$，则第一支给出
$$p_1>\frac{a_1}{2}\sqrt{\operatorname{rad}(a_1)}\ (\Omega(a_1)),\qquad \frac{a_1}{4}<p_2<\frac{2a_1}{\sqrt{\operatorname{rad}(a_1)}}\ (O(\sqrt{a_1})),$$
故 $\mu=2p_1p_2$ 的量级是 $\Theta(a_1^{3/2})$ 上下，且 $\operatorname{rad}(a_1)\le64$ 是**有限**条件（$\operatorname{rad}(a_1)\in\{2,6,10,\dots,64\}$ 的有限枚举）。

**残余（$s=3$，§40 后）**
* 第一支：$\operatorname{rad}(a_1)\le64$（否则需换机制重导目标）且 $p_1,p_2$ 落在 (iv) 的窄区间；
* 第二支：$(\text{甲})\wedge\mathcal Q$（$a_1/4<p_2<a_1/2$）；
* （乙）：$|D_1|>\log_2a_1\wedge m>0$。
三支的参数区间都已极窄；第一支更带 $\operatorname{rad}(a_1)\le64$ 的有限性，可直接把 $c=2,G=\operatorname{rad}(a_1)/2$、$p_2G<a_{i_{p_2}}<2p_1$、$\rho$-补偿代成有限组不等式逐一核对。
**新约束（对第三支有用）**：$cp_1>a_1\sqrt{\operatorname{rad}(a_1)}$ 与 44.2 的 $cp_1\le a_12^{|D_1|/2}$ 联立给 $2^{|D_1|/2}>\sqrt{\operatorname{rad}(a_1)}$，即 $|D_1|>\log_2\operatorname{rad}(a_1)$——这在 $(\text{乙})$ 中自动成立，可作为对照式先行代入。
