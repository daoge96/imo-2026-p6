# IMO 第 6 题：完整证明（Lead 定稿 v3，回应外部评语的 §5 修正）

> 结论：**FME 成立**（$A_\infty$ 只有有限多个极小元，且其素因子全 $\le 2a_1$），由 FME 直接推出题设的 $a_{n+T}=a_n+L$。
>
> **v3 变更（针对外部评语 `D:\OneDrive\Desktop\30号证明评语.md`，评语经逐行核对确认为真）**：v2 的 §5 引理 5.1 第 4 步写 “$\nu/p\ge\nu/2>a_1$”，**该式只对 $p=2$ 成立**（$p\ge3$ 时 $\nu/p\le\nu/2$），故引理 3.1 的前提 $k=\nu/p\ge a_1$ 未建立。修正办法是**改假设而非改推理**：引理 5.1 的假设改为 $\nu>a_1p$（此时 $\nu/p>a_1$，原第 4 步逐字成立），并由此得到 $E_p:=\{\mu\in\mathcal M:p\mid\mu\}$ 的**无条件**界 $\min E_p\le a_1p$（引理 5.2）。于是全部缺口收敛为**唯一一条残余命题 $R$**（定义 5.3）：$\exists$ 素 $p,\exists\mu\in\mathcal M$ 使 $p\mid\mu,\ p>2a_1,\ 2a_1<\mu\le a_1p$。**$\neg R\Rightarrow$ 原引理 5.2（$p\le2a_1$）$\Rightarrow$ FME $\Rightarrow$ 原题**（引理 5.4、定理 5.5，完全严格）。
>
> 数值：$R$ 在 $a_1\le10^4$（$B=6a_1$，并做 $B=3a_1/6a_1/10a_1$ 稳定性）内从未出现；$\max\mu/(2a_1)=0.7241$（$a_1=899,\mu=1302=2\cdot3\cdot7\cdot31$）；$\max p/a_1=1$。见 `logs/claimB_scan.py`、`logs/cofactor_scan.py`、`17-fme-indep.md` §4。
>
> 两条互不通信的独立路线（`16-descent-fix.md`（prover-descent）、`17-fme-indep.md`（prover-mu））独立收敛到同一条 $R$；`16` 另证：$R\iff\neg$(素因子界)（引理 5.3″，即 $R$ 不多不少正是所需命题），且**若 $R$ 成立则 v2 的引理 5.1 为假**（命题 5.3‴，故"改假设"是必需的），并给出 $R$ 的刚性结构（§5.7）与三条充分路线。
>
> 其余部分：§1–§4、§5（修正版）、§6（在 $\neg R$ 下）、§7、§8 全部自足；核心下降引理来自 prover-tcl 的 `10-tcl-proof.md`（同处亦有该不等式瑕疵，Lead 已复核）。
>
> **最新收窄（§5.8）**：$R$ 已进一步等价于单条不等式 $(L)$：$\exists q\mid t$（$q$ 素、$q\mid a_1$）使 $\sigma:=\nu_p\le a_1q$；$(L)\Rightarrow(b)\Rightarrow\neg R$（命题 5.8）。$Q_p:=\{q\mid t,q\mid a_1\}=\varnothing\Rightarrow p\mid a_1$（反向不成立，70 例反例），而 $p\mid a_1$ 时 $p\le a_1$ 已证（16.16(a)）。$\neg L$ 下引理 5.1′ 沿每个 $q\in Q_p$ 可用，配合 $\mathcal M$-链二分把 $(L)$ 归结为 **stall 支**：存在 $\mu^\ast\in\mathcal M$（$p\nmid\mu^\ast$、$p\mu^\ast\in A_\infty$、$\operatorname{rad}(p\mu^\ast)$ 无 $p$-含 $\mathcal M$-因子）使 $p\mu^\ast\le a_1q$。数值：$a_1\le2000$ 内 355 个 $Q_p\ne\varnothing$ 实例全部满足 $(L)$，最小余量 5 倍（两套独立实现一致）。
>
> **定稿状态（本文件即交付物，v3）**：§1–§4、§5（含 5.1′–5.6、§5.7 钳制、§5.8 全部充分路线与最窄缺口）、§6（在 $\neg R$ 下）、§7、§9 已全部自足且经两轮对抗复核（`23-verification-L.md` 14 项通过、无反驳；`21-verification-v3.md`）。**三条充分路线任一成立即无条件闭环**，均零反例（余量 1.4–5 倍）：
> $$(CS)\Rightarrow\text{FME}\Rightarrow\text{原题};\qquad (b'')\Rightarrow(L)\Rightarrow(b)\Rightarrow\neg R;\qquad (b'')\Rightarrow(c)\Rightarrow\neg R .$$
> 现缺口的最窄形式见 §5.8（$(CS)$ 的 $(\star\star)$／$|S|=2$ 约束清单 24.3／$Q^\ast\ne\varnothing$ 时的 $a_{i_q}$ 上界；或 stall 支）。§10 给出闭环后升 v4 的机械接口。

## 1. 记号

固定整数 $a_1\ge2$，序列按题设定义。记
$$\operatorname{supp}(k)=\{p\ \text{素}:p\mid k\},\quad D_n=\operatorname{supp}(a_n),\quad P_n=\bigcup_{i\le n}D_i\ \ (\text{§9 的判据用到 } P_N,\ \text{主链不用}),$$
$$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \forall i\le n\},\qquad A_\infty=\bigcap_{n\ge1}A_n,$$
$$\mathrm{kill}(k)=\min\{i\ge1:\gcd(k,a_i)=1\}\ (\text{若无则}=\infty).$$
有限素数集 $S$ 称为 $\mathcal D_n=\{D_1,\dots,D_n\}$ 的**横截集**，若 $S\cap D_i\ne\varnothing\ (\forall i\le n)$。于是 $k\in A_n\iff\operatorname{supp}(k)$ 是 $\mathcal D_n$ 的横截集。

## 2. 基本事实

- **(P1)**（良定义、两两不互素）$M_n:=\operatorname{rad}(a_1\cdots a_n)$ 的每个倍数属 $A_n$，故 $a_{n+1}$ 存在；且 $a_{n+1}$ 与每个 $a_i\ (i\le n)$ 不互素，归纳得 $\gcd(a_i,a_j)>1\ (i\ne j)$，即每个 $D_j$ 是全族 $\{D_i\}$ 的横截集。
- **(P2)** 由 (P1)：每个 $a_j\in A_\infty$；更一般地，若 $k\in A_\infty$ 则 $\operatorname{supp}(k)$ 是横截集，故 $\operatorname{rad}(k)\in A_\infty$。特别 $A_\infty\ne\varnothing$。
- **(P3)** $A_{n+1}\subseteq A_n$，故 $A_\infty\subseteq A_n\subseteq A_m\ (m\le n)$。
- **(P4)** $a_{n+1}=\min\bigl(A_n\cap(a_n,\infty)\bigr)=\min\bigl(A_\infty\cap(a_n,\infty)\bigr)$。
  证明：记两端的集合为 $X_n\supseteq Y_n$（因 $A_\infty\subseteq A_n$），故 $\min X_n\le\min Y_n$；另一方面 $A_n$ 的每个元素 $\ge a_{n+1}$ 且 $a_{n+1}$ 与所有 $a_i\ (i\le n)$ 不互素，即 $a_{n+1}\in A_n$，而由 (P2) $a_{n+1}\in A_\infty$，故 $a_{n+1}\in Y_n$，于是 $\min Y_n\le a_{n+1}=\min X_n$。两端相等。∎
- **(P5)** 序列恰是 $A_\infty\cap[a_1,\infty)$ 的递增枚举（由 (P4)+ 归纳，且 (P2) 保证每个项都在 $A_\infty$）。
- **(P6)** $\operatorname{rad}(a_1)\in A_\infty$，故 $a_{n+1}-a_n\le\operatorname{rad}(a_1)$。
- **(K)** $k\in A_N\iff \mathrm{kill}(k)>N$；$k\in A_\infty\iff \mathrm{kill}(k)=\infty$。
- **(M)** $A_\infty$ 对取倍数封闭、对乘法封闭，且 $A_\infty\subseteq\{k\ge2\}$。

**定义 2.1** $k$ 是**项**，指 $\exists t\ge1:k=a_t$。$\mu\ge2$ 是 $A_\infty$ 的**极小元**，指 $\mu\in A_\infty$ 且不存在真因子 $\nu\mid\mu$（$\nu\mid\mu$、$2\le\nu<\mu$）使 $\nu\in A_\infty$。记 $\mathcal M$ 为全体极小元。

**引理 2.2** 每个 $k\in A_\infty$ 被某极小元整除，故 $A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$，且每个 $\mu\in\mathcal M$ 无平方因子。
证明：对 $k$ 强归纳（若 $k$ 非极小则有真因子 $\nu\in A_\infty$，$\nu\ge2$，用归纳假设）。无平方因子：若 $p^2\mid\mu$ 则 $\operatorname{rad}(\mu)$ 是 $\mu$ 的真因子且由 (P2) 属 $A_\infty$，矛盾。∎

## 3. 位置引理

**引理 3.1** 设 $k\ge a_1$ 且 $\mathrm{kill}(k)=i<\infty$。则 $a_i<k$。

证明：由 (K) $k\in A_{i-1}$、$k\notin A_i$，故 $k\notin A_\infty$；结合 $k\ge a_1$ 与 (P5) 知 $k$ **不是项**。
令 $u:=\max\{t:a_t\le k\}$（存在，因 $a_t\uparrow\infty$、$a_1\le k$），则 $a_u\le k$ 且由 $u$ 的极大性 $a_{u+1}>k$；又 $k$ 不是项故 $a_u\ne k$，于是
$$a_u<k<a_{u+1}. \tag{3.1}$$
若 $u\le i-1$，则由 (P3) $A_{i-1}\subseteq A_u$ 得 $k\in A_u$，与 (P4)：$a_{u+1}=\min(A_u\cap(a_u,\infty))\le k$，矛盾于 (3.1)。故 $u\ge i$，于是 $a_i\le a_u<k$。∎

## 4. 私有指标引理

**引理 4.1** 设 $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$，$T:=\operatorname{supp}(\mu)$。则 $\exists i\ge1$：$D_i\cap T=\{p\}$。

证明：$T$ 是横截集。若 $\mu=p$（即 $T=\{p\}$），则 $p\in D_i\ (\forall i)$，取 $i=1$。否则由引理 2.2，$\mu$ 无平方因子，故 $\operatorname{supp}(\mu/p)=T\setminus\{p\}$；又 $\mu/p\ge2$ 是 $\mu$ 的真因子，由极小性 $\mu/p\notin A_\infty$，令 $i:=\mathrm{kill}(\mu/p)<\infty$。则 $\gcd(\mu/p,a_i)=1$，即 $\operatorname{supp}(\mu/p)\cap D_i=\varnothing$，而 $\operatorname{supp}(\mu/p)=T\setminus\{p\}$，故 $D_i\cap T\subseteq\{p\}$；又 $T$ 横截给出 $D_i\cap T\ne\varnothing$，故 $D_i\cap T=\{p\}$。∎

## 5. 下降引理（修正版）、$E_p$ 的界与残余命题 $R$

**引理 5.1（下降，修正版）** 设 $\nu\in\mathcal M$，$p\in\operatorname{supp}(\nu)$，且 $\nu>a_1p$。则存在 $\nu'\in\mathcal M$ 使
$$p\in\operatorname{supp}(\nu'),\qquad \operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\},\qquad \nu'<\nu/p .$$

证明：记 $T:=\operatorname{supp}(\nu)$。由 $\nu>a_1p\ge a_1$ 与 (P5)，$\nu$ 是项：$\nu=a_j$，故 $T=D_j$ 是横截集；又由引理 2.2，$\nu$ 无平方因子，故 $\operatorname{supp}(\nu/p)=T\setminus\{p\}$。

1. $k:=\nu/p>a_1\ge2$，故 $k\ge a_1$；且 $k$ 是 $\nu$ 的真因子、$k\ge2$，由极小性 $k\notin A_\infty$，令 $i:=\mathrm{kill}(k)<\infty$（(K)）。
2. 由引理 3.1（前提 $k\ge a_1$，此处由 $k>a_1$ 保证）得 $a_i<k=\nu/p$。$\tag{5.1}$
3. $\gcd(k,a_i)=1\Rightarrow\operatorname{supp}(k)\cap D_i=\varnothing\Rightarrow D_i\cap T\subseteq\{p\}$；又 $D_i\cap T\ne\varnothing$（$T$ 横截），故 $D_i\cap T=\{p\}$。$\tag{5.2}$
4. 由 (5.1) 与 $k<\nu=a_j$、项严格递增得 $i<j$。由 (P2)，$a_i\in A_\infty$ 且 $R:=\operatorname{rad}(a_i)\in A_\infty$，$R\ge2$。
5. 取 $\nu'$ 为集合 $\mathcal F:=\{\nu''\ge2:\nu''\mid R,\ \nu''\in A_\infty\}$ 中的极小者（$\mathcal F\ne\varnothing\ni R$）。则 $\nu'\in\mathcal M$：若 $\nu''\mid\nu'$、$\nu''\in A_\infty$、$2\le\nu''<\nu'$，则 $\nu''\mid R$ 使 $\nu''\in\mathcal F$，与 $\nu'$ 极小矛盾。
6. $\operatorname{supp}(\nu')\subseteq\operatorname{supp}(R)=D_i$，结合 (5.2) 得 $\operatorname{supp}(\nu')\cap T\subseteq D_i\cap T=\{p\}$；又 $\nu'\in A_\infty$ 而 $T=D_j$ 横截，故 $\operatorname{supp}(\nu')\cap T\ne\varnothing$，于是 $\operatorname{supp}(\nu')\cap T=\{p\}$，特别 $p\in\operatorname{supp}(\nu')$。
7. $\nu'\le R\le a_i\overset{(5.1)}{<}\nu/p$。∎

> **与 v2 的差别**：v2 中“$\nu/p\ge\nu/2>a_1$”（第 4 步）只对 $p=2$ 成立；修正版把假设加强为 $\nu>a_1p$，于是 $k=\nu/p>a_1$ 直接给出引理 3.1 的合法前提，其余（步骤 3、5–7）与 v2 一致。原证明里“$\nu/p\ge2$”“$\nu\ne p$”等退化讨论已被 $k>a_1\ge2$ 吸收。

**引理 5.2（$E_p$ 的最小元有界，无条件）** 设 $p$ 为素数、$E_p:=\{\mu\in\mathcal M:p\mid\mu\}\ne\varnothing$，$\nu_p:=\min E_p$。则
$$\nu_p\le a_1p\qquad\bigl(\text{若另有 } p\le a_1,\ \text{则进一步 } \nu_p\le a_1p\le a_1^2\text{——但 } p\le a_1 \text{ 即路线 (b)，未证}\bigr).$$

证明：$\nu_p\ge p\ge2$。若 $\nu_p>a_1p$，则对 $(\nu,p):=(\nu_p,p)$ 用引理 5.1 得 $\nu'\in\mathcal M$、$p\mid\nu'$（故 $\nu'\in E_p$）、$\nu'<\nu_p/p<\nu_p$，与 $\nu_p=\min E_p$ 矛盾。∎

**定义 5.3（残余命题 $R$）** 称 $R$ 成立，若
$$\exists\ \text{素数}\ p,\ \exists\mu\in\mathcal M:\qquad p\mid\mu,\qquad p>2a_1,\qquad 2a_1<\mu\le a_1p .$$

**引理 5.3′（$R$ 的最窄等价形式）** $R\iff R'$，其中
$$R':\quad\exists\ \text{素数}\ p:\quad E_p\ne\varnothing,\qquad p>2a_1,\qquad \nu_p>2a_1 .$$
证明：($\Leftarrow$) 取 $\mu:=\nu_p$：$p\mid\nu_p$ 故 $\nu_p\ge p>2a_1$，于是 $2a_1<\nu_p$，又 $p>2a_1$，且 $\nu_p\le a_1p$（引理 5.2），故 $R$ 成立。
($\Rightarrow$) 设 $\mu\in E_p$、$p>2a_1$、$2a_1<\mu\le a_1p$。若 $\nu_p\le2a_1$，则 $p\le\nu_p\le2a_1$，与 $p>2a_1$ 矛盾；故 $\nu_p>2a_1$，即 $R'$。∎

**引理 5.3″（$R$ 恰是素因子界的取反；`16-descent-fix.md` 命题 16.9）** $R\iff\neg\bigl(\forall\mu\in\mathcal M,\forall p\mid\mu:p\le2a_1\bigr)$。
证明：后者等价于 $\forall p\ (E_p\ne\varnothing\Rightarrow p\le2a_1)$，其否定即 $\exists p:E_p\ne\varnothing\wedge p>2a_1$，而由引理 5.3′ 这正是 $R$。∎
故**残余 $R$ 不多不少就是所需命题**（无需再加强）。

**命题 5.3‴（改假设是必需的；`16` 命题 16.8）** 若 $R$ 成立，则 v2 的引理 5.1（假设 $\nu>2a_1$）为**假**。
证明：取 $p>2a_1$ 与 $\nu:=\nu_p$，则 $\nu\ge p>2a_1$ 满足 v2 假设；若其结论成立则得 $\nu'\in\mathcal M$、$p\mid\nu'$、$\nu'<\nu/p<\nu$，即 $\nu'\in E_p$ 小于 $\min E_p$，矛盾。∎
（即：在 $R$ 情形下 $\nu_p/p\le a_1$ 使位置引理**必然**失效，"改假设"不可回避。）

**引理 5.4（$\neg R\Rightarrow$ 素因子界，即 v2 的引理 5.2）** 若 $\neg R$，则
$$\forall\mu\in\mathcal M,\ \forall p\in\operatorname{supp}(\mu):\quad p\le2a_1 .$$

证明：设 $\mu\in\mathcal M$、$p\mid\mu$；则 $E_p\ni\mu\ne\varnothing$。归纳构造 $p$-链：$\nu_0:=\nu_p$；只要 $\nu_r>a_1p$ 就由引理 5.1 取 $\nu_{r+1}\in\mathcal M$ 使 $p\mid\nu_{r+1}$、$\nu_{r+1}<\nu_r/p$。这是严格递减的正整数列，必在有限步 $k$ 停；停机即 $\nu_k\le a_1p$，且由 $p\mid\nu_r(\forall r)$ 得 $p\mid\nu_k$。
若 $\nu_k\le2a_1$，则 $p\le\nu_k\le2a_1$ ✔。否则 $\nu_k>2a_1$ 且 $\nu_k\le a_1p$，于是若再有 $p>2a_1$，则 $(\mu,p):=(\nu_k,p)$ 使 $R$ 成立；故 $\neg R$ 时必有 $p\le2a_1$。∎

**定理 5.5（FME，$\neg R$ 版本 $=$ 定理 6.1）** 设 $\neg R$。则 $\mathcal M\subseteq\{k\ge2:k$ 无平方因子，$\operatorname{supp}(k)\subseteq\{p:p\le2a_1\}\}$，故 $|\mathcal M|\le2^{\pi(2a_1)}$ 且 $\mu\le\prod_{p\le2a_1}p$（$\forall\mu\in\mathcal M$）。于是 §6.3、§7 全部按原文成立，原题得证。

**命题 5.6（无条件部分与条件结构）** 引理 2.2、3.1、4.1、**5.1**、**5.2** 无条件成立；因此对每个使 $E_p\ne\varnothing$ 的素数 $p$ 有 $\min E_p\le a_1p$，且 $\mathcal M=\bigcup_{p\mid a_1}E_p$（每个 $\mu\in\mathcal M$ 的支撑与 $D_1$ 相交）。此外 §6.2（实现引理）无条件；而 §6.1（FME）、§6.3、§7（原题）**仅在 $\neg R$ 的假设下**使用。结构总结：
$$\underbrace{\text{(P1)–(P6),(K),(M), 引理 2.2,3.1,4.1,5.1,5.2}}_{\text{无条件}}\ \Longrightarrow\ \neg R\ \Longrightarrow\ \text{FME 定理 6.1}\ \Longrightarrow\ \S7\ \Longrightarrow\ \text{原题}.$$
即：**只要证明 $R$ 不成立（或直接证明引理 5.4 的结论），全文即无条件闭环**。

### 5.7 攻击 $R$ 的现成抓手（`16-descent-fix.md` §5、§7.2，已复核）

设 $R$ 成立并取 $\sigma:=\nu_p=pt$（$p>2a_1$，$t=\sigma/p$）。则以下事实全部**无条件可证**，构成 $R$ 的"刚性钳制"（`16` 引理 16.12–16.15）：

1. $2\le t<a_1$（严格），$t\notin A_\infty$，且 $t$ 的**每个** $\ge2$ 因子都 $\notin A_\infty$；
2. $\exists q\mid t$ 使 $q\mid a_1$；又 $p\nmid a_1$（否则 $p\le\operatorname{rad}(a_1)\le a_1<2a_1<p$，矛盾）；
3. 每个项 $a_s$ 被 $p$ 或 $t$ 的某个素因子整除；
4. $i:=\mathrm{kill}(t)$ 满足 $D_i\cap\operatorname{supp}(\sigma)=\{p\}$、$p\mid a_i$、$\gcd(a_i,t)=1$、$a_i/p\in\mathcal R_p$，且 $\operatorname{rad}(a_i)\ge\sigma$、$a_i\ge\sigma$、$\sigma\le a_{i-1}$；
5. 首个 $p$-可除项 $a_r$ 满足 $a_r\le\sigma$（$\sigma$ 本身即 $p$-可除的项）；又 $x_p^{\min}=p\tau_p$ 恒成立，且**当 $p\tau_p\ge a_1$ 时** $x_p^{\min}$ 是项，故此时 $a_r=x_p^{\min}=p\tau_p$（若 $p\tau_p<a_1$ 则 $x_p^{\min}<a_1$ 不是项，只能得 $a_r\ge p\tau_p$——`16` §13 的修正）；
6. 对 $\nu=\nu_p$，"$\operatorname{rad}(a_i)$ 的极小 $A_\infty$-因子"构造**必然**给 $\nu'\ge\sigma>\sigma/p$（故反驳 $R$ 不能只靠该构造）；
7. **（无条件）** 由 (P1) 每个 $D_s$ 与 $D_1$ 相交，故 $D_1$ 是 $p$-free 项族的横截集，即 $\operatorname{rad}(a_1)\in\mathcal R_p$，于是
   $$\tau_p\le\min\bigl(t,\operatorname{rad}(a_1)\bigr)\le a_1 .$$
   于是路线 (c)（$a_r\le2a_1$）的**分支 $\mathcal A$**（$p\tau_p\ge a_1$，含全部 $p>2a_1$）由 $p\min(t,\operatorname{rad}(a_1))\le2a_1$ 推出；**分支 $\mathcal B$**（$p\tau_p<a_1$）改用 $p\operatorname{rad}(a_1)\in A_\infty$（支撑 $D_1\cup\{p\}$ 横截）：若 $p\operatorname{rad}(a_1)\ge a_1$ 则 $a_r\le p\operatorname{rad}(a_1)$，故 (c) 由 $p\operatorname{rad}(a_1)\le2a_1$ 推出。此外 $t=1$ 时 $\sigma=p\mid$ 所有项、$F_p=\varnothing$、$\tau_p=1$、$a_r=a_1\le2a_1$——**(c) 在 $t=1$ 时成立**。数值：$a_r>2a_1$ 零反例、$\max a_r/a_1=1.2353$；且 $p\min(t,\operatorname{rad}(a_1))>2a_1$ 零例（即分支 $\mathcal A$ 的界在样本中总够用）。

由此得**三条充分路线**（任一条成立即 $\neg R$）：
$$\text{(a)}\ p\mid a_1\Rightarrow\neg R_p\ \text{【已证】};\qquad
\text{(b)}\ \forall p\ (E_p\ne\varnothing\Rightarrow p\le a_1);\qquad
\text{(c)}\ \forall p\ (E_p\ne\varnothing\Rightarrow a_r\le2a_1).$$
(b)、(c) 均未证；数值上 (b) 零反例（$a_1\le10^4$ 内 $\max p/a_1=1$，唯一取等 $a_1=p=2$），(c) 的等价形式是 $p\tau_p\le2a_1$。

### 5.8 把 $R$ 再收窄为单条不等式 $(L)$（`16-descent-fix.md` §10，已复核）

**定义 5.7（$(L)$）** 设 $p$ 素、$E_p\ne\varnothing$、$\sigma:=\nu_p$、$t:=\sigma/p$、$Q_p:=\{q\ \text{素}:q\mid t,\ q\mid a_1\}$（由 16.12(iv)，$p\nmid a_1$ 时 $Q_p\ne\varnothing$）。称
$$(L)\qquad \exists q\in Q_p:\quad \sigma\le a_1q .$$

**命题 5.8** $(L)\Rightarrow(b)\Rightarrow\neg R$。证明：$q\mid t\Rightarrow q\le t$，故 $p=\sigma/t\le a_1q/t\le a_1$，再用 16.16(b)。∎
（等价：$(L)\iff\exists q\in Q_p:\sigma/q\le a_1$，而 $\sigma/q\ge p$；故 $\neg L$ 即"对一切 $q\in Q_p$，引理 5.1′ 沿 $q$ 都可用"。）

**命题 5.8′（$(L)$ 与 $(b)$ 的关系；`16` §12.2 的更正）** $(L)\Rightarrow(b)$，但反之不成立。
证明：$(L)\Rightarrow(b)$ 即命题 5.8。反向失败的原因：$\neg R$ 只约束**素因子** $\le2a_1$，而 $\nu_p$ 是乘积——故不能由 $\neg R$ 得 $\nu_p\le2a_1$。
**正确的充分链**：命
$$(b'')\quad \forall p\ (E_p\ne\varnothing\Rightarrow\nu_p\le2a_1),$$
则 $(b'')\Rightarrow(L)$（任取 $q\in Q_p$，$q\ge2$，得 $\nu_p\le2a_1\le a_1q$），且 $(b'')\Rightarrow\neg R$；而 $(L)\Rightarrow(b)\Rightarrow\neg R$。
**故以下任一成立即闭环**：$(b)$：$\forall p(E_p\ne\varnothing\Rightarrow p\le a_1)$［最弱、足够］；$(L)$；$(b'')$：$\nu_p\le2a_1$［最强，数值上成立：$\max\nu_p/(2a_1)=0.6176$］。$p\mid a_1$ 时 $p\le a_1$ 已由 16.16(a) 给出。

**另一条充分路线 $(CS)$（"乘性"形式，不经过 $R$）**：
$$(CS)\qquad \forall\mu\in\mathcal M,\ \forall p\mid\mu:\quad \frac{\mu}{p}\le a_1 .$$
则 $\mu\le a_1\min\operatorname{supp}(\mu)\le a_1\max D_1\le a_1^2$（每个 $\mu$ 的支撑与 $D_1$ 相交，故 $\min\operatorname{supp}(\mu)\le\max D_1\le a_1$），于是 $\mathcal M\subseteq[2,a_1^2]$ 有限 $\Rightarrow$ FME $\Rightarrow$ §6.3、§7 成立（TCL 常数取 $\max\{2a_1^2,\prod_{p\le a_1}p\}$）。**$(CS)$ 与 $\neg R$ 互不包含**（$(CS)$ 不限制素因子大小），但两者都足以闭环。
数值：$(CS)$ 在 $a_1\le3000$ 全值零反例（$\max\mu/(a_1p)=0.7241$，$B\in\{3a_1,6a_1,10a_1\}$ 三档一致），$[3000,2\times10^4]$ 与抽稀至 $2\times10^5$ 在扫。注意 $\mu/p\le\operatorname{rad}(a_1)$ 为**假**（$a_1=375,\mu=399,p=3$：$133>15$），勿混用。

**$(CS)$ 的已知部分结果**（`17-fme-indep.md` §7，prover-mu，已复核）【已证明】：
- $|\operatorname{supp}(\mu)|\le1$ 时 $(CS)$ 成立；$\mu\le2a_1$ 时 $(CS)$ 成立；
- $H:\iff\forall p\mid\mu:\mu/p\ge a_1$ 与 $(CS)$ 不相容（故 $(CS)$ 的反例必满足 $\exists p:\mu/p>a_1$）；
- $|\operatorname{supp}(\mu)|=2$ 时 $(CS)$ 的反例必呈 $p<a_1<q$、$p\mid a_1$、$\mu=pq$ 的形状（用位置引理 + 私有指标 + $D_1\setminus S\ne\varnothing$ 导出 $a_{i_q}>2a_1$ 与 $a_{i_q}<p\le a_1$ 相撞）。
**【缺口】** 仅剩：$|\operatorname{supp}(\mu)|=2$ 的反例形状（$p<a_1<q$、$p\mid a_1$、$\mu=pq$）与 $|\operatorname{supp}(\mu)|\ge3$。

**$(CS)$ 失败的一般结构（`17` §8，prover-mu，已证明）**：失败点可取 $p_{\min}$；令 $P^\ast=\{r\mid\mu:\mu/r>a_1\}$（由单调性它是 $\operatorname{supp}(\mu)$ 的初始段），$Q^\ast=\operatorname{supp}(\mu)\setminus P^\ast$（$\mu/r=a_1$ 不可能）。则
- $\forall r\in P^\ast$ 位置引理可用，给 $T_r:=a_{i_r}r\in[a_1r,\ \mu/r)$、$\operatorname{supp}(T_r)\cap\operatorname{supp}(\mu)=\{r\}$、$T_r$ 为项；
- **主不等式** $\ a_1^{k}\bigl(\prod_{P^\ast}r\bigr)^{2}<\mu^{k}$（$k=|P^\ast|\ge1$），特例 $\mu>a_1(\min P^\ast)^2$；若 $P^\ast=S$（即 $H$）则 $a_1^{s}<\mu^{s-2}$，于是 $s=2$ 时 $a_1^2<1$ 矛盾 ⟹ **$(CS)$ 在 $s=2$ 且 $H$ 时成立**；
- 反例必有 $S\ne D_1$，且 $\forall r\notin D_1$ 有 $a_{i_r}\ge2r$（$A=D_1\setminus S\ne\varnothing$ 的 $\rho_r\mid a_{i_r}$）；
- 若 $\exists q\in Q^\ast\setminus D_1$ 且 $\mu>a_1^2$，则 $\mu>2q^2$、$q>\mu/a_1$，故 $\mu<a_1^2/2$，与主不等式相撞。
**最窄缺口**：$Q^\ast\ne\varnothing$ 时需要 $a_{i_q}\ (q\in Q^\ast)$ 的**非位置引理上界**（$\mu/q<a_1$ 使位置引理失效）；证 $a_{i_q}\le2q$ 或 $\le a_1$ 即与主不等式相撞。数值：$a_{i_r}r/\mu$ 实测最大 $742.5$，故无"$C\mu/r$"型上界（`logs/d17_kill.py`）。
**Lead 校准（$a_1\le400$，672 个 $(\mu,q)$ 对）**：上述两个候选上界**都太强**——$a_{i_q}\le a_1$ 有 208 例违反、$a_{i_q}\le2q$ 亦假（例：$a_1=15,\mu=6,q=2,a_{i_q}=20$），但 $a_{i_q}\le2a_1$ 在样本中成立（$\max a_{i_q}/a_1=4/3$）。故缺口应表述为"某个 $O(a_1)$ 型上界 + 与主不等式 $a_1^k(\prod_{P^\ast}r)^2<\mu^k$ 的配合"。

**$a_{i_r}\le2a_1$ 的横截集重述（`16` §17，已证明）**：$a_{i_r}\le2a_1$ $\iff$ 存在横截集 $T$ 使 $T\cap\operatorname{supp}(\mu/r)=\varnothing$ 且 $a_1\le\prod_{p\in T}p\le2a_1$（取 $W=\prod T$ 即为与 $\mu/r$ 互素的项）。
- $A':=(S\setminus\{r\})\cap D_1=\varnothing$ 时，$W=\operatorname{rad}(a_1)\lceil a_1/\operatorname{rad}(a_1)\rceil$ 满足 $\operatorname{supp}(W)=D_1$、$\gcd(W,\mu/r)=1$、$a_1\le W\le a_1+\operatorname{rad}(a_1)\le2a_1$ ⟹ **该分支已解决**。
- **$2\nmid t$ 时已解决**（`16` 26.3+26.4：$\ell=2$ 的 boost 给 $W<2a_1$）；失效形态 $\exists s:D_s\cap D_1\subseteq A'$ 且 $r\nmid a_s$ 的修复集 $T=T_0\cup\{\rho_s\}$ 必横截、不交 $\operatorname{supp}(t)$（26.2，已证明），boost 引理 26.3（$\prod_Tp\le a_1$、$\ell\notin\operatorname{supp}(t)$ ⟹ $W<a_1\ell$）。
- **【关键放宽，`16` §20】**：因 $r\mid a_{i_r}\Rightarrow r\le a_{i_r}$ 且 $\mu=rt<ra_1$，故**任何常数 $C$** 的 $a_{i_r}<Ca_1$ 都给 $\mu<Ca_1^2$ ⟹ $\mathcal M$ 有限 ⟹ FME ⟹ 原题。故目标放宽为"某个统一常数界 $a_{i_r}\le Ka_1$"。
- **【缺口（最窄）】**：仅剩"$W$ 落不进窗口"的组合——$3\mid t$ 且（$\prod_Tp\ge3a_1$，或所有可用素数对 $\ell_2>3\ell_1$）。三条充分条件 A/B/C 已证（28.1–28.3），数值上（978 例、$\max a_{i_r}/a_1=1.4483$）除此之外从未出现。
- **【进一步收窄，`17` §8.3】**：$(UB)$ 取任意 $C<4$ 时，$Q^\ast\ne\varnothing$ 支与 $H$ 支 $s\le3$ **全部解决**（$H$ 支用 $2^sa_1^s<\mu^{s-2}$ 与 $\mu<(Ca_1/2)^s$：$s=2$ 需 $C\ge2$、$s=3$ 需 $C<4$，与 $a_1$ 无关），故残余只剩 $H\wedge s\ge4$（$s=|\operatorname{supp}\mu|$）；另已证 $D_s\not\subseteq\operatorname{supp}(\mu/r)$，且失效项可替换为 $\rho_s\in D_s\setminus(D_1\cup\operatorname{supp}(t))$ 而保持互素（迭代**无条件有限终止**：最小失效下标严格递增，`17` §8.4）。
- **【$H\wedge s\ge4$ 的 Lead 观察（可即刻使用）】**：$H$ 下对**每个** $p\in S$ 都有 $\mu/p>a_1$，故 5.1′/16.4 的下降对**全部** $p\in S$ **同时**可用，给出 $\nu_p\in E_p$（$p\mid\nu_p$、$\operatorname{supp}(\nu_p)\cap S=\{p\}$、$\nu_p<\mu/p$，且可取 $\nu_p\le a_1p$）。于是这些 $\nu_p\in\mathcal M$ 两两相交而支撑交为空 ⟹ 交叉素数 $r_{pp'}\notin S$，且 $\prod_{p\in S}\nu_p<\mu^{s-1}$、$\prod_{p\in S}\nu_p\ge\mu\prod_{\{p,p'\}}r_{pp'}^2$（32.1/32.2 的同型下界），即 $\prod_{\{p,p'\}}r_{pp'}^2<\mu^{s-2}$。**这正是任务 26/25 需要的"多 $p$ 同步下降"版本**；障碍仍是 $X=\prod_Bp$ 的上界。
- **【$\mathrm H_{1/2}$ 粗糙路线，`16` §24，已证明】**：若 $\exists p\mid\mu:\mu/p\le a_1/2$，则 $\mu=p\cdot(\mu/p)\le a_1p/2$；再需 $p\le2a_1$（见下注）即得 $\mu\le a_1^2\le2a_1^2$ ⟹ 14 号定理 2.2（$N=2a_1^2$）⟹ 原题。$|S|=1$ 自动成立；反设 $\mathrm H_{1/2}$（$\forall p:\mu/p>a_1/2$）时结构与 $H$ 同构且**更干净**：$\mu/p\notin A_\infty$ **无条件**成立（$\mu$ 极小），$\forall p$：$D_{i_p}\cap S=\{p\}$、$p\mid a_{i_p}$、$\gcd(a_{i_p},\mu/p)=1$、交叉素数 $r_{pp'}\notin S$、$p\in B\Rightarrow a_{i_p}\ge2p$；$\mu/p\ge a_1$ 的 $p$ 上位置引理给 $a_{i_p}<\mu/p$，而 $\mathrm H_{1/2}\wedge\neg H$ 时必有 $\exists p:\mu/p\in(a_1/2,a_1)$。**残余＝排除 $\mathrm H_{1/2}$**（$|S|\ge2$）。
> 注（Lead 提醒）：33.1 里"$p\le2a_1$"的出处需写清——它正是素因子界（引理 5.4 的结论）的一半；若只由引理 5.2（$\min E_p\le a_1p$）得不出 $p\le2a_1$。稳妥表述：$\mu/p\le a_1/2$ 给 $\mu\le a_1p/2$，故只要有 $p\le4a_1$ 就够（弱于素因子界）。
- **【Lead 实验定位（$a_1\le1500$，1892 个 $\mu$）】**：$\max_{\mu}\min_{p\mid\mu}\frac{\mu}{p\,a_1}=0.5$（仅 $|S|=1$ 退化例 $a_1{=}2,\mu{=}2$）；**$|S|\ge2$ 时最大只有 $0.2$**（$a_1{=}15,\mu{=}15,S{=}\{3,5\}$），且 $H$ 实例数为 $\mathbf{0}$。即"$\exists p\mid\mu:\mu/p\le a_1/5$"在样本中成立 ⟹ $\neg H$ 余量 $\ge5$ 倍，**应可用粗糙论证直接证 $\neg H$**；配 (b)（$p\le a_1$）即得 $\mu\le a_1^2/5<2a_1^2$（`logs/lead_Hnear.py`）。
- **【$\mathrm H_{1/2}$ 路线的完整现状（`16` §24–§39，除注明外全【已证明】）】**：目标是最弱形式——若 $\exists p\mid\mu:\mu/p\le a_1/2$ 则 $\mu\le a_1p/2$（配 $p\le4a_1$ 即 $\le2a_1^2$）；反设 $\mathrm H_{1/2}$（$\forall p:\mu/p>a_1/2$）时：
  - $\mu/p\notin A_\infty$ **无条件**（$\mu$ 极小），故私有指标、$\rho'$-机制（$p\in B\Rightarrow a_{i_p}\ge2p$）、交叉素数 $r_{pp'}\notin S$ 全部可用；
  - $|S|\le2$ 已闭环（38.1/38.2：$p\mid a_1\wedge p>a_1/2\Rightarrow p=a_1$，故情形 B 为空、情形 A 给 $\mu<a_1^2$）；
  - $b=|B|\ge2$（39.1：$b=1$ 会迫使 $a_1<\Pi\mid\operatorname{rad}(a_1)\le a_1$），$|C|\le s-2$；$s=3$ 时 $C=\{c\}$、$B=\{p_1,p_2\}$、$c\mid a_1$、$c\le a_1/2$、$\min B>2a_1/c$、目标 $p_2\le2a_1^2/(cp_1)$；
  - 分区：$cp_1\le2a_1$ 闭环；$2a_1<cp_1\le a_1^{3/2}$ 闭环（40.1–40.2：$\exists c'\in D_1\setminus\{c\}$，$p_2c'\le a_{i_{p_2}}<cp_1$）；
  - 硬区 $cp_1>a_1^{3/2}$ 经 43.1/43.2/44.1–44.3/45.1–45.2/46.1–46.2 收成三支：(甲) $c=2\wedge m=0$、(乙) $|D_1|>\log_2a_1\wedge m>0$，及 (甲)$\wedge\mathcal Q$；**48.1 已闭环 (甲)$\wedge\mathcal P\wedge[cp_1\le a_1\sqrt{\operatorname{rad}(a_1)}]$**（用 $G=\operatorname{rad}(a_1)/2$ 与位置引理）；
  - 第一支（$cp_1>a_1\sqrt{\operatorname{rad}(a_1)}$）另由 $\mathrm H_{1/2}$ 的 $p_2>a_1/4$ 推出 $\operatorname{rad}(a_1)\le64$。
  **【缺口】** (甲)$\wedge\mathcal P\wedge(cp_1>a_1\sqrt{\operatorname{rad}(a_1)})$、(甲)$\wedge\mathcal Q$、(乙) 三支——皆带显式参数；数值上 $\mathrm H_{1/2}$ 在样本中从不出现（$\max\min_p\mu/(pa_1)=0.2$）。
- **【`16` §21/§22 + `17` §8.6 勘误】**：$H$ 的乘积界原本被 13 号引理 3.4 的写法（$\prod_{r\in S}T_r<\mu^{s-1}$）污染。`17` §8.6【已证明 + 勘误】给出正确原式
$$\prod_{r\in S}T_r=\mu\prod_{r\in S}a_{i_r}<\mu^{s}\ \Longrightarrow\ \text{(A) }a_1^s<\mu^{s-1},\quad\text{(B) }2^s<\mu^{s-2},\quad\text{(C) }(2a_1)^{s/2}<\mu^{s-1},$$
而 13 号的 "$2^sa_1^s<\mu^{s-2}$" 为**假**（反例 $a_1=100,S=\{2,101,103\},\mu=20806$ 满足 $H$ 但 $8\cdot10^6\not<\mu$）。配 $\mu<(Ca_1/2)^s$（此处必须用 $C$，$C\ge2$；换成 $\Pi$ 需额外 $\Pi\le Ca_1/2$）所得必要条件
$$(N\text{-}A)\ 2<Ca_1^{\frac{s-2}{s-1}},\qquad (N\text{-}B)\ 2^{\frac{s-1}{s-2}}<Ca_1,\qquad (N\text{-}C)\ 2^{\frac{s-1/2}{s-1}}<Ca_1^{\frac{s-3/2}{s-1}}$$
对 $s\ge4,C\ge2,a_1\ge3$ **自动成立** ⟹ **$H\wedge s\ge4$ 不被乘积界排除**，只排边界（如 (N-B) 排 $(s{=}3,C{=}2,a_1{=}2)$）。另有【已证明】乘性约束 $\Pi\prod_{B\setminus\{\max B\}}p>a_1$、$\max B<\mu/a_1$（30.2）与统一 boost 判据 $g\prod_Tp\le(C-1)a_1\Rightarrow a_{i_r}<Ca_1$（$g=2^{|\operatorname{supp}t|}$）。**$H\wedge s\ge4$ 需乘积界之外的新输入。**
数值：$|S|=2$ 的 $\mu$ 在 $a_1\le600$ 内共 133 例，**$\max\operatorname{supp}(\mu)/a_1=1/3$ 且无一例 $\max\operatorname{supp}(\mu)>a_1$**（余量 $\ge3$；`logs/d18_S2.py`）——故 $|S|=2$ 一侧应有较大余量。

**$|S|=2$ 形状上的刚性事实（`16` §15 + Lead 勘误，已证明）**：设 $\mu=pq\in\mathcal M$、$p<a_1<q$、$p\mid a_1$、$q\notin D_1$。则
1. $q\notin A_\infty$（否则 $q$ 是 $\mu$ 的真 $A_\infty$-因子）；
2. 一切 $<q$ 的项都被 $p$ 整除（若 $q\mid a_s$ 则 $a_s\ge q$）；特别**首个 $p$-可除项 $a_P=a_1$，故 $\tau_p=a_1/p$**；结合 21.1（$\tau_p\le\operatorname{rad}(a_1)$）与 23.2(ii) 得
$$\frac{a_1}{\operatorname{rad}(a_1)}\ \le\ p\ \le\ \operatorname{rad}(a_1)\qquad(\text{故反例只在 } a_1 \text{ 不光滑处});$$
3. $a_{u+1}\in(q,2q)$ 且 $p\mid a_{u+1}-a_u\le\operatorname{rad}(a_1)$，故 $p\le\operatorname{rad}(a_1)$（即上式右端）；
4. 首个 $q$-可除项 $a_Q$ 满足 $2q\le a_Q=qs\ (2\le s\le p)\le\mu=pq$（$q$ 不是项、$q<a_Q$）；另有 $\rho'$-机制给 $a_{i_q}\ge q\rho'\ ({\rho'\in D_1\setminus S})$ 与下降元 $\nu'\in E_p$、$q\nmid\nu'$、$\nu'\le a_u<q$。
5. **（`16` §16 引理 24.1，已证明）** $\nu'q\in A_\infty$；取其 $\mathcal M$-因子 $\nu''$，则 $q\mid\nu''$ 且 $\operatorname{supp}(\nu'')\cap S\in\{\{q\},\{p,q\}\}$。后一情形强制 $\nu''=\mu$（否则 $pq$ 是 $\nu''\in\mathcal M$ 的真 $A_\infty$-因子），于是 $p\le\nu'\le a_u<q$；前一情形给 $\nu''=qs$、$s<q$、$p\nmid s$、$\nu''<q^2$。
> 残余抓手：情形 "$\nu''=\mu$" 用 $p\le\nu'\le a_u<q$ 与 $a_u>q-\operatorname{rad}(a_1)$ 双侧夹逼；情形 "$\nu''=qs$" 用 $\nu''$ 与 $\rho'$-机制（$a_{i_q}\ge q\rho'$）相撞。
> 勘误：`16` §15 的 $a_r$ 曾在"首个 $p$-可除项"与"首个 $q$-可除项"间混用；上式已用 $a_P/a_Q$ 分开（$a_r\ge2q$ 只对 $a_Q$ 成立，$a_P\le a_1$）。

**$(CS)$ 已移植的下降结构（`16` §14，已证明）**：对 $(CS)$ 反例 $(\mu,p)$（$\mu/p>a_1$）令 $t:=\mu/p$，则 $t\notin A_\infty$ 且其一切 $\ge2$ 因子 $\notin A_\infty$；$\operatorname{supp}(\mu)=\operatorname{supp}(t)\sqcup\{p\}$ 横截；$t\in\mathcal R_p$；$i=\mathrm{kill}(t)$ 给 $D_i\cap S=\{p\}$、$p\mid a_i$、$\gcd(a_i,t)=1$、$a_i/p\in\mathcal R_p$，且 $t>a_1$ 时位置引理给 $a_i<t$；并且**存在严格下降** $\nu'\in\mathcal M$（$p\mid\nu'$、$\operatorname{supp}(\nu')\cap S=\{p\}$、$\nu'<\mu/p$），故
$$(CS)\iff\ \text{不存在 }(\star\star):\ \exists\mu\in\mathcal M,\exists p\mid\mu:\ a_1<\mu/p\le a_1p .$$
$(\star\star)$ 与 $R$ 一样在数值上从不触发（$a_1\le10^4$：$(CS)$ 零反例、$\max\mu/(a_1p)=0.724138$）。
> 数值提示（$a_1\le800$ 全扫，`logs/lead_pa1tight.py`）：$t\ge2$ 时若 $Q_p\ne\varnothing$ 则 $p/a_1\le0.2$；$Q_p=\varnothing$ 恰为 $p\mid a_1$（此时 $p\le a_1$ 已证）。故"硬情形"都形如 $a_1=pq$、$\sigma=pq=a_1$。
> 注（勘误）：`16` 的 18.3 中"$\nu_q\in E_q\Rightarrow\nu_q\le a_1q$"须说明——16.6 只给 $\min E_q\le a_1q$；正确做法是对 $\nu_q$ 继续沿 $q$ 下降（16.4）至 $\le a_1q$（下降保持 $\nu_q<\sigma/q$ 与 $p\nmid\nu_q$），结论不变。`16` §12 已改。

**归约**：只需处理 $p>a_1$（此时 $p\nmid a_1$、$Q_p\ne\varnothing$、$t\ge2$）；$Q_p=\varnothing$ 恰发生在 $p\mid a_1$，而那里 $p\le a_1$ 已由 16.16(a) 解决。

**命题 5.9（$\neg L$ 的结构）** 设 $\neg L$、$q\in Q_p$。则引理 5.1′（取 $\nu:=\sigma$）给出 $\nu_q\in\mathcal M$ 使 $q\mid\nu_q$、$p\nmid\nu_q$、$\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$、$\nu_q<\sigma/q=pt/q$；又 $\nu_q\in E_q$ 故 $\nu_q\le a_1q$。
进一步，沿"$\operatorname{rad}(p\mu)$ 的 $p$-含 $\mathcal M$-因子"下降得**二分**（`16` 引理 18.4 终止版）：或者落在**成功支** $\sigma\le p\nu_q$（此时 $t\le\nu_q$，且可对 $(q,Q_q)$ 递归），或者停在 **stall 构型** $\mu^\ast\in\mathcal M$、$p\nmid\mu^\ast$、$p\mu^\ast\in A_\infty$、$\mu^\ast\mid\nu_q$，且 $\operatorname{rad}(p\mu^\ast)$ 无 $p$-含 $\mathcal M$-因子。stall 真实存在（$a_1=187,p=3,\mu^\ast=22$）。
$(L)$ 于是归结为 stall 支的
$$p\,\mu^\ast\le a_1q .$$

【缺口】$(L)$（等价地：stall 支的 $p\mu^\ast\le a_1q$）。数值：$a_1\le2000$ 内 $Q_p\ne\varnothing$ 的 355 个 $(a_1,p)$ 全部满足 $(L)$，$\min_q a_1q/\sigma=5$（$a_1{=}35,p{=}7$），即余量约 5 倍；`logs/lead_qbound.py`、`logs/d17_Lcheck.py`（两套独立实现一致）。

## 6. FME 与实现引理

**定理 6.1（FME；在定义 5.3 的 $\neg R$ 下成立）** $\mathcal M$ 有限；更精确地，$\mathcal M\subseteq\{k\ge2:k\ \text{无平方因子},\ \operatorname{supp}(k)\subseteq\{p:p\le2a_1\}\}$，故
$$|\mathcal M|\le2^{\pi(2a_1)},\qquad \mu\le\prod_{p\le2a_1}p\ \ (\forall\mu\in\mathcal M).$$
证明：由引理 2.2 每个 $\mu$ 无平方因子、$\mu=\prod_{p\in\operatorname{supp}(\mu)}p$；由引理 5.4（假设 $\neg R$）每个素因子 $\le2a_1$。∎

> 注：**唯一**用到 $\neg R$ 的就是这里（经引理 5.4）；§6.2、§6.3、§7 的其余步骤无条件。

**引理 6.2（实现）** 对每个 $\mu\in\mathcal M$ 存在**项** $a_t$ 使 $D_t=\operatorname{supp}(\mu)$。

证明：取 $p\in\operatorname{supp}(\mu)$，令 $j:=\min\{s\ge1:\mu p^s\ge a_1\}$，$k:=\mu p^{j}$。则 $\operatorname{supp}(k)=\operatorname{supp}(\mu)$，$k\in A_\infty$（(M)），$k\ge a_1$，故由 (P5) $k=a_t$ 是项且 $D_t=\operatorname{supp}(k)=\operatorname{supp}(\mu)$。∎

**定理 6.3（TCL，备用路线）** 由定理 6.1 $\mathcal M$ 有限，故
$$N:=\max\{t(\mu):\mu\in\mathcal M\}<\infty,\qquad\text{且}\qquad \forall m>N\ \exists i\le N:\ D_i\subseteq D_m .$$
证明：$t(\mu)$ 由引理 6.2 给出（$\mathcal M$ 是 $A_\infty$ 的确定子集，无循环）。取 $m>N$：$a_m\in A_\infty\Rightarrow\operatorname{rad}(a_m)\in A_\infty$（(P2)），由引理 2.2 取极小元 $\mu\mid\operatorname{rad}(a_m)$，则 $\operatorname{supp}(\mu)\subseteq D_m$；由引理 6.2 取 $i:=t(\mu)\le N$，则 $D_i=\operatorname{supp}(\mu)\subseteq D_m$。∎

> **注（有效常数，prover-fme 的 R3 方案，完全严格）**：若要显式 $N$，令 $P:=\prod_{p\le2a_1}p$（由定理 6.1 每个 $\mu\mid P$）。对 $\mu\in\mathcal M$ 取 $j:=\min\{s\ge0:\mu p^s\ge a_1\}$、$k:=\mu p^{j}$：当 $j=0$ 时 $k=\mu\le P$，项指标 $t\le k-a_1+1\le P-1$；当 $j\ge1$ 时由 $j$ 的极小性 $\mu p^{j-1}<a_1$，故 $k<a_1p\le2a_1^2$，$t<2a_1^2$。于是 TCL 取 $N=\max\{2a_1^2,P\}$ 即可。（原 `10-tcl-proof.md` 的 $N=2a_1^2$ 在 $j=1,\mu\ge a_1$ 分支失效，反例 $a_1=15,\mu=15,p=3$：$k=45=a_1p$；见 `12-fme-proof.md` §4。）

## 7. 由 FME 推出原题

由引理 2.2 与 (M)：$A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$。由定理 6.1 取 $L:=\operatorname{lcm}\{\mu:\mu\in\mathcal M\}$（$\ge2$），则 $\mu\mid L\ (\forall\mu\in\mathcal M)$。于是对一切 $x\ge2$：
$$x\in A_\infty\iff x+L\in A_\infty. \tag{7.1}$$
（$\Rightarrow$：$\mu\mid x\Rightarrow\mu\mid x+L$。$\Leftarrow$：$x+L\ge2$ 属某 $\mu\mathbb Z$，故 $\mu\mid x+L$ 而 $\mu\mid L$，得 $\mu\mid x$，又 $x\ge2$。）

又 $L+1\notin A_\infty$：否则 $\mu\mid L+1$ 与 $\mu\mid L$ 给出 $\mu\mid1$，矛盾。

令 $g(k):=|A_\infty\cap(k,k+L]|\ (k\ge2)$。由 (7.1)（$k+1\ge3\ge2$）：
$$g(k+1)-g(k)=\bigl[k+L+1\in A_\infty\bigr]-\bigl[k+1\in A_\infty\bigr]=0,$$
故 $g$ 在 $k\ge2$ 上为常数；记 $T:=g(a_1)\ge1$（因 $a_1\in A_\infty$、(7.1) 给出 $a_1+L\in A_\infty\cap(a_1,a_1+L]$）。并且
$$T=g(2)=|A_\infty\cap(2,L+2]|=|A_\infty\cap(0,L]|,$$
最后一个等号：对称差 $[3,L+2]\triangle[2,L]\subseteq\{2,L+1,L+2\}$，其中 $[L+1\in A_\infty]=0$、$[L+2\in A_\infty]=[2\in A_\infty]$（(7.1)），而 $1\notin A_\infty$。故
$$|A_\infty\cap(k,k+L]|=T\qquad(\forall k\ge2). \tag{7.2}$$

取 $k=a_n\ (n\ge1$；$a_n\ge a_1\ge2)$。由 (7.2)，$A_\infty\cap(a_n,a_n+L]$ 恰有 $T$ 个元素，它们都 $>a_n\ge a_1$；由 (P5) 它们正是紧随 $a_n$ 的 $T$ 个项 $a_{n+1},\dots,a_{n+T}$。又 $a_n+L\in A_\infty$（(7.1)）是该区间右端点，故 $a_{n+T}=a_n+L$。∎

**定理（原题）** 在 $\neg R$（定义 5.3）下：存在正整数 $T,L$ 使 $\forall n\ge1:\ a_{n+T}=a_n+L$。$\blacksquare$

> 若把 $\neg R$ 换成 v2 的写法，本条应读作：“除残余命题 $R$ 外全部自足”。$R$ 的数值地位：$a_1\le10^4$ 内从未出现，且 $R$ 等价于“$\exists\mu\in\mathcal M:\mu>2a_1$ 且其某素因子 $>2a_1$”；由于所有已检验样本都有 $\mu\le1.45a_1$、$p\le a_1$，$R$ 属于**数值上无法触发**的惰性情形——这正是它此前被漏检的原因。

## 8. 交叉验证
- `10-tcl-proof.md`（prover-tcl）独立给出同一证明链（Lead 逐行复核）；同处第 73 行亦有 §5 的同一不等式瑕疵。
- `verify.py` / `20-verification.md`（verifier-num）独立精确整数程序：$a_1=15,385,2$ 等样本上 TCL/UCL/周期性/FME/dangerous-阶段一致性全部通过，影子命题反例符合预期。
- `11-alt-proof.md`（prover-alt）、`12-fme-proof.md`（prover-fme）为第二、第三条独立复核。
- **须知（评语第 81 行，成立）**：由于下降引理的前提（v2 的 $\nu>2a_1$、v3 的 $\nu>a_1p$ 之外的触发条件）在样本中从不满足，数值验证对 §5 本身**几乎零信息**；样本上的 FME 一致性由“$\mathcal M$ 元素很小”这一经验事实支撑。
- 独立扫描（Lead，`logs/claimB_scan.py`、`logs/cofactor_scan.py`、`logs/xpmin_scan.py`）：$a_1\le3000$ 无 $\mu>2a_1$；$a_1\le1200$ 无 (CS) 反例；$a_1\le300$ 与 `17-fme-indep.md` §4 的实现完全一致。

## 9. 附录：把 TCL 常数从 $\max\{2a_1^2,\prod_{p\le2a_1}p\}$ 改回 $2a_1^2$ 的努力（13–15 号文档）

**已完全证明的化归**（`14-H-gap.md` 定理 2.2，已复核）：若每个极小元 $\mu\in\mathcal M$ 满足 $\mu\le2a_1^2$，则 TCL 可取 $N=2a_1^2$（§6.2 的实现项 $t$ 可控制在 $2a_1^2$ 以内）。充分条件：$\mu\le2a_1$，或（更强）$\mu\le\operatorname{rad}(a_1)X\le a_1^2$，其中 $X:=\prod_{p\in\operatorname{supp}(\mu)\setminus D_1}p$。

**已证明的辅助结果**（`13-mu-bound.md`、`14-H-gap.md`、`15-x-final.md`，各自自足并互校；`14`/`15` 更正了 `13` 中两处记账）：
1. 强化下降引理：$\nu\in\mathcal M,\ p\mid\nu,\ \nu>a_1p\Rightarrow\exists\nu'\in\mathcal M:\ p\mid\nu',\ \operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\},\ \nu'<\nu/p$。
2. $D_1\subseteq\operatorname{supp}(\mu)\Rightarrow\operatorname{supp}(\mu)=D_1$；$|S\cap D_1^{c}|\le1$ 时 $\mu\le a_1^2/2$；$|S|=2$ 时 $\neg H$。
3. 记 $H:\iff\forall p\in S:\ \mu/p\ge a_1$：$H$ 下 $\forall p\in S$ 有 $a_{i_p}<\mu/p$、$D_{i_p}\cap S=\{p\}$，且 $p\in S\setminus D_1\Rightarrow a_{i_p}\ge2p$；并有 $X^{2-|S\setminus D_1|}\prod q_p\,(\prod_{A}p)^{|S\setminus D_1|}<\operatorname{rad}(a_1)^{|S\setminus D_1|}$。
4. 精确化（`15` 定理 2.4）：恒等式 $\dfrac{\mu}{a_1}=\dfrac{X}{\sigma\prod_{A}p}$（$\sigma=a_1/\operatorname{rad}(a_1)$，$A=D_1\setminus S$），$H\iff\mu>a_1\max S$；并给出若干**无条件**判据（如 $m:=\max S\in S\setminus D_1$ 且 $\prod_{p\in S\setminus(D_1\cup\{m\})}p\le\prod_{A}p\Rightarrow\neg H$），数值上覆盖 $|S\setminus D_1|\ge2$ 案例的 36/37。

**残余缺口（v3 口径：两条，互不相同）**
1. **主链残余 $R$**（定义 5.3；`16`、`17`、Lead 扫描三路独立收敛）：等价形式 $R\iff\neg$(素因子界)$\iff\exists p:E_p\ne\varnothing,p>2a_1\iff\exists p:E_p\ne\varnothing,\nu_p>2a_1$（引理 5.3′、5.3″）；$\neg R\Rightarrow$ 引理 5.4 $\Rightarrow$ FME $\Rightarrow$ 原题；$R$ 从未在 $a_1\le10^4$ 内出现。结构钳制与三条充分路线见 §5.7；其中 (b)（$E_p\ne\varnothing\Rightarrow p\le a_1$）数值零反例、且比 $R$ 强。
2. **常数残余 $H$**（本节 1–4 条）：全面证明 $\neg H$（等价形式见 `15-x-final.md` §2）。数值：$H$ 在 $a_1\le3000$（扫描界 $B=8a_1$）中从未出现，$\max\mu/(a_1\max\operatorname{supp}\mu)=0.5$，故 $N=2a_1^2$ 在所有被检验实例中成立；$\max\{2a_1^2,\prod_{p\le2a_1}p\}$ 始终无条件有效。注意：$H$ 是“$\forall p\mid\mu:\mu/p\ge a_1$”，与 $R$ 用的“$\mu/p$ 小”方向相反，二者**不是**同一问题（评语第 85 行这一点成立）。

**已证且与 $R$ 相关的无条件结论**（可复用）：引理 5.2（$\min E_p\le a_1p$）；每个 $\mu\in\mathcal M$ 的支撑与 $D_1$ 相交，故 $\mathcal M=\bigcup_{p\mid a_1}E_p$；$\min\mathcal M\le\operatorname{rad}(a_1)\le a_1$；强不变量 (CS) $\mu/p\le a_1$ 在 $a_1\le1200$ 内零反例（$a_1=375$ 处 $\mu/p\le\operatorname{rad}(a_1)$ 为假，勿混用）。

## 10. 升级到 v4 的接口（一旦某条充分命题落地）

若下列任一被证，则本文件升为 v4，改动是机械的：
- **(CS)**（$\forall\mu\forall p\mid\mu:\mu/p\le a_1$）被证：删去 §5.8 中 $(CS)$ 的【缺口】；§6.1 改为"由 $(CS)$ 得 $\mu\le a_1^2$，故 $\mathcal M\subseteq[2,a_1^2]$ 有限"；§6.3 的常数由 `13-mu-bound.md` §6 的化归（$\mu\le2a_1^2\Rightarrow N=2a_1^2$）取 $N=2a_1^2$；§7 不变。引理 5.2（$p\le2a_1$）可保留为条件命题。
- **$\neg R$**（$=$ 引理 5.4 的结论）被证：删去 §5.4–§5.6、§6.1、§7 中的 $\neg R$ 假设，全文无条件；引理 5.2 升级为 $\nu_p\le a_1p\le a_1^2$（`16` §12 已给出 $(b)+\nu_p\le2a_1$ 的接口）。
- 两处落定后都需 verifier-num 按 `21-verification-v3.md` 的口径再复核一次，并更新 §8、§9、`22-pause-state.md`。

## 11. 参考文献（本仓）
`00-problem.md`、`01-reduction.md`、`02-lead-notes.md`、`10-tcl-proof.md`、`11-alt-proof.md`、`12-fme-proof.md`、`13-mu-bound.md`、`14-H-gap.md`、`15-x-final.md`、`16-descent-fix.md`、`17-fme-indep.md`、`20-verification.md`、`21-verification-v3.md`、`23-verification-L.md`、`22-pause-state.md`、`verify.py`、`logs/`、外部评语 `D:\OneDrive\Desktop\30号证明评语.md`。
