# FME 独立复证 + 对 `10-tcl-proof.md` 的对抗性复核

**作者**：prover-fme（task-4）。**依赖**：`00-problem.md`、`01-reduction.md`（记号 (P1)–(P8)、(K)）、`02-lead-notes.md`（归约）。
**结论**：FME 成立且可完整证明（本文 §2 给出独立自足的证明），FME ⟹ 原题（§2.6）。对 `10-tcl-proof.md` 的逐条复核见 §3；**发现一处局部缺口**（引理 5.2 的一个不等式的退化分支，§4），该缺口**不影响 FME，也不影响原题**，只影响该文 TCL 的显式常数 $N=2a_1^2$。
**与 `10-tcl-proof.md` 的关系：独立复证 + 发现差异**。差异仅一处（§4），且给出三种修复方案（其中 R3 完全严格）；其余全部独立确认为正确。

> 标注约定：**【已证明】** = 本文给出完整证明；**【已核对】** = 数值/逻辑复核通过；**【缺口】** = 论证不成立处。

---

## 1. 记号与引用的事实（引自 01，已在 01 证明）

固定 $a_1\ge 2$。$\operatorname{supp}(k)=\{p\ \text{素}:p\mid k\}$，$D_n=\operatorname{supp}(a_n)$，$T:=\operatorname{supp}(\mu)$ 等。
$$A_n=\{k\ge2:\ \operatorname{supp}(k)\cap D_i\ne\varnothing\ \ \forall i\le n\},\qquad A_\infty=\bigcap_{n\ge1}A_n,\qquad \mathrm{kill}(k)=\min\{i\ge1:\gcd(k,a_i)=1\}\ (\text{无则 }\infty).$$
有限素集 $S$ 称**横截集**，若 $S\cap D_i\ne\varnothing\ (\forall i\ge1)$；于是 $k\in A_\infty\iff \operatorname{supp}(k)$ 横截（【已证明】，定义直接展开）。

本文引用（均为 01 已证）：
- **(P1)** $\gcd(a_i,a_j)>1\ (i\ne j)$；每个 $D_j$ 是族 $\{D_i\}_{i\ge1}$ 的横截集。
- **(P2)** 每个 $a_j\in A_\infty$ 且 $\operatorname{rad}(a_j)\in A_\infty$。
- **(P3)** $A_\infty\subseteq A_n\subseteq A_m$（$m\le n$）。
- **(P4)(P5)** $a_{n+1}=\min(A_n\cap(a_n,\infty))=\min(A_\infty\cap(a_n,\infty))$；$(a_n)$ 是 $A_\infty\cap[a_1,\infty)$ 的严格递增枚举。
- **(P6)** $a_{n+1}-a_n\le \operatorname{rad}(a_1)$。
- **(P8)** 序列无穷、良定义。
- **(K)** $k\in A_N\iff \mathrm{kill}(k)>N$；$k\in A_\infty\iff\mathrm{kill}(k)=\infty$。
- **(M)** $A_\infty$ 对取倍数封闭；$\operatorname{rad}(a_1)\in A_\infty$；$A_\infty\subseteq\{k\ge2\}$。

**定义 1.1** $\mu\ge2$ 叫 $A_\infty$ 的**极小元**，若 $\mu\in A_\infty$ 且无真因子 $\nu$（$2\le\nu<\mu$）满足 $\nu\in A_\infty$。记 $\mathcal M$ 为极小元之集。**FME**：$\mathcal M$ 有限。

---

## 2. FME 的独立证明【全部已证明】

### 2.1 极小元覆盖引理

**引理 2.1** 每个 $k\in A_\infty$ 有 $\mu\in\mathcal M$，$\mu\mid k$。
**证明** 对 $k$ 强归纳。$k\in A_\infty$。若 $k$ 极小取 $\mu=k$。否则存在真因子 $\nu\mid k$，$2\le\nu<k$，$\nu\in A_\infty$（极小性之否定），由归纳假设得 $\mu\mid\nu\mid k$。∎
于是 $A_\infty=\bigcup_{\mu\in\mathcal M}\mu\,\mathbb Z_{\ge2}$（$\supseteq$ 由 (M)，$\subseteq$ 由本引理）。

### 2.2 位置引理（被杀者必在凶手之后）

**引理 2.2** 若 $k\ge a_1$ 且 $\mathrm{kill}(k)=i<\infty$，则 $a_i<k$。
**证明** 由 (K)：$k\in A_{i-1}$，$k\notin A_i$。
1. $k\notin A_\infty$（因 $A_\infty\subseteq A_i$）。由 (P5)，$A_\infty\cap[a_1,\infty)$ 恰是项集，而 $k\ge a_1$，故 $k$ **不是项**；特别 $k\ne a_1$。
2. 令 $u:=\max\{t\ge1:a_t\le k\}$（存在：$a_1\le k$ 且 $a_t\to\infty$，见 (P8)）。$a_u\ne k$ 故 $a_u<k$。
3. 又 $k$ 不是项，而 $a_{u+1}$ 是 $>a_u$ 的最小项，故 $k<a_{u+1}$。
4. 若 $u\le i-1$：由 (P3) $A_{i-1}\subseteq A_u$，故 $k\in A_u$；结合 $k>a_u$ 与 (P4) $a_{u+1}=\min(A_u\cap(a_u,\infty))$ 得 $a_{u+1}\le k$，与 3. 矛盾。
5. 故 $u\ge i$，于是 $a_i\le a_u<k$。∎

### 2.3 私有素数（见证）

**引理 2.3** 设 $\mu\in\mathcal M$，$p\in \operatorname{supp}(\mu)=:T$。则 $\exists i\ge1$：$D_i\cap T=\{p\}$。
**证明** $\mu\in A_\infty$ ⇒ $T$ 是横截集。
- 若 $\mu=p$：$T=\{p\}$，横截性给出 $p\in D_i\ (\forall i)$，取 $i=1$ 得 $D_1\cap T=\{p\}$。
- 若 $\mu>p$：则 $\mu/p\ge2$ 且 $\mu/p\mid\mu$，由极小性 $\mu/p\notin A_\infty$，故 $i:=\mathrm{kill}(\mu/p)<\infty$。于是 $\gcd(\mu/p,a_i)=1$，即 $\operatorname{supp}(\mu/p)\cap D_i=\varnothing$；而 $\operatorname{supp}(\mu/p)=T\setminus\{p\}$，故 $D_i\cap T\subseteq\{p\}$。又 $T$ 横截 ⇒ $D_i\cap T\ne\varnothing$，故 $=\{p\}$。∎

### 2.4 下降步骤

**引理 2.4** 设 $\nu\in\mathcal M$，$\nu>2a_1$，$p\in\operatorname{supp}(\nu)$。则 $\exists\nu'\in\mathcal M$ 使 $p\in\operatorname{supp}(\nu')$ 且 $\nu'<\nu/p$。
**证明** 记 $T:=\operatorname{supp}(\nu)$。
1. $\nu>2a_1\ge a_1$，由 (P5) $\nu=a_j$ 是项；故 $T=D_j$ 是族 $\{D_i\}$ 的成员。
2. $\nu/p\ge2$：否则 $\nu=p$；此时 $T=\{p\}$ 横截 ⇒ $p\mid a_i\ (\forall i)$ ⇒ $p\mid a_1$ ⇒ $p\le a_1<2a_1<\nu=p$，矛盾。
3. $\nu/p\ge\nu/2>a_1$ 且 $\nu/p\notin A_\infty$（极小性），故 $\mu:=\nu/p$ 满足 $\mathrm{kill}(\mu)=:i<\infty$。
4. 引理 2.2（$k:=\mu>a_1\ge a_1$）给出 $a_i<\mu$。
5. $\gcd(\mu,a_i)=1$ ⇒ $\operatorname{supp}(\mu)\cap D_i=\varnothing$ ⇒ $D_i\cap T\subseteq\{p\}$（因 $\operatorname{supp}(\mu)=T\setminus\{p\}$）；又 $T$ 横截 ⇒ $D_i\cap T\ne\varnothing$，故 $D_i\cap T=\{p\}$。
6. $a_i<\mu<\nu=a_j$ 且项严格递增 ⇒ $i<j$。
7. 由 (P2) $\operatorname{rad}(a_i)\in A_\infty$ 且 $\ge2$。令 $\mathcal F:=\{\nu''\ge2:\nu''\mid\operatorname{rad}(a_i),\ \nu''\in A_\infty\}\ne\varnothing$（含 $\operatorname{rad}(a_i)$），取其中在整除偏序下的极小者 $\nu'$。则 $\nu'\in\mathcal M$：若 $\nu''\mid\nu'$、$\nu''\in A_\infty$、$2\le\nu''<\nu'$，则 $\nu''\mid\operatorname{rad}(a_i)$ 故 $\nu''\in\mathcal F$，与取法矛盾。
8. $\operatorname{supp}(\nu')\subseteq D_i$，故 $\operatorname{supp}(\nu')\cap T\subseteq D_i\cap T=\{p\}$；又 $\nu'\in A_\infty$ ⇒ $\operatorname{supp}(\nu')$ 横截，而 $T=D_j$ 是族成员 ⇒ $\operatorname{supp}(\nu')\cap T\ne\varnothing$；故 $=\{p\}$，特别 $p\in\operatorname{supp}(\nu')$。
9. $\nu'\mid\operatorname{rad}(a_i)$ ⇒ $\nu'\le\operatorname{rad}(a_i)\le a_i<\nu/p$。∎

### 2.5 关键引理与 FME

**引理 2.5** 设 $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$。则 $p\le2a_1$。
**证明** 若 $\mu\le2a_1$，则 $p\le\mu\le2a_1$。否则 $\mu>2a_1$，用引理 2.4 迭代：$\nu_0:=\mu$，只要 $\nu_r>2a_1$ 就取 $\nu_{r+1}:=(\text{引理 2.4 对}(\nu_r,p)\text{给的}\nu')$。归纳地：$p\in\operatorname{supp}(\nu_r)$ 对一切 $r$ 成立（$r=0$ 为假设，传递由引理 2.4 的结论），且 $\nu_{r+1}<\nu_r/p\le\nu_r/2$。故 $(\nu_r)$ 是严格递减正整数列，有限步 $k$ 停机；停机即 $\nu_k\le2a_1$（否则可再走一步）。于是 $p\le\nu_k\le2a_1$。∎

**定理 2.6（FME）** $\mathcal M$ 有限。精确地：
$$\mathcal M\ \subseteq\ \bigl\{k\ge2\ \text{无平方因子}:\ p\mid k\Rightarrow p\le2a_1\bigr\},\qquad \#\mathcal M\le2^{\pi(2a_1)} .$$
**证明** 设 $\mu\in\mathcal M$。
1. $\mu$ 无平方因子：若 $p^2\mid\mu$，则 $\operatorname{rad}(\mu)\mid\mu$、$\operatorname{rad}(\mu)<\mu$、$\operatorname{rad}(\mu)\ge2$，且 $\operatorname{supp}(\operatorname{rad}(\mu))=\operatorname{supp}(\mu)$ 横截 ⇒ $\operatorname{rad}(\mu)\in A_\infty$，与极小性矛盾。
2. 由引理 2.5，$\mu$ 的每个素因子 $\le2a_1$；结合 1. 得 $\mu=\prod_{p\in\operatorname{supp}(\mu)}p$。
3. 映射 $\mu\mapsto\operatorname{supp}(\mu)$ 是 $\mathcal M$ 到 $\{$素数的 $\le2a_1$ 子集$\}$ 的单射，后者共 $2^{\pi(2a_1)}$ 个。∎

### 2.6 FME ⟹ 原题（周期化）

由引理 2.1 与 (M)：$A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$。

1. $L:=\operatorname{lcm}\{\mu:\mu\in\mathcal M\}\ (\ge2)$；由定理 2.6 该 lcm 有限。于是 $\mu\mid L\ (\forall\mu\in\mathcal M)$，故对一切 $x\ge2$：
$$x\in A_\infty\iff x+L\in A_\infty. \tag{2.1}$$
（$\Rightarrow$：$\mu\mid x$ ⇒ $\mu\mid x+L$ ⇒ $x+L\in\mu\mathbb Z_{\ge2}\subseteq A_\infty$。$\Leftarrow$：$x+L\in A_\infty$ ⇒ $\exists\mu:\mu\mid x+L$；$\mu\mid L$ ⇒ $\mu\mid x$，又 $x\ge2$ ⇒ $x\in A_\infty$。）
2. $L+1\notin A_\infty$：否则 $\exists\mu:\mu\mid L+1$ 而 $\mu\mid L$，得 $\mu\mid1$，矛盾。又 $1\notin A_\infty$（(M)）。
3. 令 $g(k):=|A_\infty\cap(k,k+L]|$。对 $k\ge2$：$k+1\ge3>2$，由 (2.1)（施于 $x=k+1$）
$$g(k+1)-g(k)=[k+L+1\in A_\infty]-[k+1\in A_\infty]=0,$$
故 $g$ 在 $\{2,3,\dots\}$ 上恒为常数 $T:=g(2)$。
4. $T=g(2)=|A_\infty\cap(2,L+2]|$。而 $\{2,L+1,L+2\}$ 覆盖两个区间的对称差：由 (2.1) $[L+2\in A_\infty]=[2\in A_\infty]$、由 2. $[L+1\in A_\infty]=0$、$[1\in A_\infty]=0$，故
$$T=|A_\infty\cap(0,L]|\ \ge1$$
（$\ge1$ 的三重理由：$g$ 为常值故 $T=g(2)=g(a_1)=|A_\infty\cap(a_1,a_1+L]|$；而 $a_1\in A_\infty$（(P2)）由 (2.1) 给出 $a_1+L\in A_\infty$，故该区间非空；亦可用 $\min\mathcal M\le L$ 与 $\min\mathcal M\in A_\infty$。）于是
$$|A_\infty\cap(k,k+L]|=T\qquad(\forall k\ge2). \tag{2.2}$$
5. 取 $k=a_n\ (\ge a_1\ge2)$。由 (2.2)，$A_\infty\cap(a_n,a_n+L]$ 恰有 $T$ 个元素；它们全 $>a_n\ge a_1$，由 (P5) 恰为紧随其后的 $T$ 个项 $a_{n+1},\dots,a_{n+T}$。而 $a_n+L\in A_\infty$（(2.1) 与 $a_n\in A_\infty$）落在该区间内且是区间右端点，故是其中最大元，即 $a_{n+T}=a_n+L$（$\forall n\ge1$）。∎

**注 2.7** 本路线只用 (P1)(P2)(P5)(P8)、(K)、(M)、引理 2.1–2.5、定理 2.6，**不用** Main Lemma / TCL / G2，与 Lead 在 02 中的归约完全一致。

---

## 3. 对 `10-tcl-proof.md` 的逐条对抗性复核

> 本节及 §4 中的引理/定理编号（如"引理 2.1""定理 5.1""引理 5.2"）除特别注明外**均指 `10-tcl-proof.md` 的编号**；本文自身的编号形式为"§2 的引理 2.1–2.5 / 定理 2.6"。

记号：该文引理 2.1 / 3.1 / 4.1 / 4.2 / 5.2 / §6。

| # | 位置 | 复核内容 | 判定 |
|---|---|---|---|
| 1 | 引理 1.3 | 强归纳，$\mu\mid\nu\mid k$ | ✅【已核对】 |
| 2 | 引理 2.1 步骤 1 | $k\notin A_\infty$ 且 $k\ge a_1$ ⇒ $k$ 不是项（(P5)） | ✅ |
| 3 | 引理 2.1 步骤 2–3 | $u:=\max\{t:a_t\le k\}$ 存在；$a_u<k<a_{u+1}$ | ✅（$a_t\to\infty$ 由 (P8)） |
| 4 | 引理 2.1 步骤 4 | 若 $u\le i-1$ 则 $A_{i-1}\subseteq A_u$、$k\in A_u$，与 (P4) 及 $k<a_{u+1}$ 矛盾 ⇒ $u\ge i$ | ✅（$i=1$ 时 $u\ge1=i$ 自动成立，无需 $A_0$） |
| 5 | 引理 3.1 | $T$ 横截；$\mu=p$ 单列；否则 $i=\mathrm{kill}(\mu/p)$ 给出 $D_i\cap T=\{p\}$ | ✅ |
| 6 | 引理 4.1 步骤 1 | $\nu>2a_1\ge a_1$ ⇒ $\nu=a_j$ 是项，$T=D_j$ 是族成员 | ✅ |
| 7 | 引理 4.1 步骤 2 | $\nu/p\ge2$ 的退化分支（$\nu=p$ ⇒ $p\mid a_1\Rightarrow p\le a_1<2a_1<\nu$）矛盾 | ✅ |
| 8 | 引理 4.1 步骤 3–5 | $\mu=\nu/p>a_1$；引理 2.1 给 $a_i<\nu/p$；$D_i\cap T=\{p\}$ | ✅ |
| 9 | 引理 4.1 步骤 6–8 | $i<j$；$\mathcal F$ 非空；$\nu'$ 在 $\mathcal F$ 内极小 ⇒ $\nu'\in\mathcal M$；$p\in\operatorname{supp}(\nu')$ | ✅（$\nu'\in\mathcal M$ 的论证完整：任何更小 $A_\infty$-因子仍属 $\mathcal F$） |
| 10 | 引理 4.1 步骤 9 | $\nu'\le\operatorname{rad}(a_i)\le a_i<\nu/p$ | ✅ |
| 11 | 引理 4.2 | 迭代终止性（$\nu_{r+1}<\nu_r/2$）与 $p\le2a_1$ | ✅【已核对】终止无隐含假设，$p$ 沿链保持 |
| 12 | 定理 5.1 | $\mu$ 无平方因子；素因子 $\le2a_1$；$\#\mathcal M\le2^{\pi(2a_1)}$ | ✅ |
| 13 | 引理 5.2 | $k$ 是项且 $D_t=\operatorname{supp}(\mu)$ 的**存在性** | ✅ |
| 14 | 引理 5.2 | 不等式 $k=\mu p^{e-1}\cdot p<a_1p$ 与结论 $t<2a_1^2$ | ⚠️ **【缺口】**，见 §4 |
| 15 | 定理 5.3 | TCL 的最终陈述（存在 $N$） | ✅（结论正确；该文的**显式** $N=2a_1^2$ 未由 14 建立，但可用 §4.3 R3 严格修复为 $N=\max\{2a_1^2,\prod_{p\le2a_1}p\}$，或用 R1 补 $\mu\le2a_1$ 后恢复原文常数） |
| 16 | §6 (6.1) | $x\in A_\infty\iff x+L\in A_\infty$（$x\ge2$） | ✅ 双向严格核对 |
| 17 | §6 | $L+1\notin A_\infty$、$1\notin A_\infty$ | ✅（否则 $\mu\mid L,L+1\Rightarrow\mu\mid1$） |
| 18 | §6 $g$ 常值 | $g(k+1)-g(k)=[k+L+1\in A_\infty]-[k+1\in A_\infty]=0$（用 (6.1) 于 $x=k+1\ge3$） | ✅ |
| 19 | §6 $T=g(2)$、(6.2) | $T=|A_\infty\cap(0,L]|$：对称差 $\subseteq\{1,2,L+1,L+2\}$，用 (6.1) 消去 $2\leftrightarrow L+2$、$L+1,1\notin A_\infty$ | ✅ |
| 20 | §6 末步 | $A_\infty\cap(a_n,a_n+L]$ 恰 $T$ 个元素 ⇒ 恰为 $a_{n+1},\dots,a_{n+T}$；$a_n+L$ 是该区间右端点 ⇒ $a_{n+T}=a_n+L$ | ✅（$T\ge1$ 由 $\operatorname{rad}(a_1)\in A_\infty$） |

**结论：除第 14 项外，其余 19 项独立确认无误。** 第 14 项是唯一差异，且不触及 FME（定理 5.1）与 §6 路线 A。

---

## 4. 【缺口】引理 5.2 的退化分支（含反例与三种修复）

### 4.1 缺口内容

该文引理 5.2：取 $p\in\operatorname{supp}(\mu)$，$e:=\min\{e\ge1:\mu p^e\ge a_1\}$，$k:=\mu p^e$，断言
$$k=\mu p^{e-1}\cdot p\ \overset{?}{<}\ a_1p .$$
该不等式等价于 $\mu p^{e-1}<a_1$。当 $e\ge2$ 时由 $e$ 的极小性成立；但当 $e=1$ 时它要求 $\mu<a_1$，而 $e=1$ **并不**推出 $\mu<a_1$：只要 $\mu p\ge a_1$ 就有 $e=1$。故当
$$\mu\ \ge\ a_1$$
时 $e=1$、$k=\mu p$、$\mu p^{e-1}=\mu\ge a_1$，不等式不成立。

**具体反例**（$a_1=15$，$\mathcal M=\{6,10,15\}$，取 $\mu=15\in\mathcal M,\ p=3$）：$e=1$，$k=45$，而 $a_1p=45$，故 $k<a_1p$ **不成立**（取等号）。取 $\mu=15,p=5$ 亦同。

**数值统计**（本文脚本 `logs/audit_tcl.py`）：在 $a_1\in[2,129]\cup\{150,187,210,385,1001,2310,3003,15015\}$ 中共 **76** 个 $a_1$ 出现该不等式失效。而在这些样本中**结论** $t<2a_1^2$ 仍然成立（在 $k$ 落在已构造序列区间内的样本上 $\max t/(2a_1^2)=0.25$；$k$ 超出区间时由 $t\le k-a_1+1$ 亦不违例）。因此这是**论证缺口**，不是命题反例。经验上 $\mu\le 2a_1$ 且更精确地 $\mu\le\tfrac12 a_1\operatorname{rad}(a_1)$（样本最大比值 $0.5$），与该文 §7 表所记 $\mu\le a_1+\operatorname{rad}(a_1)\le2a_1$ 一致，但该文**未证** $\mu$ 本身的界。

### 4.2 影响范围

- **不影响 FME（定理 5.1）**：定理 5.1 只用到引理 4.2（素因子上界），不使用引理 5.2。
- **不影响原题**：§6 路线 A 只用 FME；结论 $a_{n+T}=a_n+L$ 的推导已逐条核对通过。
- **影响**：TCL 的显式常数 $N=2a_1^2$（定理 5.3 的陈述）与其"$t<2a_1^2$"这一断言。TCL 的**存在性**在修复方案 R2 下依然成立，故路线 B 的结论也成立。

### 4.3 修复方案（R3 完全严格；R1 可恢复原文常数；R2 不需常数）

先用一个**只用 10 文已证引理**的引理，把"实现"步骤改造好。记 $P:=\prod_{p\le2a_1}p$（由定理 5.1，$\mu\mid P$）。

**引理 4.4（实现，带显式指数）** 设 $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)$，$e:=\min\{e\ge0:\mu p^e\ge a_1\}$，$k:=\mu p^e$。则 $k\in A_\infty$、$\operatorname{supp}(k)=\operatorname{supp}(\mu)$、$k\ge a_1$，故 $k=a_t$ 是项且 $D_t=\operatorname{supp}(\mu)$，并且 $t<\max\{2a_1^2,\ P\}$。
**证明** $k$ 是 $\mu$ 的倍数 ⇒ $k\in A_\infty$（(M)）；$p\mid\mu$ ⇒ $\operatorname{supp}(k)=\operatorname{supp}(\mu)$；$k\ge a_1$ 由 $e$ 的定义；故由 (P5) $k=a_t$，$D_t=\operatorname{supp}(k)=\operatorname{supp}(\mu)$。
- 若 $e=0$：$\mu\ge a_1$ 且 $\mu=\prod_{q\mid\mu}q\le P$；项严格递增（(P4)：$a_{n+1}>a_n$，故 $a_t\ge a_1+t-1$）给 $t\le k-a_1+1\le P$。
- 若 $e\ge1$：由 $e$ 的极小性 $\mu p^{e-1}<a_1$，故 $k=\mu p^{e-1}\cdot p<a_1p\le2a_1^2$（引理 2.5），于是 $t\le k-a_1+1<2a_1^2$。∎

**R3（显式且完全严格，推荐）**：取 $N:=\max\{2a_1^2,\ P\}$（$P=\prod_{p\le2a_1}p$）。设 $m>N$。由 (P2) $\operatorname{rad}(a_m)\in A_\infty$，由引理 2.1 存在 $\mu\in\mathcal M$ 使 $\mu\mid\operatorname{rad}(a_m)$。由引理 4.4 取项 $a_{t}$ 使 $D_t=\operatorname{supp}(\mu)$ 且 $t<N$；而 $\operatorname{supp}(\mu)\subseteq\operatorname{supp}(\operatorname{rad}(a_m))=D_m$，故 $D_t\subseteq D_m$，且 $t\le N<m$。**TCL 成立。**∎
（于是 01 §4 的 TCL$\Rightarrow$UCL$\Rightarrow$Main Lemma$\Rightarrow$原题照样走通；只是常数由 $2a_1^2$ 变为 $\max\{2a_1^2,P\}$。）

**R1（补一条引理即可恢复原文常数 $N=2a_1^2$）**：只需证 $\mu\le2a_1\ (\forall\mu\in\mathcal M)$。此时在引理 4.4 中：$e\ge1$ 分支已有 $t<2a_1^2$；$e=0$ 分支 $\mu\ge a_1$ 且 $\mu\le2a_1$ 给 $t\le\mu-a_1+1\le2a_1<2a_1^2$。故 R1 成立 ⇒ 定理 5.3 原文陈述成立。**唯一待补：$\mu\le2a_1$**（样本最大 $\mu/(2a_1)=0.637$；更精确地样本最大 $\mu/(a_1\operatorname{rad}(a_1))=0.5$，与 10 文 §7 表一致，但该文未证）。★建议后续工作★

**R2（连常数也不要）**：$\mathcal M$ 有限（定理 5.1）且每个 $\mu$ 被某个项实现（引理 4.4，或仅用存在性），故 $N:=\max_{\mu\in\mathcal M}t(\mu)$ 有限（无循环：$\mathcal M$ 由 $A_\infty$ 确定）。对 $m>N$ 同上得 $D_{t(\mu)}\subseteq D_m$，$t(\mu)\le N<m$，TCL 成立。∎

---

## 5. 数值证据（精确整数运算；脚本在 `logs/`，仅用于定位）

1. **反链/极小元算法正确性**：用增量规则（$A_{n+1}$ 的极小元 = 幸存者 ∪ 被杀者的孩子 $b\cdot p$ 极小化）计算 $A_n$ 极小元，并在 $n=10,50,200$ 处与 **Berge 极小横截集暴力**逐项比对，全部一致（`logs/fme_exp2.py` 的 mismatch 检查为 `None`）。
2. **$\mathcal M$（持久极小元）复现** Lead 数据：$a_1=15\to\{6,10,15\}$；$35\to\{10,15,35,42\}$；$187\to\{22,102,187,231,238\}$；$385\to\{14,30,66,231,385,399,418\}$；$15015\to\{6,10,14,22,26,15015\}$；$210/2310/30030\to\{2\}$。
3. **引理 2.2 数值核对**：对 $a_1\in[2,129]$ 与上述样本，枚举 $k\in[a_1,\min(4000,40a_1+200)]$ 并计算 $\mathrm{kill}(k)=:i$，验证 $a_i<k$：**无违例**。
4. **引理 2.5 / 定理 2.6 数值核对**：所有算得的 $\mu\in\mathcal M$ 的素因子 $\le2a_1$：**无违例**；且样本最大 $\mu/(2a_1)=0.6364$（$a_1=187,\mu=238$），最大 $\mu/(a_1\operatorname{rad}(a_1))=0.5$——支持 §4.3 R1 的待证引理 $\mu\le2a_1$。
5. **§2.6 数值核对**（脚本 `logs/audit_period.py`，独立于 fme_exp2 实现）：由 $\mathcal M$ 构造 $L=\operatorname{lcm}\mathcal M$、$T=|A_\infty\cap(0,L]|$，核对 (i) $A_\infty$ 的 $L$-周期性；(ii) $L+1\notin A_\infty$；(iii) $a_{n+T}=a_n+L$ 对序列全部 $n$ 成立。$a_1\in\{2,3,15,35,187,385,1001,15015,15016\}$ **全部通过**，具体 $(T,L)$：$a_1{=}2\to(1,2)$、$a_1{=}15\to(8,30)$、$a_1{=}35\to(34,210)$、$a_1{=}187\to(484,7854)$、$a_1{=}385\to(5088,43890)$、$a_1{=}15015\to(9256,30030)$。其中 $(8,30),(34,210)$ 与 01 §5 独立记录一致；$a_1{=}15016=2^3\cdot1877$（含大素因子 $1877$）给 $\mathcal M=\{2\}$、$(T,L)=(1,2)$。
6. **缺口统计**：见 §4.1（76 个 $a_1$ 触发失效的不等式；结论仍成立）。

---

## 6. 缺口与自查清单

1. **已证明（无缺口）**：引理 2.1–2.5、定理 2.6（FME）、§2.6（FME ⟹ 原题）；§3 表中第 1–13、15–20 项。
2. **缺口（唯一，且已可修）**：`10-tcl-proof.md` 引理 5.2 的不等式 $k<a_1p$ 在 $\mu\ge a_1$ 时不成立（反例：$a_1=15,\mu=15,p=3,k=45=a_1p$），故该文 $t<2a_1^2$ 与 $N=2a_1^2$ 未经证明。修复：**R3（完全严格、显式）** 给出 TCL 与 $N=\max\{2a_1^2,\prod_{p\le2a_1}p\}$；**R1** 只需补证 $\mu\le2a_1$ 即可恢复原文常数。该缺口不影响 FME、不影响 §6 路线 A，也不影响原题的成立。
3. **对 $a_1\ge2$ 无隐藏假设**：证明中只出现 $a_1$ 与 (P1)(P2)(P3)(P4)(P5)(P8)(K)(M)；退化情形（$\mu$ 为素数、$\nu=p$、$a_1=2$、$\mu\le2a_1$）均单列。
4. **自查方式**：(i) 每个引理核对是否用到未证前提（引理 2.4 只用 (P2)(P5) 与引理 2.2/2.3 的思想；引理 2.5 的迭代保持假设 $p\in\operatorname{supp}(\nu_r)$ 并给出严格递减）；(ii) 用 Berge 暴力独立复核极小元集合；(iii) §2.6 逐式核对（含 $\{1,2,L+1,L+2\}$ 对称差与 $L+1\notin A_\infty$），并用独立实现的脚本 `logs/audit_period.py` 重跑 $L,T$ 与 $a_{n+T}=a_n+L$。
5. **未做**：$\mu\le2a_1$ 的证明（§4.3 R1）；Main Lemma / G2 的独立复核（本文不需要）；$\mathcal M$ 的具体结构刻画。
