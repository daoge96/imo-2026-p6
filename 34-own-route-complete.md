# 自创路线的完整化：$A_\infty$-极小元有限（FME）⟹ 原题

> **本文目的**：把本项目**自己搭出来的那条路线**补成一条完整、无条件的证明。它此前只差一件事——一个"上界机制"（我们全套工具只出下界）。补进的唯一外部想法是 **LP**：*含大素数（$>a_1^2$）的项必有更早的项，其支撑含于它*（用几何级数 $q^kc$ 一步证出）。LP 在 IMO 2026/6 的标准解法中出现，本文按我们的语言重证并明确标注；其余（$A_\infty$、极小元、FME、TCL、由 FME 得周期性的 gcd/格论证、全部引理）皆为本项目自创。
>
> **状态**：完整、无条件、已逐行自核；LP 与由此得的 FME 界另做了数值核验（`logs/verify34.py`，零违例）。
> 对照：`33-complete-proof.md` 是纯标准路线（$\prec$-偏序 + $F$/剩余类收尾）。

---

## §0 归属总表（诚实版）

| 内容 | 归属 |
|---|---|
| $A_\infty$、$\mathcal M$、FME、TCL、$\operatorname{kill}$、横截集语言、(P1)–(P6)/(K)/(M)、引理 1.1 | **自创** |
| 位置引理、私有指标引理、下降引理（修正版）、$\min E_p\le a_1p$、$\tau_p\le\min(t,\operatorname{rad}a_1)$ | **自创** |
| 引理 2.1（极小元 $\leftrightarrow$ 极小横截集）、引理 4.1（归约）、§5（FME $\Rightarrow$ 周期性） | **自创** |
| **引理 3.1（LP）**：大素数项有更早的支撑包含项（几何级数 $q^kc$） | **查来**（Evan Chen《IMO 2026 Solution Notes》§2.3；AoPS friendly-sets 解法同源） |
| 残余命题 $R$、$(L)$、$(CS)$、stall、$\mathrm H_{1/2}$、交叉素数计数 | **自创**（本文不再需要，见 §7） |

## §1 记号与基本事实（自创，已复核）

固定 $a_1\ge2$，序列按题设定义。$\operatorname{supp}(k)=\{p\ \text{素}:p\mid k\}$，$D_n=\operatorname{supp}(a_n)$，
$$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \forall i\le n\},\quad A_\infty=\bigcap_n A_n,\quad \operatorname{kill}(k)=\min\{i:\gcd(k,a_i)=1\}.$$
有限素数集 $S$ 叫**横截集**，若 $S\cap D_i\ne\varnothing\ (\forall i\ge1)$；于是 $k\in A_\infty\iff\operatorname{supp}(k)$ 横截。$\mu\ge2$ 是 $A_\infty$ 的**极小元**，若 $\mu\in A_\infty$ 且无真因子 $\nu\mid\mu$、$\nu\ge2$ 属 $A_\infty$；记 $\mathcal M$ 为全体极小元。

**【已证】事实 (P1)–(P6)、(K)、(M)**（证明见 `30-final-proof.md` §2）
- (P1) $a_{n+1}$ 存在；项两两不互素；每个 $D_j$ 是全族横截集。
- (P2) 每个 $a_j\in A_\infty$；$k\in A_\infty\Rightarrow\operatorname{rad}(k)\in A_\infty$。
- (P3) $A_{n+1}\subseteq A_n$。
- (P4) $a_{n+1}=\min(A_\infty\cap(a_n,\infty))$。
- (P5) **序列恰是 $A_\infty\cap[a_1,\infty)$ 的递增枚举**；特别地 $x\ge a_1$ 是项 $\iff x\in A_\infty$。
- (P6) $\operatorname{rad}(a_1)\in A_\infty$，故项距 $\le\operatorname{rad}(a_1)$。
- (K) $k\in A_N\iff\operatorname{kill}(k)>N$；$k\in A_\infty\iff\operatorname{kill}(k)=\infty$。
- (M) $A_\infty$ 对取倍数、对乘法封闭。

**【已证】引理 1.1** 每个 $k\in A_\infty$ 都被某极小元整除（故 $A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$）；每个 $\mu\in\mathcal M$ 无平方因子。（`30` 引理 2.2）

## §2 桥梁：极小元 $\leftrightarrow$ 极小横截集（自创）

**【已证】引理 2.1** 对 $\mu\ge2$：
$$\mu\in\mathcal M\iff \operatorname{supp}(\mu)\ \text{是}\ \subseteq\text{-极小横截集（横截，且不含真子横截集）}.$$
证明：$(\Rightarrow)$ $\mu\in A_\infty$ ⟹ 每个 $D_i$ 与 $\operatorname{supp}(\mu)$ 相交 ⟹ 横截。若 $T\subsetneq\operatorname{supp}(\mu)$ 也横截，取 $k=\prod_{p\in T}p$：$\operatorname{supp}(k)=T$ 横截 ⟹ $k\in A_\infty$；又 $\mu$ 无平方因子（引理 1.1）且 $T\subseteq\operatorname{supp}(\mu)$ ⟹ $k\mid\mu$、$k<\mu$，与极小性矛盾。
$(\Leftarrow)$ 支撑横截 ⟹ $\mu\in A_\infty$。若 $\nu\mid\mu$、$2\le\nu<\mu$、$\nu\in A_\infty$：则 $\operatorname{supp}(\nu)\subseteq\operatorname{supp}(\mu)$ 横截；若包含严格，与极小性矛盾；若不严格，则由引理 1.1 两者均无平方因子，$\nu=\operatorname{rad}\nu=\operatorname{rad}\mu=\mu$，亦矛盾。故 $\mu\in\mathcal M$。∎

**推论 2.2** 若 $\mu\in\mathcal M$，且 $T\subseteq\operatorname{supp}(\mu)$ 是横截集，则 $T=\operatorname{supp}(\mu)$。

## §3 补强引理 LP（外部灵感，本文重证）

**引理 3.1（LP）** 若项 $a_t$ 含素因子 $p>a_1^2$，则存在 $j<t$ 使 $\operatorname{supp}(a_j)\subseteq\operatorname{supp}(a_t)$。

证明：对 $t$ 作强归纳。写 $a_t=pc$，取素数 $q\mid\gcd(a_1,a_t)$（由 (P1) 项两两不互素存在）。令
$$K:=\min\{k\ge1:q^kc\ge a_1\},\qquad x:=q^Kc .$$
由 $K$ 的最小性 $q^{K-1}c<a_1$，故
$$a_1\ \le\ x=q\cdot q^{K-1}c\ <\ q\,a_1\ \le\ a_1^2\ <\ a_t\qquad(\text{末步用 }q\le a_1,\ a_t\ge p>a_1^2). \tag{3.1}$$

**约定（relevant）** 称项 $a_i$ 是 **relevant** 的，若不存在 $j<i$ 使 $\operatorname{supp}(a_j)\subseteq\operatorname{supp}(a_i)$（即"没有更早的项，其支撑含于它"）。这是**下标型**条件，便于归纳。

**断言 A**：若 $a_m\ (m<t)$ 是 relevant 且 $p\mid a_m$，则矛盾（故 relevant 项 $a_m$ 满足 $p\nmid a_m$）。
证：由归纳假设（$p>a_1^2$ 大、$a_m$ 含 $p$、$m<t$）存在 $j<m$ 使 $D_j\subseteq D_m$，与 $a_m$ relevant 矛盾。∎

**断言 B**：对每个 relevant 的 $a_m\ (m<t)$，有 $\gcd(x,a_m)>1$。
证：由断言 A，$p\nmid a_m$。由 (P1) 取素数 $r\mid\gcd(a_t,a_m)>1$；由 $p\nmid a_m$ 得 $r\ne p$，而 $a_t=pc$，故 $r\mid c$，于是 $r\mid q^Kc=x$。∎

**断言 C**：$x$ 是项。
证：由 (P5) 只需 $x\in A_\infty$；据引理 4.1（见 §4），只需对每个 relevant 的 $a_m$ 且 $a_m<x$ 验证 $\gcd(x,a_m)>1$。由 $a_m<x$ 与 (3.1) 得 $m<t$（序列递增、$x<a_t$），故断言 B 适用。∎

由断言 C，$x=a_j$ 且 $j<t$（因 $x<a_t$）。又 $\operatorname{supp}(x)=\operatorname{supp}(q)\cup\operatorname{supp}(c)\subseteq\operatorname{supp}(a_t)$（$q\mid a_t$、$c\mid a_t$），故 $a_j$ 即为所求。∎

## §4 归约引理（自创）

**引理 4.1** 设 $x\ge a_1$。则 $x$ 是项 $\iff$ 对每个 relevant 的 $a_m$ 且 $a_m<x$，有 $\gcd(x,a_m)>1$。

证明：$(\Rightarrow)$ $x=a_i$ 是项，$a_m<x$ ⟹ $m<i$ ⟹ 由 (P1) 项两两不互素得 $\gcd>1$。
$(\Leftarrow)$ 先证 $\gcd(x,a_i)>1$ 对一切 $a_i<x$ 成立：对 $i$ 强归纳。若 $a_i$ relevant，用假设；否则按定义 $\exists j<i$ 使 $D_j\subseteq D_i$，此时 $a_j<a_i<x$，由归纳假设 $\gcd(x,a_j)>1$ 且 $\operatorname{supp}(a_j)\subseteq D_i$，故 $\gcd(x,a_i)>1$。
于是 $x$ 与所有更早的项有公因子；若 $x$ 不是项，取 $n$ 使 $a_n<x<a_{n+1}$，由 (P4) 得 $a_{n+1}\le x$，矛盾。故 $x$ 是项。∎

## §5 由 LP 得 FME，再由 FME 得原题（收尾全为自创）

**命题 5.1（FME，带显式界）** 记 $P:=\{p\ \text{素}:p\le a_1^2\}$。则
$$\forall\mu\in\mathcal M:\ \operatorname{supp}(\mu)\subseteq P,\qquad \mu\ \Big|\ \prod_{p\in P}p,\qquad |\mathcal M|\le 2^{|P|},\qquad \mu\le\prod_{p\in P}p .$$
证明：设 $\mu\in\mathcal M$。若 $\mu$ 无大素因子，则 $\operatorname{supp}(\mu)\subseteq P$。否则 $\mu\ge p>a_1^2>a_1$，故 $\mu$ 是项（(P5)），取 $t:=\text{该下标}$。由引理 3.1 迭代：只要 $a_{t_i}$ 含大素因子，就取 $t_{i+1}<t_i$ 使 $\operatorname{supp}(a_{t_{i+1}})\subseteq\operatorname{supp}(a_{t_i})$。下标严格下降，终止于 $t^\ast$，其 $a_{t^\ast}$ 无大素因子，且 $\operatorname{supp}(a_{t^\ast})\subseteq\operatorname{supp}(\mu)$。$\operatorname{supp}(a_{t^\ast})$ 横截，由推论 2.2 得 $\operatorname{supp}(a_{t^\ast})=\operatorname{supp}(\mu)$，故 $\operatorname{supp}(\mu)\subseteq P$。其余三条随之。∎

**定理 5.2（FME $\Rightarrow$ 原题）** 由命题 5.1，$\mathcal M$ 有限。取 $L:=\operatorname{lcm}\{\mu:\mu\in\mathcal M\}$（$\ge2$，且 $L\mid\prod_{p\in P}p$）。由引理 1.1，$A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$，故对一切 $x\ge2$：$x\in A_\infty\iff x+L\in A_\infty$；又 $L+1\notin A_\infty$。令 $g(k):=|A_\infty\cap(k,k+L]|\ (k\ge2)$，则由上式 $g(k+1)-g(k)=0$，故 $g\equiv T:=g(a_1)\ (\ge1$，因 $a_1,a_1+L\in A_\infty)$。取 $k=a_n$：$(a_n,a_n+L]$ 内恰有 $T$ 个 $A_\infty$ 元素，由 (P5) 正是 $a_{n+1},\dots,a_{n+T}$；而右端点 $a_n+L\in A_\infty$，故 $a_{n+T}=a_n+L$。$\blacksquare$

**附（TCL，备用形式）** 命题 5.1 亦给显式 $N$：对 $\mu\in\mathcal M$ 取 $j=\min\{s:\mu p^s\ge a_1\}$、$k=\mu p^j$，则 $k$ 是项、$D_k=\operatorname{supp}(\mu)$、$k<\max\bigl(\prod_{p\in P}p,\ a_1p\bigr)$；故 $N:=\max\{2a_1^2,\prod_{p\le a_1^2}p\}$ 满足 $\forall m>N\ \exists i\le N:D_i\subseteq D_m$。

## §6 数值核验（针对本文新引理）

`logs/verify34.py`（窗口 $B=3000$，$a_1\in\{2,3,4,6,12,15,30,35,45,99,121,175,187,899\}$）逐步生成真序列后核验：
- **(LP)** 含 $>a_1^2$ 素因子的项必有更早项的支撑含于其支撑 —— **零违例**；
- **(FME\*)** 窗口内每个 $A_\infty$-极小元支撑只含 $\le a_1^2$ 的素因子 —— **零违例**。

## §7 与早期残余链的关系、可继续做的事

- 早期路线把目标收窄为 $R$／$(L)$／$(CS)$／$\mathrm H_{1/2}$（`31-final.md`、`16`、`17`），唯一缺口是"$O(a_1)$ 型上界"。LP 提供 $\operatorname{supp}(\mu)\subseteq\{p\le a_1^2\}$ 正是该上界，**残余链因此作废（不必再打）**。
- 可继续：(1) 把界 $a_1^2$ 改善为 $a_1$（即 $(b)$；数值上 $\max p/a_1=1$，唯一 $a_1=p=2$）；(2) 用我们的 $\nu_p\le a_1p$（引理 4.2 于 `30`）与 LP 夹逼同一方向；(3) 端到端数值检验（$a_1\le10^4$）。

## §8 参考

- Evan Chen,《IMO 2026 Solution Notes》§2.3（LP 来源）：`https://web.evanchen.cc/exams/IMO-2026-notes.pdf`
- IMO 2026 官方试题 Problem 6（供题 Taiwan）：`https://www.imo-official.org/problems/2026`
- 本项目：`30-final-proof.md`（工作版）、`31-final.md`（旧路线自足稿）、`33-complete-proof.md`（标准路线完整稿）、`23-verification-L.md`（对抗复核）、`logs/verify34.py`（本文新引理核验）。
