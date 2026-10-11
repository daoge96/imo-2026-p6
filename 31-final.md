# IMO 第 6 题：定稿（自足清洁版）

> **结论（条件式／待闭合）**：设整数 $a_1>1$，序列由"$a_{n+1}:=>$ 所有 $a_i\ (i\le n)$ 有公因子的最小整数 $>a_n$"定义。**则存在正整数 $T,L$ 使 $\forall n\ge1:\ a_{n+T}=a_n+L$**——其中"FME"（$A_\infty$ 的极小元集 $\mathcal M$ 有限）已由本文 §1–§4 无条件化归，**唯一缺口是 §9 列出的残余（三条等价/充分命题之一）**。
>
> 本文件是自足定稿；更长的工作版（含全部勘误与中间尝试）为 `30-final-proof.md`，素材库为 `16-descent-fix.md`、`17-fme-indep.md`，对抗复核为 `23-verification-L.md`、`21-verification-v3.md`。
> 标签约定：**【已证明】** 无条件且经复核；**【缺口】** 尚未证明。

---

## §1 记号与基本事实

固定 $a_1\ge2$。记
$$\operatorname{supp}(k)=\{p\ \text{素}:p\mid k\},\quad D_n=\operatorname{supp}(a_n),$$
$$A_n=\{k\ge2:\operatorname{supp}(k)\cap D_i\ne\varnothing\ \ \forall i\le n\},\qquad A_\infty=\bigcap_{n\ge1}A_n,\qquad \mathrm{kill}(k)=\min\{i:\gcd(k,a_i)=1\}.$$
有限素数集 $S$ 叫 $\{D_1,\dots,D_n\}$ 的**横截集**，若 $S\cap D_i\ne\varnothing\ (\forall i\le n)$；于是 $k\in A_n\iff\operatorname{supp}(k)$ 横截。

**【已证明】(P1)–(P6)、(K)、(M)**
- (P1) $\operatorname{rad}(a_1\cdots a_n)$ 的倍数属 $A_n$，故 $a_{n+1}$ 存在；且 $a_{n+1}$ 与每个 $a_i\ (i\le n)$ 不互素 ⟹ $\gcd(a_i,a_j)>1\ (i\ne j)$ ⟹ **每个 $D_j$ 是全族的横截集**。
- (P2) 每个 $a_j\in A_\infty$；$k\in A_\infty\Rightarrow\operatorname{rad}(k)\in A_\infty$。
- (P3) $A_{n+1}\subseteq A_n$。
- (P4) $a_{n+1}=\min(A_n\cap(a_n,\infty))=\min(A_\infty\cap(a_n,\infty))$。
- (P5) 序列恰是 $A_\infty\cap[a_1,\infty)$ 的递增枚举。
- (P6) $\operatorname{rad}(a_1)\in A_\infty$，故 $a_{n+1}-a_n\le\operatorname{rad}(a_1)$。
- (K) $k\in A_N\iff\mathrm{kill}(k)>N$；$k\in A_\infty\iff\mathrm{kill}(k)=\infty$。
- (M) $A_\infty$ 对取倍数、对乘法封闭。

**定义**：$k$ 是**项** ⟺ $\exists t:k=a_t$；$\mu$ 是 $A_\infty$ 的**极小元** ⟺ $\mu\in A_\infty$ 且无真因子 $\nu\in A_\infty$；记 $\mathcal M$ 为全体极小元。

**【已证明】引理 1.1** 每个 $k\in A_\infty$ 被某极小元整除（故 $A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$），且每个 $\mu\in\mathcal M$ 无平方因子。

## §2 位置引理

**【已证明】引理 2.1** 设 $k\ge a_1$、$\mathrm{kill}(k)=i<\infty$，则 $a_i<k$。
证明：$k\in A_{i-1}\setminus A_i$ 故 $k\notin A_\infty$，结合 $k\ge a_1$ 与 (P5) 知 $k$ 不是项。令 $u:=\max\{t:a_t\le k\}$，则 $a_u<k<a_{u+1}$。若 $u\le i-1$ 则由 (P3) $k\in A_u$ 与 (P4) 得 $a_{u+1}\le k$，矛盾。故 $u\ge i$，$a_i\le a_u<k$。∎

## §3 私有指标引理

**【已证明】引理 3.1** $\mu\in\mathcal M$、$p\mid\mu$、$T:=\operatorname{supp}(\mu)$ ⟹ $\exists i:D_i\cap T=\{p\}$。
证明：$T$ 横截。若 $\mu=p$ 取 $i=1$。否则 $\mu/p$ 是 $\mu$ 的真因子且 $\ge2$，故 $\mu/p\notin A_\infty$，取 $i:=\mathrm{kill}(\mu/p)$，则 $D_i\cap(T\setminus\{p\})=\varnothing$ 而 $D_i\cap T\ne\varnothing$。∎

## §4 下降引理（修正版）与 $E_p$ 的界

**【已证明】引理 4.1（下降）** $\nu\in\mathcal M$、$p\mid\nu$、$\nu>a_1p$ ⟹ $\exists\nu'\in\mathcal M$：$p\mid\nu'$、$\operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\}$、$\nu'<\nu/p$。
证明：$\nu>a_1\ge a_1$ 是项；$k:=\nu/p>a_1$，$k\notin A_\infty$；$i:=\mathrm{kill}(k)$，引理 2.1 给 $a_i<k$，故 $D_i\cap\operatorname{supp}(\nu)=\{p\}$。取 $\nu'$ 为 $\{\nu''\mid\operatorname{rad}(a_i),\nu''\in A_\infty\}$ 的极小者，则 $\nu'\in\mathcal M$、$\operatorname{supp}(\nu')\subseteq D_i$，与 $T$ 横截相撞得 $\operatorname{supp}(\nu')\cap T=\{p\}$，且 $\nu'\le a_i<\nu/p$。∎
（**关键**：v2 曾用 $\nu/p\ge\nu/2>a_1$，该式只对 $p=2$ 成立；此处改假设为 $\nu>a_1p$。）

**【已证明】引理 4.2** $E_p:=\{\mu\in\mathcal M:p\mid\mu\}\ne\varnothing$ ⟹ $\nu_p:=\min E_p\le a_1p$。
证明：若 $\nu_p>a_1p$，引理 4.1 给 $\nu'<\nu_p/p<\nu_p$ 且 $p\mid\nu'$，与极小性矛盾。∎

## §5 残余命题 $R$ 及其等价形式

**定义 5.1（$R$）** $\exists$ 素 $p,\exists\mu\in\mathcal M$：$p\mid\mu$、$p>2a_1$、$2a_1<\mu\le a_1p$。

**【已证明】引理 5.2** $R\iff\exists p:E_p\ne\varnothing\wedge p>2a_1\iff\exists p:E_p\ne\varnothing\wedge\nu_p>2a_1$。
**【已证明】引理 5.3** $R\iff\neg\bigl(\forall\mu\forall p\mid\mu:p\le2a_1\bigr)$，即 $R$ **恰是**"素因子界"的取反。
**【已证明】引理 5.4** $\neg R$ ⟹ $\forall\mu\in\mathcal M,\forall p\mid\mu:p\le2a_1$。
证明：对 $\nu_0:=\nu_p$ 迭代引理 4.1 得严格递减 $p$-链，停在 $\nu_k\le a_1p$；若 $\nu_k>2a_1$ 且 $p>2a_1$ 则 $R$ 成立，故 $\neg R$ 时 $p\le2a_1$。∎

## §6 FME 与由 FME 推出原题（在 $\neg R$ 下）

**【已证明，用引理 5.4】定理 6.1（FME）** $\mathcal M\subseteq\{\mu:\mu$ 无平方因子，$\operatorname{supp}(\mu)\subseteq\{p\le2a_1\}\}$，故 $|\mathcal M|$ 有限且 $\mu\le\prod_{p\le2a_1}p$。

**【已证明】引理 6.2（实现）** 每个 $\mu\in\mathcal M$ 有项 $a_t$ 使 $D_t=\operatorname{supp}(\mu)$（取 $k=\mu p^j\ge a_1$ 最小者即可）。

**【已证明】定理 6.3（TCL，备用有效常数）** $\mathcal M$ 有限 ⟹ $N:=\max_\mu t(\mu)<\infty$ 且 $\forall m>N\exists i\le N:D_i\subseteq D_m$（$N=\max\{2a_1^2,\prod_{p\le2a_1}p\}$ 可取）。

**【已证明】定理 6.4（由 FME 得原题）** 取 $L:=\operatorname{lcm}\{\mu\in\mathcal M\}$，则 $x\in A_\infty\iff x+L\in A_\infty\ (x\ge2)$，$L+1\notin A_\infty$；令 $g(k)=|A_\infty\cap(k,k+L]|$ 得 $g\equiv T$。取 $k=a_n$：区间 $(a_n,a_n+L]$ 的 $T$ 个 $A_\infty$ 元素由 (P5) 正是 $a_{n+1},\dots,a_{n+T}$，而右端点 $a_n+L\in A_\infty$ ⟹ $a_{n+T}=a_n+L$。∎

## §7 三条充分路线（任一成立即闭环）

**【已证明】** $(CS)\Rightarrow$FME$\Rightarrow$原题；$(b'')\Rightarrow(L)\Rightarrow(b)\Rightarrow\neg R$；$(b'')\Rightarrow(c)\Rightarrow\neg R$。其中
$$(CS):\forall\mu\forall p\mid\mu:\tfrac{\mu}{p}\le a_1;\qquad (b):\forall p(E_p\ne\varnothing\Rightarrow p\le a_1);\qquad (b''):\forall p(E_p\ne\varnothing\Rightarrow\nu_p\le2a_1);$$
$$(L):\exists q\mid t\ (t:=\nu_p/p,\ q\ \text{素},\ q\mid a_1):\ \nu_p\le a_1q;\qquad (c):\forall p(E_p\ne\varnothing\Rightarrow a_r\le2a_1).$$
- $(CS)\Rightarrow$FME：$\mu\le a_1\min\operatorname{supp}(\mu)\le a_1\max D_1\le a_1^2$，故 $\mathcal M\subseteq[2,a_1^2]$。
- $(L)\Rightarrow(b)$：$\sigma:=\nu_p=pt$，$p=\sigma/t\le a_1q/t\le a_1$。
- $(b'')\Rightarrow(L)$（任取 $q\ge2$）、$(b'')\Rightarrow(c)$ 直接。
- **任何常数 $C$** 的"$a_{i_r}<Ca_1$"都给 $\mu<Ca_1^2$（因 $r\mid a_{i_r}\Rightarrow r\le a_{i_r}$、$\mu=rt<ra_1$）。

## §8 残余的刚性结构（全部【已证明】，供 §9 使用）

设 $R$ 成立，$\sigma:=\nu_p=pt$（$p>2a_1$）：
1. $2\le t<a_1$，$t\notin A_\infty$ 且 $t$ 的每个 $\ge2$ 因子都 $\notin A_\infty$；
2. $\exists q\mid t,\ q\mid a_1$（故 $Q_p:=\{q\mid t,q\mid a_1\}\ne\varnothing$）；$p\nmid a_1$；$Q_p=\varnothing\Rightarrow p\mid a_1$；
3. 每个项被 $p$ 或 $t$ 的某素因子整除；$i:=\mathrm{kill}(t)$ 给 $D_i\cap\operatorname{supp}(\sigma)=\{p\}$、$p\mid a_i$、$\gcd(a_i,t)=1$、$a_i\ge\sigma$；
4. 由 (P1) 有 $\operatorname{rad}(a_1)\in\mathcal R_p$，故 $\tau_p\le\min(t,\operatorname{rad}(a_1))\le a_1$；
5. $R$ 情形下 $\nu_p/p\le a_1$（位置引理必然失效），stall 二分把 $(L)$ 归结为 stall 支 $p\mu^\ast\le a_1q$；
6. **连同 $\neg L$ 结构**：对每个 $q\in Q_p$ 得 $\nu_q\in E_q$，$p\nmid\nu_q$，$\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$，$\nu_q<\sigma/q$；$\mathcal M$-链成功支给 $\sigma\le p\nu_q$，失败支即 stall（真实存在：$a_1=187,p=3,\mu^\ast=22$）。

## §9 唯一缺口（三条窄支，任一支打通即全文闭环）

**取代 $R$ 的最弱目标**（`16` §24–§40）：记 $\mathrm H_{1/2}:\iff\forall p\mid\mu:\mu/p>a_1/2$。则
- 若 $\neg\mathrm H_{1/2}$（$\exists p:\mu/p\le a_1/2$），则 $\mu\le a_1p/2$；只需 $p\le4a_1$ 即 $\mu\le2a_1^2$ ⟹ 定理 6.3/6.4（$N=2a_1^2$）；
- 若 $\mathrm H_{1/2}$：已证 $\mu/p\notin A_\infty$ 无条件、$|S|\le2$ 全部闭环、$b=|B|\ge2$、$|C|\le s-2$；$s=3$ 时 $C=\{c\}$、$B=\{p_1,p_2\}$、$c\mid a_1$、$c\le a_1/2$、目标 $p_2\le2a_1^2/(cp_1)$；分区 $cp_1\le2a_1$、$2a_1<cp_1\le a_1^{3/2}$、$(\text{甲})\wedge\mathcal P\wedge[cp_1\le a_1\sqrt{\operatorname{rad}(a_1)}]$ **均已闭环**。

**【缺口】仅剩三支**：
1. $(\text{甲})\wedge\mathcal P\wedge\bigl[cp_1>a_1\sqrt{\operatorname{rad}(a_1)}\bigr]$，其中 (甲) $:c=2\wedge m=0$；已推出 $\operatorname{rad}(a_1)\le64$、$p_2\in(a_1/4,2a_1/\sqrt{\operatorname{rad}(a_1)})$、$p_2\operatorname{rad}(a_1)/2\le a_{i_{p_2}}<2p_1$；**纯算术非空，需顺序结构**；
2. $(\text{甲})\wedge\mathcal Q$（$cp_2<a_1$：$a_1/4<p_2<a_1/2$，两个位置引理皆失效）；
3. $(\text{乙})$ $|D_1|>\log_2a_1\wedge m>0$（可用 46.1 的显式常数 $4$：$\mu-a_{i_{p_2}}\le4\big/(\tfrac1{\operatorname{rad}(a_1)}-\Sigma)$）。

其中 $B:=S\setminus D_1$、$b:=|B|$、$C:=S\cap D_1$、$m:=$ 使 $c'\nmid a_{i_{p_2}}$ 的 $c'\in D_1\setminus\{c\}$ 的个数、$\mathcal P:cp_2\ge a_1$、$\mathcal Q:cp_2<a_1$、$G:=\prod\{c'\in D_1\setminus\{c\}:c'\mid a_{i_{p_2}}\}$（$m=0$ 时 $G=\operatorname{rad}(a_1)/c$）。
另有三条**并列**的旧缺口（与上面等价或互不包含）：$R$／stall 支（§8.5–8.6）、$H\wedge s\ge4$、$T$-窗口 $g\prod_Tp>(C-1)a_1$。

## §10 数值证据（三套独立实现互表；全部零反例）

| 量 | 值（范围） |
|---|---|
| $R$ 实例／$\mu>2a_1$ | $0$（$a_1\le10^4$，$B\in\{3,6,10\}a_1$ 三档稳定） |
| $\max\mu/(2a_1)$ | $0.724138$（$a_1{=}899,\mu{=}1302$） |
| $\max p/a_1$ | $1$（唯一 $a_1{=}p{=}2$） |
| $(CS)$ 反例 | $0$（$a_1\le3000$） |
| $\mathrm H_{1/2}$、$H$ 实例 | $0$；$\max\min_p\mu/(pa_1)=0.2$（$|S|\ge2$） |
| $a_{i_r}/a_1$（$r\in Q^\ast$） | $\max 1.4483$；$a_{i_r}\le2a_1$ 零反例 |
| $(L)$ 余量 $\min a_1q/\sigma$ | $5.0$（$a_1\le400$）→ $2.96$（$a_1\le3000$） |

脚本：`logs/claimB_scan.py`、`cofactor_scan.py`、`lead_qbound.py`、`d17_ub.py`、`d18_S2.py`、`lead_Hnear*.py`、`leadH12*.py`。

## §11 复核、索引与升级接口

- 对抗复核：`23-verification-L.md`（对 `16` §10–§16、`17` §6–§8 逐条重推：14 项通过、零反驳；两处历史错误 18.3、16.15 已修）；`21-verification-v3.md`（对 §5）。
- 素材：`16-descent-fix.md`（§1–§40）、`17-fme-indep.md`（§1–§8.6）、`14-H-gap.md`、`13-mu-bound.md`、`15-x-final.md`、`10-tcl-proof.md`。
- **升级到 v4（闭环后机械改动）**：$(CS)$ 被证 ⟹ §6.1 改为由 $\mu\le a_1^2$ 得有限性、$N=2a_1^2$；$\neg R$ 被证 ⟹ 删去 §6 全部假设、引理 4.2 升级为 $\nu_p\le a_1^2$；随后按 `23-verification-L.md` 口径复核一次。
