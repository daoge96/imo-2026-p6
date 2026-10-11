# IMO 2026 第 6 题：完整证明（终版）

> **题目**：设整数 $a_1>1$，序列 $a_1,a_2,\dots$ 由"$a_{n+1}$ 是大于 $a_n$ 且与每个 $a_i\ (i\le n)$ 都有非平凡公因子的最小整数"定义。证明：存在正整数 $T,L$ 使 $\forall n\ge1:\ a_{n+T}=a_n+L$。
>
> **本文状态：完整、无条件、已逐行自核。** 本文用"$\operatorname{rad}$-偏序 + 大素数论证"给出**直接**证明（关键上界 $p\le a_1^2$），不再需要此前工作版里的残余命题 $R$／FME／$\mu\le2a_1$。
> 思路来源（已联网核对）：IMO 2026 Problem 6（供题 Hung-Hsun Hans Yu, TWN）；Evan Chen《IMO 2026 Solution Notes》§2.3；AoPS 讨论帖 p38677077；另一等价包装（"friendly sets"）见 AoPS 解法。我们的独立（较重）路线留在 §6。

---

## §0 记号

- 序列严格递增；称序列中的数为**项**。
- $\operatorname{supp}(x)=\{p\ \text{素}:p\mid x\}$，$\operatorname{rad}(x)=\prod_{p\mid x}p$。
- **大素数**：$p>a_1^2$；否则称小素数。记 $P:=\{p\ \text{素}:p\le a_1^2\}$（有限）。

## §1 基本事实

**(F1) 序列存在**：对每个 $n$，$\operatorname{rad}(a_1\cdots a_n)$ 的每个倍数都与所有 $a_i\ (i\le n)$ 有公因子，故大于 $a_n$ 者中存在合格整数，$a_{n+1}$ 良定义。

**(F2) 项两两不互素**：对 $n$ 归纳。$a_{n+1}$ 与每个 $a_i\ (i\le n)$ 有非平凡公因子（定义），故 $\gcd(a_i,a_{n+1})>1$；再由归纳假设即得所有项两两不互素。特别地 $\gcd(a_1,a_n)>1\ (\forall n\ge1)$。

**(F3) 项的每个非平凡倍数都在"候选集"里**：若 $x\ge a_1$ 且对一切 $i\le n$ 有 $\gcd(x,a_i)>1$，则由 $a_{n+1}$ 的最小性得 $a_{n+1}\le x$（当 $x>a_n$ 时）。

## §2 偏序 $\prec$ 与"只需检验极小项"

在项上定义关系
$$a_m\prec a_n\ :\iff\ m<n\ \text{且}\ \operatorname{rad}(a_m)\mid\operatorname{rad}(a_n).$$
（即 $\operatorname{supp}(a_m)\subseteq\operatorname{supp}(a_n)$ 且 $a_m$ 在前。）称项 $a_n$ 是**极小的**，若不存在 $a_m\prec a_n$。
直观：$a_m\prec a_n$ 时，$a_n$ 的素数集合覆盖了 $a_m$ 的，故 $a_n$ 对"谁与它相交"这件事不提供超出 $a_m$ 的信息。

**引理 2.1（归约）** 设整数 $x\ge a_1$。则
$$x\ \text{是项}\iff \gcd(x,a_i)>1\ \ \text{对每个极小项}\ a_i<x .$$

证明：$(\Rightarrow)$ 设 $x=a_m$，$a_i$ 极小且 $a_i<a_m$。则 $i<m$，由 (F2) 得 $\gcd(a_m,a_i)=\gcd(x,a_i)>1$。∎

$(\Leftarrow)$ 先证更强的命题
$$(\ast)\qquad \gcd(x,a_i)>1\ \ \text{对一切}\ i\ \text{满足}\ a_i<x .$$
对 $i$ 作强归纳：设 $a_i<x$。若 $a_i$ 极小，用假设。若 $a_i$ 非极小，取 $a_j\prec a_i$（$j<i$，$\operatorname{supp}(a_j)\subseteq\operatorname{supp}(a_i)$）；由 $a_j<a_i<x$ 及归纳假设 $\gcd(x,a_j)>1$，故 $x$ 与 $a_i$ 有公因子，即 $\gcd(x,a_i)>1$。命题 $(\ast)$ 得证。
现在若 $x$ 不是项：由 $x\ge a_1$ 与序列无界，存在 $n$ 使 $a_n<x<a_{n+1}$。由 $(\ast)$ 得 $\gcd(x,a_i)>1\ (\forall i\le n)$，即 $x$ 合格，由 (F3) 得 $a_{n+1}\le x$，矛盾。故 $x$ 是项。∎

## §3 大素数不可能出现在极小项中

**引理 3.1** 若大素数 $p>a_1^2$ 整除 $a_n$，则 $a_n$ 不是极小的。

证明：对 $n$ 作强归纳。写 $a_n=pc$。取素数 $q\mid\gcd(a_1,a_n)$（由 (F2) 存在，$\gcd>1$）。令
$$K:=\min\{k\ge1:\ q^kc\ge a_1\},\qquad x:=q^Kc .$$
则 $q^{K-1}c<a_1$（$K=1$ 时约定 $q^0c=c$，此时 $c<a_1$ 由 $K$ 的最小性给出），故
$$a_1\le x=q\cdot q^{K-1}c<q\,a_1\le a_1^2<a_n ,$$
最后一步用了 $q\le a_1$ 与 $a_n=pc\ge p>a_1^2$。

下面验证引理 2.1 的假设：设 $a_i$ 是极小项且 $a_i<x\,(<a_n)$。
1. **$p\nmid a_i$**：否则 $p\mid a_i$ 且 $p>a_1^2$ 是大素数、$i<n$，由归纳假设 $a_i$ 不是极小的，矛盾。
2. 由 (F2) $\gcd(a_n,a_i)>1$，取素数 $r\mid\gcd(a_n,a_i)$。由 1. 知 $r\ne p$；又 $a_n=pc$，故 $r\mid c$，于是 $r\mid q^Kc=x$，得 $\gcd(x,a_i)>1$。

由引理 2.1，$x$ 是项：$x=a_j$。又 $x<a_n$ 故 $j<n$。并且
$$\operatorname{supp}(x)=\operatorname{supp}(q)\cup\operatorname{supp}(c)\subseteq\operatorname{supp}(a_n),$$
因为 $q\mid a_n$（$q\mid\gcd(a_1,a_n)$）且 $c\mid a_n$。于是 $a_j\prec a_n$，即 $a_n$ 不是极小的。∎

**推论 3.2** 每个极小项的素因子都 $\le a_1^2$，即 $\operatorname{supp}(a_n)\subseteq P$ 对一切极小项 $a_n$ 成立。
（对 $n$ 归纳：若 $a_n$ 极小则无大素因子；由引理 3.1 的逆否即得。）

## §4 序列只依赖 $a \bmod L$：收尾

记 $L:=\prod_{p\in P}p$（$P=\{p\le a_1^2\}$，故 $L\ge2$）。对整数 $a\ge2$ 令
$$S(a):=\{p\in P:\ p\mid a\}\subseteq P .$$
定义 $F:=\{S(a_n):n\ge1\}\subseteq 2^{P}$（有限），及
$$\bar R:=\{r\in\mathbb Z/L\mathbb Z:\ S(r)\in F\},\qquad T:=|\bar R|\ (\ge1,\ \text{因}\ a_1\ \text{是项}).$$

**引理 4.1（序列的显式刻画）** 对 $a\ge a_1$：
$$a\ \text{是项}\iff a\bmod L\in\bar R .$$
证明：$(\Rightarrow)$ 若 $a=a_n$ 则 $S(a)=S(a_n)\in F$，故 $a\bmod L\in\bar R$。
$(\Leftarrow)$ 设 $S(a)\in F$，取 $n$ 使 $S(a)=S(a_n)$。用引理 2.1：只需对每个极小项 $a_i<a$ 验证 $\gcd(a,a_i)>1$。由推论 3.2，$\operatorname{supp}(a_i)\subseteq P$；由 (F2) 取素数 $r\mid\gcd(a_n,a_i)$，则 $r\in\operatorname{supp}(a_i)\subseteq P$，故 $r\in S(a_n)=S(a)$，即 $r\mid a$，于是 $\gcd(a,a_i)>1$。引理 2.1 给出 $a$ 是项。∎

**定理（本题）** 存在正整数 $T,L$ 使 $\forall n\ge1:\ a_{n+T}=a_n+L$。

证明：取上面的 $L,T$。对任意项 $a_n$：由引理 4.1，$a_n\bmod L\in\bar R$，故 $(a_n+L)\bmod L\in\bar R$ 且 $a_n+L>a_n\ge a_1$，于是由引理 4.1 $a_n+L$ 是项。
另一方面，区间 $(a_n,\,a_n+L]$ 恰含 $L$ 个整数、每个模 $L$ 的剩余类恰出现一次，故其中满足 $y\bmod L\in\bar R$ 的恰有 $T$ 个；由引理 4.1 这些正是一个项。于是紧随 $a_n$ 的 $T$ 个项恰为该区间的 $T$ 个元素，其中最大者是 $a_n+L$，即
$$a_{n+T}=a_n+L .\qquad\blacksquare$$

> 附注：只用到"$a_{n+1}$ 最小"这一条性质，与"$a_1>1$"共同构成全部输入；$T,L$ 可显式取 $L=\prod_{p\le a_1^2}p$。

## §5 与另一条等价包装（"friendly sets"）的关系

AoPS 上的另一解法把上述内容改写为集合语言：称有限素数集 $X$ **友好**，若 $X$ 与每个 $\operatorname{supp}(a_n)$ 相交；则任意两个友好集必相交（否则取 $x=\prod X$、$y=\prod Y$ 的高次幂，两者都出现在序列中却互素，矛盾），取"含 $p$ 的乘积最小友好集 $M$"，由 $M\setminus\{p\}$ 不友好得某 $a_i$ 与 $X=\prod(M\setminus\{p\})$ 互素，再由 $M$ 友好得 $p\mid a_i$，于是 $p\le a_i<a_1^2$（取 $x^k\in[a_1,a_1^2)$ 的那一步）——与本文引理 3.1 同源。二法殊途同归。

## §6 我们此前的独立路线（备用，现已非必需）

本项目早期（`30-final-proof.md`、`16-descent-fix.md`、`17-fme-indep.md`）走的是**另一条**路线：把问题化归为"$A_\infty$ 的极小元集 $\mathcal M$ 有限（FME）"，再证 $\neg R$（$\forall\mu\forall p\mid\mu:p\le2a_1$）或 $(CS)$。该路线自足、经对抗复核（`23-verification-L.md`），当时的唯一残余是三支显式不等式的"上界缺口"——正是本文引理 3.1 所提供的那种上界（我们的工具全是下界）。相关事实（项 $=A_\infty\cap[a_1,\infty)$、位置引理、私有指标、下降引理等）见 `31-final.md`，可作为对照阅读。

## §7 数值核对（针对**机制**，不只是结论）

脚本 `logs/verify33.py`（窗口 $B=4000$，$a_1\in\{2,3,4,6,12,15,30,35,45,99,121,175,187,899\}$）逐步生成真序列后，检验本文两条关键断言：
- **引理 4.1**（$a$ 是项 $\iff S(a)\in F$）——**零违例**；
- **推论 3.2**（每个 $\prec$-极小项只有小素因子）——**零违例**。

（输出：对每个 $a_1$ 报 `L1viol=0 C2viol=0 OK`，例如 $a_1=15$：$\texttt{|F|=440}$、$a_1=899$：$\texttt{|F|=811}$。）

其它已知事实（供对照）：所有已检样本中极小元的素因子 $\le a_1$，$\max p/a_1=1$（唯一 $a_1=p=2$），$\max\mu/(2a_1)=0.7241$（$a_1=899$）；$a_1=15$ 时序列为 $15,18,20,24,30,36,40,42,\dots$，其项恰为 $\ge15$ 且被 $2\cdot3$、$3\cdot5$、$2\cdot5$ 之一整除者（$L=30$）。

## §8 参考资料（联网核对）

- IMO 2026 试题（Problem 6，供题 Taiwan）：`https://www.imo-official.org/problems/2026`
- Evan Chen, *IMO 2026 Solution Notes*, §2.3（本文主证的结构）：`https://web.evanchen.cc/exams/IMO-2026-notes.pdf`
- AoPS 讨论帖（作者帖）：`https://aops.com/community/p38677077`；AoPS Wiki: `2026 IMO Problems/Problem 6`
