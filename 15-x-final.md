# H∧|B|≥2 收尾：缺口的最终等价形式、无条件新判据与残余单条不等式

> **作者**：prover-x（task-7）。**依赖**：`30-final-proof.md`（(P1)–(P6)、(K)、(M)、引理 2.2/3.1/4.1/5.1/5.2）、`13-mu-bound.md`、`14-H-gap.md`（其定理 2.2 的化归、定理 4.1/4.2 的闭环与 §5 的乘积约束均逐条自核后引用）。
> **口径（先看这里）**
> 1. **缺口已被压缩为一条不等式**（§2 定理 2.4，完全严格）：记 $m:=\max S$、$\sigma:=a_1/\operatorname{rad}(a_1)\ge1$，则
> $$H\iff \mu>a_1m\iff \Bigl[\ m\in B\ \wedge\ \prod_{p\in B\setminus\{m\}}p>\sigma\prod_{p\in A}p\ \Bigr]\ \vee\ \Bigl[\ m\in C\ \wedge\ X>m\,\sigma\prod_{p\in A}p\ \Bigr].$$
> 由于 $a_1\ge\operatorname{rad}(a_1)$（即 $\sigma\ge1$），立得**无条件新判据（定理 3.1、系 3.2、系 3.4）**：$m\in B$ 且 $\prod_{B\setminus\{m\}}p\le\prod_A p$ $\Rightarrow\neg H$；$m\in C$ 且 $X\le m\prod_A p$ $\Rightarrow\neg H$；$|B|=2$ 且 $\bigl(\prod_Cp\bigr)m\le a_1$ $\Rightarrow\mu\le2a_1^{2}$（不用 $H$）。数值上它们合计覆盖 $a_1\le1200$ 的全部 37 个 $|B|\ge2$ 案例中的 **36 个**（唯一逃逸：$|B|=3$ 的 $a_1=845,\mu=858$）。
> 2. **新引理（§4，已证）**：$H$ 且 $|S|=3$ 时（此时 $B=\{p,q\}$、$C=\{c\}$）必有 $4pq<c^{2}$、$c<pq$、$pq>a_1$、$c>2\sqrt{a_1}$、$c\le a_1/2$、$\mu<c^{3}/4$；故 $a_1\le64$ 时 $|S|=3$ 的 $H$ 不可能（$|S|\ge4$ 支仍开）。
> 3. 【已证明】安全乘积界：$a_1^{s}<\mu^{s-1}$、$\prod_{p\in B}\max(2,q_p)<\mu^{s-2}$（$s=|S|$；不依赖 13 §3.4.2 有争议的 $T_p<\mu/p$）；并定位 13 的 $s=3$ 闭环所需的唯一额外条件 $a_{i_p}p^{2}<\mu$。
> 4. 【数值】$H$ 在大 $B$（至 $60a_1$）下仍不出现，$\max\mu/a_1=1.4483\le2$，$\mathcal M$ 关于 $B$ 稳定；$\max rH=0.5$（$a_1\ge7$ 时 $0.1714$）。新提出并检验了指数猜想 $t(\mu)\le\mu/\max S$（0 反例）。
> 5. **残余缺口（唯一）**：$(\star)$ $|B|\ge2$ 且 $m\in B$ 且 $\prod_{B\setminus\{m\}}p>\sigma\prod_Ap$（或对偶的 $m\in C,\ X>m\sigma\prod_Ap$）下证 $\neg H$。任一 G1/G2 或下列更强形式之一即闭环：$\mu\le2a_1$，或 $X\le2\sigma\prod_Ap$，或 $X\le a_1$。**缺口未被完全关闭**；但已从"$H\wedge|B|\ge2$"精确化为上述单条不等式，并由 §3 的无条件判据在数值上覆盖 36/37。

---

## 1. 记号与已证工具（逐条自核）

固定整数 $a_1\ge2$，序列 $a_{n+1}=\min\{k>a_n:\gcd(k,a_i)>1\ \forall i\le n\}$。记 $D_n=\operatorname{supp}(a_n)$、$A_n$、$A_\infty$、$\mathrm{kill}$、$\mathcal M$（极小元集）、项；有限素集 $T$ 为**横截集** $\iff T\cap D_i\ne\varnothing\ \forall i$；于是 $k\in A_\infty\iff\operatorname{supp}(k)$ 是横截集，$A_\infty$ 对倍数封闭 (M)。以下引自 30/13/14，本文逐条复核：

* **(P1)** $\gcd(a_i,a_j)>1\ (i\ne j)$：每个 $D_j$ 是全族的横截集，且诸 $D_j$ 两两相交。
* **(P2)** 每个 $a_j\in A_\infty$；$k\in A_\infty\Rightarrow\operatorname{rad}(k)\in A_\infty$。**(K)** $k\in A_\infty\iff\mathrm{kill}(k)=\infty$。
* **(P4)(P5)** 项 $=$ $A_\infty\cap[a_1,\infty)$ 的递增枚举；特别 $k\ge a_1$ 是项 $\iff k\in A_\infty$。
* **引理 2.2** 每个 $k\in A_\infty$ 被某 $\mu\in\mathcal M$ 整除；$\mu$ 无平方因子；$\mu=\prod_{p\in\operatorname{supp}(\mu)}p$。
* **引理 3.1（位置引理）** $k\ge a_1,\ \mathrm{kill}(k)=i<\infty\Rightarrow a_i<k$。
* **引理 4.1（私有指标）** $p\in S:=\operatorname{supp}(\mu)\Rightarrow\exists i:D_i\cap S=\{p\}$。
* **引理 5.1（下降）** $\nu\in\mathcal M,\nu>2a_1,p\in\operatorname{supp}(\nu)\Rightarrow\exists\nu'\in\mathcal M:p\mid\nu',\operatorname{supp}(\nu')\cap\operatorname{supp}(\nu)=\{p\},\nu'<\nu/p$。
* **引理 5.2（素因子界）** $p\in S\Rightarrow p\le2a_1$。
* **（14 定理 4.1）** $|B|\le1\Rightarrow\mu\le a_1^{2}/2$（不用 $H$）。**（14 定理 4.2）** $|S|=2\Rightarrow\neg H$。**（14 系 4.4）** $H$ 下 $x\in B\Rightarrow a_{i_x}\ge2x$、$x^{2}<\mu/2$。

约定（与 14 §1 一致）：
$$S=\operatorname{supp}(\mu),\quad C=S\cap D_1,\quad B=S\setminus D_1,\quad A=D_1\setminus S,\quad X=\prod_{p\in B}p,\quad m=\max S .$$
$H$ 指 $\forall p\in S:\mu/p\ge a_1$。恒等式：$\mu=\bigl(\prod_Cp\bigr)X$，$\operatorname{rad}(a_1)=\bigl(\prod_Cp\bigr)\bigl(\prod_Ap\bigr)$，$C\ne\varnothing$（$S$ 横截），且 $B\ne\varnothing\Rightarrow A\ne\varnothing$（14 引理 $\ast$）。

**引理 1.1（$i_p$ 的刻画，已证）** 对 $p\in S$ 令 $i_p:=\mathrm{kill}(\mu/p)$（当 $\mu/p\notin A_\infty$ 时 $<\infty$）。若 $|S|\ge2$ 则 $\mu/p\ge2$ 是 $\mu$ 的真因子，故由极小性与 (K) 得 $i_p<\infty$；并且
$$i_p=\min\{i\ge1:D_i\cap S=\{p\}\},\qquad D_{i_p}\cap S=\{p\},\qquad p\mid a_{i_p}.$$
证明：$\mathrm{kill}(\mu/p)=\min\{i:\gcd(\mu/p,a_i)=1\}=\min\{i:D_i\cap(S\setminus\{p\})=\varnothing\}$，而 $D_i\cap S\ne\varnothing$（横截），故 $=\min\{i:D_i\cap S=\{p\}\}$；取到后 $p\in D_{i_p}$。∎

**引理 1.2（$H$ 的严格化，13 引理 3.2）** $H\Rightarrow\mu/p>a_1\ \forall p\in S$；特别 $H\Rightarrow\mu>a_1m\ge2a_1$，且 $i_p<\infty$、位置引理可用：$a_{i_p}<\mu/p$。∎

---

## 2. 缺口的精确等价形式（本文核心化归）

**引理 2.1（不变量恒等式，新）** 记 $\sigma:=a_1/\operatorname{rad}(a_1)\in\mathbb Z_{\ge1}$。则
$$\frac{\mu}{a_1}=\frac{X}{\sigma\prod_{p\in A}p}\qquad\text{（精确恒等式）}.$$
证明：$\mu=(\prod_Cp)X$，$a_1=\operatorname{rad}(a_1)\sigma=(\prod_Cp)(\prod_Ap)\sigma$，相除即得。∎

**系 2.2（充分条件的等价写法，新）**
1. $\neg H\iff X<\sigma\bigl(\prod_Ap\bigr)m$；$H\iff X>\sigma\bigl(\prod_Ap\bigr)m$（等号不可能，见定理 2.4）。
2. $\mu\le2a_1\iff X\le2\sigma\prod_Ap$；故 $\mu\le2a_1\Rightarrow\neg H$（因 $H\Rightarrow\mu>2a_1$）。
3. $X\le a_1\Rightarrow\mu\le a_1X\le a_1^{2}\le2a_1^{2}$（G2；与 14 系 2.3 一致）。

**引理 2.3（$\neg H$ 的闭环口径）** $\neg H\Rightarrow\exists p\in S:\mu/p<a_1\Rightarrow\mu<a_1p\le2a_1^{2}$（引理 5.2），于是由 14 引理 2.1、定理 2.2 存在项 $a_t$ 满足 $D_t=S$、$t<2a_1^{2}$，TCL 常数可取 $N=2a_1^{2}$。∎

**定理 2.4（缺口的最终形式，完全严格）** 设 $|S|\ge2$。则
$$\mu=a_1m\ \text{不可能};\qquad H\iff\mu>a_1m\iff\prod_{p\in S\setminus\{m\}}p>a_1 .$$
并且（按 $m$ 的归属分情形，两侧均为 $\iff$）
$$m\in B:\quad H\iff \prod_{p\in B\setminus\{m\}}p>\sigma\prod_{p\in A}p;\qquad
m\in C:\quad H\iff X>m\,\sigma\prod_{p\in A}p .$$
证明：$\mu\ge a_1m\iff H$，而 $H$ 经引理 1.2 给出 $\mu>a_1m$，故 $\mu=a_1m$ 不可能，且 $H\iff\mu>a_1m$，即 $\prod_{S\setminus\{m\}}p=\mu/m>a_1$。

* $m\in B$：$\mu/m=(\prod_Cp)(\prod_{B\setminus\{m\}}p)$，而 $a_1=\sigma(\prod_Cp)(\prod_Ap)$；约去 $\prod_Cp>0$ 得 $\iff\prod_{B\setminus\{m\}}p>\sigma\prod_Ap$。
* $m\in C$：$\mu/m=(\prod_{C\setminus\{m\}}p)X$，$a_1=\sigma m(\prod_{C\setminus\{m\}}p)(\prod_Ap)$；约去 $\prod_{C\setminus\{m\}}p$ 得 $\iff X>m\sigma\prod_Ap$。∎

**注 2.5（缺口的最窄形式）** 只需在
$$(\star)\qquad |B|\ge2,\quad m\in B,\quad \prod_{p\in B\setminus\{m\}}p>\sigma\prod_{p\in A}p$$
（或对应的 $m\in C$ 形式）下证明 $\neg H$。$|S|\le2$、$B=\varnothing$、$|B|=1$ 已在 14 闭环，故 $(\star)$ 里 $|S|\ge3$。

---

## 3. 无条件新判据（$H$ 的必要条件）

**定理 3.1（$H$ 的必要条件，新）** $H$ 成立时：
$$m\in B\ \Rightarrow\ \prod_{p\in B\setminus\{m\}}p>\prod_{p\in A}p;\qquad
m\in C\ \Rightarrow\ X>m\prod_{p\in A}p .$$
证明：$H$ 经引理 1.2 给 $\mu/m>a_1\ge\operatorname{rad}(a_1)=(\prod_Cp)(\prod_Ap)$。$m\in B$ 时 $\mu/m=(\prod_Cp)(\prod_{B\setminus\{m\}}p)$，约去 $\prod_Cp$ 即得第一式（比定理 2.4 弱了 $\sigma\ge1$ 这一因子，故为**无条件**判据）；$m\in C$ 时 $\mu/m=(\prod_{C\setminus\{m\}}p)X$ 且 $\operatorname{rad}(a_1)=m(\prod_{C\setminus\{m\}}p)(\prod_Ap)$，约去后得第二式。∎

**系 3.2（$H$-free 判据，可直接使用的闭环）**
$$m\in B\ \wedge\ \prod_{p\in B\setminus\{m\}}p\le\prod_{p\in A}p\ \Longrightarrow\ \neg H\ \Longrightarrow\ \mu<2a_1^{2};$$
$$m\in C\ \wedge\ X\le m\prod_{p\in A}p\ \Longrightarrow\ \neg H\ \Longrightarrow\ \mu<2a_1^{2}.$$
（用定理 3.1 取逆否 + 引理 2.3。）

**系 3.3（更弱但更易用的形式）** 若 $m\in C$ 且 $X\le a_1$（或 $X\le2\prod_Ap$、$X\le m$ 等）则闭环；若 $m\in B$ 且 $\prod_{B\setminus\{m\}}p\le2$（即 $|B|=2$ 且较小者 $\le2$，或 $|B|=1$）也闭环。

**系 3.4（$|B|=2$ 的无条件界，不用 $H$，新）** 若 $|B|=2$ 且
$$\Bigl(\prod_{p\in C}p\Bigr)\cdot m\ \le\ a_1,$$
则 $\mu\le2a_1^{2}$（从而 TCL 常数 $N=2a_1^{2}$ 对该 $\mu$ 成立）。
证明：$B=\{p,m\}$（$p\le m=\max S$），$m\le2a_1$、$p\le2a_1$（引理 5.2），故
$$\mu=\Bigl(\prod_Cp\Bigr)pm\ \le\ \Bigl(\prod_Cp\Bigr)m\cdot2a_1\ \le\ 2a_1\cdot a_1=2a_1^{2}.\qquad\blacksquare$$
（注意 $\prod_Cp\le\operatorname{rad}(a_1)$，故 $\bigl(\prod_Cp\bigr)m\le a_1$ 是容易核对的条件；例如 $(a_1,\mu)=(375,399)$：$\prod_Cp=3,m=19$，$57\le375$ ✔。对 $|B|\ge3$ 同一手法失效：$\mu\le(\prod_Cp)(2a_1)^{|B|-1}m$ 要求 $(\prod_Cp)m\le(2a_1)^{2-|B|}$，$|B|=3$ 时为 $\le1/2$，故 $|B|\ge3$ 必须用 $H$ 或更细的结构。）

**注 3.5（判据的覆盖力，数值）** 在 $a_1\le1200$（$B_{\rm scan}=12a_1$）上，$|B|\ge2$ 的极小元共 37 例；系 3.2 直接判否 35 例、系 3.4 无条件闭环 18 例，**两者合计覆盖 36/37**。唯一逃逸者是
$$(a_1,\mu)=(845,858):\ S=\{2,3,11,13\},\ C=\{13\},\ B=\{2,3,11\},\ A=\{5\},\ X=66,\ m=13,\ \prod_Cp=13,$$
它满足 $\bigl(\prod_Cp\bigr)m=169\le845$，但 $|B|=3$ 使系 3.4 失效；此处 $H$-条件（定理 2.4，$m\in B$）要求 $2\cdot3=6>13\cdot5=65$，为假，故仍 $\neg H$。另有 $(a_1,\mu)=(375,399)$：系 3.2 需借助 $\sigma$，而系 3.4 无条件闭环 ✔。

**注 3.6（判据为何不能再弱化）** 反例（数值，$a_1=375,\mu=399$）：$X=133>\prod_Ap\cdot m=5\cdot19=95$，故"$X\le\prod_Ap\cdot m$"这一更弱的充分条件**不成立**；同时 $X/a_1=0.3547<1$，故 G2 型判据仍有余量。可见 $\prod_Ap\cdot m$、$\sigma\prod_Ap\cdot m$ 与 $a_1$ 三者的差距是实质的：不能指望"$X\le(\text{某个 }A\text{-侧乘积})$"式的判据覆盖全部情形，$|B|\ge3$（淘汰者是 $|S|\ge4$）与 $\prod_Ap$ 很小时需要新的结构输入。

---

## 4. $|S|=3$ 的 $H$-结构（新）与乘积界（修正 13 的用法）

**引理 4.1（$B$ 侧量词的正确下界，已证）** 设 $p\in B$、$H$ 成立。则 $D_{i_p}\cap D_1\ne\varnothing$（(P1)）且 $D_{i_p}\cap D_1\subseteq A$（$D_{i_p}\cap S=\{p\}\ni p\notin D_1$），取 $q_p\in A$、$q_p\mid a_{i_p}$。因 $\gcd(p,q_p)=1$（$p\notin D_1\ni q_p$）得 $pq_p\mid a_{i_p}$，又 $a_{i_p}\ne p$（否则 $\operatorname{supp}(p)=\{p\}$ 横截 $\Rightarrow p\mid a_1\Rightarrow p\in D_1$）故 $a_{i_p}\ge2p$。于是
$$a_{i_p}\ \ge\ \max(2p,\ p\,q_p),\qquad\text{从而}\qquad \max\bigl(2p^{2},\ p^{2}q_p\bigr)<\mu .$$
（右式由 $a_{i_p}p<\mu$，即位置引理。）∎

**注 4.2（对 13/14 的两处记账更正）**
1. 由上：$p^{2}q_p<\mu$ 与 $2p^{2}<\mu$ 都成立，但**$2p^{2}q_p<\mu$ 需要 $2q_p\mid a_{i_p}/p$ 才成立**（例如 $a_{i_p}=3p$、$q_p=3$ 时 $a_{i_p}=pq_p$）。本文只用 $p^{2}q_p<\mu$、$2p^{2}<\mu$。
2. 13 §4 的 $s=3$ 分支把 $T_x=a_{i_x}x$ 的交叉素因子当作互不相同（$T_x\ge a_1x\,r_{xy}r_{xz}$）。安全写法是 $a_{i_x}\ge x\max(r_{xy},r_{xz})$（$r$ 可重合）；由此 $\prod_xa_{i_x}\ge\mu\,R$、$R:=r_{pq}r_{pr}r_{qr}$（用 $\max(a,b)\max(a,c)\max(b,c)\ge abc$）。13 的结论 $\mu>8a_1^{3}$ 还需**额外条件 $T_p<\mu/p$（$\iff a_{i_p}p^{2}<\mu$）**；仅用 $T_p<\mu$ 只能得下一条。

**定理 4.3（$H$ 下的安全乘积界，不依赖 $T_p<\mu/p$）** $H$ 成立、$s=|S|\ge2$。则
$$\text{(i) }a_1^{s}<\mu^{s-1};\qquad \text{(ii) }X^{2}\prod_{p\in B}\max(2,q_p)<\mu^{|B|};\qquad \text{(iii) }\prod_{p\in B}\max(2,q_p)<\mu^{s-2},\ \text{特别}\ 2^{|B|}<\mu^{s-2}.$$
证明：由引理 1.2，$a_{i_p}<\mu/p$ 对一切 $p\in S$ 成立，故
$$\prod_{p\in S}a_{i_p}<\prod_{p\in S}\frac{\mu}{p}=\frac{\mu^{s}}{\prod_{p\in S}p}=\mu^{s-1}. \tag{4.1}$$
另一方面：$p\in B$ 时由引理 4.1 有 $a_{i_p}\ge\max(2p,pq_p)\ge p\max(2,q_p)$；$p\in C$ 时 $a_{i_p}\ge p$（$p\mid a_{i_p}$）。两式相乘并用 $\prod_{p\in C}p\cdot X=\mu$：
$$\prod_{p\in S}a_{i_p}\ \ge\ X\Bigl(\prod_{p\in C}p\Bigr)\prod_{p\in B}\max(2,q_p)\ =\ \mu\prod_{p\in B}\max(2,q_p). \tag{4.2}$$
又 $a_{i_p}\ge a_1$（项），故 $\prod_{p\in S}a_{i_p}\ge a_1^{s}$。由 (4.1)+(4.2) 得 (iii)（约去 $\mu$）；由 (4.1) 与 $a_1^{s}$ 得 (i)；(ii) 由 (4.2) 限制在 $B$ 上：$\prod_{p\in B}a_{i_p}\ge X\prod_{p\in B}\max(2,q_p)$ 而 $\prod_{p\in B}a_{i_p}<\prod_{p\in B}\mu/p=\mu^{|B|}/X$。∎

**注 4.3.1** (i) 在 $s=3$ 时给 $\mu>a_1^{3/2}$；(iii) 在 $|B|\ge2$、$s=3$ 时给 $\mu>4$。这些界弱于 $H\Rightarrow\mu>2a_1$（后者来自 $\mu>a_1\max S\ge2a_1$），但 (ii) 是 $|B|=2$ 时唯一形如"$X$ 的下界"之外的乘积信息。若另外能证 $a_{i_p}p^{2}<\mu$（$\iff T_p<\mu/p$），则 (4.1) 可改写为 $\prod_{p\in S}T_p<\mu^{s-1}$，配合 $T_p\ge a_1pR_p$ 得 $a_1^{s}\prod_{p\in S}R_p<\mu^{s-2}$；$s=3$ 时即 $\mu>8a_1^{3}\ge(2a_1)^{3}\ge\mu$ 的矛盾——这正是 13 §4 的 $s=3$ 闭环，其唯一未证前提就是 $a_{i_p}p^{2}<\mu$。

**定理 4.4（$|S|=3$ 时的 $H$-约束，新）** 设 $H$ 成立、$S=\{p,q,c\}$（由 $|B|\ge2\Rightarrow|C|=1$，可记 $B=\{p,q\}$、$C=\{c\}$，$c\mid a_1$）。则
$$4pq<c^{2},\qquad c<pq,\qquad pq>a_1,\qquad c>2\sqrt{a_1},\qquad c\le a_1/2,\qquad \mu< c^{3}/4 .$$
证明：由引理 4.1（对 $x=p,q$）：$2x^{2}<\mu$，即 $2p^{2}<qc$、$2q^{2}<pc$；相乘得 $4p^{2}q^{2}<pqc^{2}$，即 $4pq<c^{2}$。又 $a_{i_c}<\mu/c=pq$（引理 1.2）且 $c\mid a_{i_c}$（引理 1.1），故 $c<pq$。$H$ 对 $x=c$ 给 $\mu/c=pq>a_1$。由 $4pq<c^{2}$ 与 $pq>a_1$ 得 $c>2\sqrt{a_1}$。$B\ne\varnothing\Rightarrow A\ne\varnothing\Rightarrow\prod_Ap\ge2$，故 $\operatorname{rad}(a_1)\ge c\prod_Ap\ge2c$，即 $c\le a_1/2$。最后 $\mu=pqc$ 与 $pq<c^{2}/4$ 给 $\mu<c^{3}/4$。∎

**系 4.5（$a_1\le64$ 时 $|S|=3$ 的 $H$ 不可能，新）** 若 $a_1\le64$，由 $c\le a_1/2$ 与 $a_1/2\le2a_1^{2/3}\iff a_1\le64$ 得 $c\le2a_1^{2/3}$，即 $c^{3}\le8a_1^{2}$，于是 $\mu<c^{3}/4\le2a_1^{2}$。∎
（对 $a_1>64$ 需更强上界；注意定理 2.4 的残余形式此时要求 $\prod_{B\setminus\{m\}}p>\sigma\prod_Ap\ge\prod_Ap\ge2$，例如 $m=q$ 时 $p>\prod_Ap$。）

**系 4.6（$|S|=3$、$m=c$ 的残余必要条件）** 若 $m=c$（即 $c>p,q$），则定理 2.4 给 $pq>c\sigma\prod_Ap\ge c\prod_Ap$；结合 $pq<c^{2}/4$ 得 $c>4\prod_Ap\ge8$。∎

---

## 5. 数值证据（精确整数；脚本 `logs/x_final.py`、`x_wide.py`、`x_index.py`、`x_close.py`、`x_hunt.py`）

计算方式与 14 §7 相同（生成到首个 $a_N>B$，增量维护 $\min A_n$；$a_N>B$ 时 $\min A_N\cap[2,B]=\mathcal M\cap[2,B]$，精确）。**新增大 $B$ 复核**：此前扫描用 $B=8a_1$ 或 $12a_1$，而 $H$ 只保证 $\mu>2a_1$（$\mu$ 可以更大），故本轮专门放大 $B$。

| 检验 | 范围 | 结果 |
|---|---|---|
| $H$（$\exists p:\mu/p\ge a_1$，即 $rH\ge1$） | $a_1\le1600,\ B=8a_1$；$a_1\le900,\ B=12a_1$ | **0 例** |
| $H$（放大 $B$） | $a_1\le200,\ B=60a_1$（`logs/x_wide.py` 运行输出） | **0 例** |
| $\mathcal M$ 随 $B$ 的稳定性 | $a_1\in\{2,15,35,94,202,375,899\}$，$B/a_1\in\{20,200\}$ | $\#\mathcal M$、$\max\mathcal M$ 完全不变（如 $a_1=899$：$\#\mathcal M=6,\max\mathcal M=1302$） |
| $\max\mu/a_1$ | $a_1\le1600$ | $1.4483$（$a_1=899,\mu=1302$）$\le2$，即 $\mu\le2a_1$ 无反例 |
| $\max rH=\mu/(a_1\max S)$ | $a_1\le1600$ | 最大值 $0.5$ 仅在 $a_1=2$（$a_1=3,5,15$ 分别为 $0.333,0.2,0.2$）；$a_1\ge7$ 时最大 $0.1714$（$a_1=35$）——非平凡情形下 $H$ 距成立差约 6 倍 |
| $X\le a_1$（G2） | $a_1\le1600$ | 0 反例，$\max X/a_1=0.3547$（$a_1=375,\mu=399$） |
| $X\le\prod_Ap\cdot m$ | $a_1\le1200$ | **反例 2 例**（$a_1=375$；$a_1=845$），见注 3.6 |
| $|B|\ge2$ 案例（$a_1\le1200$，共 37 例） | 系 3.2 + 系 3.4 | 覆盖 36 例（系 3.2 判否 35，系 3.4 无条件闭环 18，并集 36）；唯一逃逸 $a_1=845,\mu=858$（$|B|=3$），其 $H$-条件为假（$6>65$ ✗）故仍 $\neg H$ `logs/x_close.py` |
| 指数猜想 $t(\mu)\le\mu/\max S$ | $a_1\le700,\ B=10a_1$ | 0 反例，$t/(\mu/m)\le1$，等号仅 $a_1=2$（`logs/x_index.py`） |

**注 5.1（恒等式与判据的机器复核）** 在 $a_1\le1200$ 的全部 289 个极小元上（精确有理数）：引理 2.1 的恒等式 $\mu/a_1=X/(\sigma\prod_Ap)$ 0 反例；$\mu\le2a_1^{2}$ 0 反例；系 3.2 触发 35 次、系 3.4 触发 18 次，**均无与其结论矛盾者**（`logs/x_close.py` 的运行脚本）。

**注 5.2（猜想 $t(\mu)\le\mu/\max S$ 的用处，数值）** 由 (P6) $a_{n+1}-a_n\le\operatorname{rad}(a_1)$ 得 $\mu=a_{t(\mu)}\le a_1+(t-1)\operatorname{rad}(a_1)$；若 $t(\mu)\le\mu/m$，则
$$\mu\Bigl(1-\frac{\operatorname{rad}(a_1)}{m}\Bigr)\le a_1-\operatorname{rad}(a_1)\quad\Longrightarrow\quad m>\operatorname{rad}(a_1)\ \text{时}\ \mu\le\frac{(a_1-\operatorname{rad}a_1)m}{m-\operatorname{rad}a_1},$$
于是 $m\ge2\operatorname{rad}(a_1)$ 时 $\mu\le2a_1$（$\Rightarrow\neg H$）；与 $H$ 联立进一步给出 $m\le\operatorname{rad}(a_1)$。这是把 5 中"$\mu\le2a_1$ 无反例"变成定理的一条可行路线（【缺口】，待证）。

---

## 6. 残余缺口与建议路线（按可行性）

**缺口 6.1（唯一）** 在
$$|B|\ge2,\quad m\in B,\quad \prod_{p\in B\setminus\{m\}}p>\sigma\prod_{p\in A}p$$
（或 $m\in C,\ X>m\sigma\prod_Ap$）下证明 $\mu\le2a_1^{2}$（等价地 $\neg H$；两者都已由 14 定理 2.2 化归到 TCL 常数 $N=2a_1^{2}$）。**已闭环**：$|S|\le2$（14 定理 4.2）、$B=\varnothing$、$|B|=1$（14 定理 4.1）、$|S|=3$ 且 $a_1\le64$（系 4.5）、系 3.2 覆盖的"$B$ 侧乘积 $\le A$ 侧乘积"的全部情形（含 $m\in C\wedge X\le m\prod_Ap$）、以及系 3.4 覆盖的"$|B|=2$ 且 $\prod_Cp\cdot m\le a_1$"。数值上（$a_1\le1200$）这些判据合计覆盖全部 37 个 $|B|\ge2$ 案例中的 36 个，唯一逃逸者 $(a_1,\mu)=(845,858)$ 亦满足 $H$ 的否定（定理 2.4 的 $H$-条件为假），但该否定目前只能逐例核对、不能由既有判据统一给出。

**路线（本文提供的新工具）**
1. **证 $\mu\le2a_1$（最强充分）**：等价于 $X\le2\sigma\prod_Ap$（系 2.2.2），数值最大比值 $1.4483$。若能证注 5.1 的指数猜想（或它的弱形式 $t\le2\mu/m$ 之类），则由 (P6) 可得 $\mu\le2a_1$。
2. **证 $\neg H$（G1）**：即证 $\prod_{S\setminus\{m\}}p<a_1$。可用输入：定理 3.1/2.4 的必要条件、定理 4.4（$s=3$ 约束）、定理 4.3、引理 4.1 的下界 $\max(2p^{2},p^{2}q_p)<\mu$、以及 $H$ 给出的全部 $a_{i_p}<\mu/p$ 与 $D_{i_p}\cap S=\{p\}$。
3. **证 $X\le a_1$（G2）**：数值最紧处 $X/a_1=0.3547$，但注意 $X/(\sigma\prod_Ap)$ 最紧处为 $1.4483$；$X\le a_1$ 与 $X\le2\sigma\prod_Ap$ 互不包含，前者在 $\prod_Ap$ 大时更有效。
4. **补 13 的 $s=3$ 缺口**：若证明额外条件 $a_{i_p}p^{2}<\mu$（等价 $T_p<\mu/p$）在 $H$ 下成立，则 13 §4 的 $s=3$ 结论 $\mu>8a_1^{3}> (2a_1)^{3}\ge\mu$ 立得矛盾，于是 $H\Rightarrow|S|\ge4$，缺口收缩到 $|S|\ge4$（配合定理 4.4 的结构信息）。

**注 6.2（$H$ 是否真的可能？）** 在 $a_1\le1600$（$B=8a_1$）、$a_1\le900$（$B=12a_1$）、$a_1\le200$（$B=60a_1$）三档扫描中 $H$ **从未成立**，且 $\mathcal M$ 关于 $B$ 稳定、$\max rH=0.5$（非平凡情形 $0.1714$）。故经验上 $H$ 极可能不可能（G1 为真），但既有不等式只给 $\mu>2a_1$、$H\Rightarrow m\in B\wedge\prod_{B\setminus\{m\}}p>\sigma\prod_Ap$ 等**下界型**信息，尚不足以导出矛盾。

---

## 7. 已证 / 缺口清单

**已证（严格、自足，只用 §1 引用事实）**

1. 引理 1.1（$i_p=\min\{i:D_i\cap S=\{p\}\}$、$p\mid a_{i_p}$）、引理 1.2。
2. 引理 2.1（恒等式 $\mu/a_1=X/(\sigma\prod_Ap)$）、系 2.2、引理 2.3、**定理 2.4（缺口 $\iff$ 单条不等式，含 $\mu=a_1m$ 不可能）**。
3. **定理 3.1 / 系 3.2 / 系 3.4（$H$ 的无条件必要条件、$H$-free 闭环判据、$|B|=2$ 的无条件界）**，注 3.5（判据的数值覆盖力）与注 3.6（判据不能更弱化：$X\le\prod_Ap\cdot m$ 有反例）。
4. 引理 4.1（正确的下界 $\max(2p^{2},p^{2}q_p)<\mu$）、注 4.2（对 13/14 两处记账的更正）、定理 4.3 与注 4.3.1（安全乘积界，并把 13 的 $s=3$ 闭环归结为唯一前提 $a_{i_p}p^{2}<\mu$）、**定理 4.4 与系 4.5（$|S|=3$ 且 $a_1\le64$ 时 $H$ 不可能）**、系 4.6。
5. §5 的全部数据结论（精确整数）。

**缺口**

6. 缺口 6.1：$(\star)$ 情形下 $\neg H$（或 $\mu\le2a_1$、$X\le2\sigma\prod_Ap$、$X\le a_1$ 任一）。数值 0 反例；建议路线见 §6。**未闭环**，但缺口已从"$H\wedge|B|\ge2$"精确化为"$B$ 侧乘积严格大于 $A$ 侧乘积"的单条不等式，并被 §3 的无条件判据在 $a_1\le1200$ 的数据上覆盖 $36/37$；唯一逃逸者 $(a_1,\mu)=(845,858)$ 需 $|B|\ge3$ 的新输入。
