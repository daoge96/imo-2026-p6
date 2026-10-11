# 独立路线（task-9）：FME / $\mu\le2a_1$ 的 descent-free 归约 + 大规模反例搜索

> 作者：prover-mu。依赖：`30-final-proof.md`（记号与 (P1)–(P5),(K),(M)、引理 2.2/3.1/4.1）、`13-mu-bound.md`（本文作者的强化下降引理 2.1）。
> 本文**不重读、不修改** `30-final-proof.md`；路线与 `16-descent-fix.md`（prover-descent 的分情形修补）互补：本文用「**把下降引理的假设改成正确阈值 $\nu>a_1p$**」+「$E_p$ 的最小元」来绕开被外部评语指出的那一步（$\nu/p\ge\nu/2>a_1$ 只对 $p=2$ 成立）。
> 标注约定：【已证明】= 本文或已定稿文件中完整证明；【缺口】= 明确残余。

---

## 0. 摘要

1. 【已证明】一组**完全不用下降引理**的结构事实（§1）：$\mathcal M$ 与「族的极小横截集」一一对应；$\forall k\ge2:\ k\operatorname{rad}(a_1)\in A_\infty$；私有指标；$E_p\ne\varnothing\Rightarrow\min E_p\le a_1p$（与 Lead 独立给出的同一条一致）。
2. 【已证明】$\mu\le2a_1\ (\forall\mu\in\mathcal M)$ 一旦成立，则 §5 引理 5.1 **空真**、引理 5.2 平凡、FME 与 TCL 常数 $N=2a_1^2$ 立刻可得（§2 给出逐句推导）。这就是「$\mu\le2a_1$ 与被指出的缺口是同一件事的两面」的精确含义。
3. 【已证明】把 §5 引理 5.1 的假设从 $\nu>2a_1$ 换成 $\nu>a_1p$ 后，其证明（含第 4 步）**逐字成立**（因为需要的是 $\nu/p\ge a_1$，而 $\nu>a_1p\Rightarrow\nu/p>a_1$）；由此得 $E_p$ 的最小元界 $\nu_p\le a_1p\le a_1^2$（§1.4），**这条链不再依赖任何分情形**。
4. 【缺口】最窄残余命题 R（§3）：存在 $\nu\in\mathcal M$ 与素数 $p\mid\nu$，使 $2a_1<\nu\le a_1p$ 且 $p>2a_1$。反驳 R $\Rightarrow$ 引理 5.2（$p\le2a_1$）$\Rightarrow$ FME $\Rightarrow$ 原题；若 R 成立则应能构造 $\mu>2a_1$ 的样本。
5. 【数值】§4：$a_1\le10^4$ 全扫描 0 例 $\mu>2a_1$、0 例 (CS) 反例；$B\in\{3a_1,6a_1,10a_1\}$ 截断稳定性检查全通过。

---

## 1. descent-free 工具（全部【已证明】，只需 (P1)–(P5),(K),(M)、引理 2.2/3.1/4.1）

以下固定 $a_1\ge2$；$D_n=\operatorname{supp}(a_n)$；$R:=\operatorname{rad}(a_1)$；$\mathcal M$ = $A_\infty$ 的极小元集；**项** = 某个 $a_t$。

**引理 1.1（$\mathcal M$ = 极小横截集之积）【已证明】**
$$\mu\in\mathcal M\iff \operatorname{supp}(\mu)\ \text{是族}\ \{D_t\}_{t\ge1}\ \text{的包含极小横截集}.$$
证明：$\Rightarrow$：$\mu\in A_\infty$ 给出 $S:=\operatorname{supp}(\mu)$ 横截；若存在横截 $S'\subsetneq S$，则 $k:=\prod_{p\in S'}p\ge2$ 满足 $k\in A_\infty$（(M) 的封闭性 / 横截定义）且 $k\mid\mu$、$k<\mu$，与极小性矛盾。
$\Leftarrow$：设 $S$ 是包含极小横截集，$\mu:=\prod_{p\in S}p$。由 $\mu$ 无平方因子且 $S$ 横截得 $\mu\in A_\infty$；若 $\nu\mid\mu$、$2\le\nu<\mu$、$\nu\in A_\infty$，则 $\operatorname{supp}(\nu)=\{p\in S:p\mid\nu\}$ 是横截真子集（否则 $\nu=\prod_{p\in S}p=\mu$），与 $S$ 极小矛盾。故 $\mu\in\mathcal M$。∎
（推论：$|\mathcal M|$ = 极小横截集个数；FME $\iff$ 极小横截集只有有限多个。）

**引理 1.2（倍数格点）【已证明】** 对每个 $k\ge2$：$kR\in A_\infty$；因此
$$\min\{z\in A_\infty:z\ge k\}\le kR,\qquad\text{特别}\ \min\{z\in A_\infty:p\mid z\}\le pR\ \ (p\ \text{素}),$$
且 $A_\infty\cap[a_1,\infty)$ 中相邻两元间隔 $\le R$（由 (P2) $R\in A_\infty$ 与 (M) 取倍数封闭）。
证明：$R\in A_\infty$（(P2)），$A_\infty$ 对取倍数封闭（(M)），故 $R\mathbb Z_{\ge2}\subseteq A_\infty$，于是 $kR\in A_\infty$。∎
（注：这是"$p\cdot\operatorname{rad}(a_1)\in A_\infty$"的一般形式，也是"项序列间隔 $\le R$"的出处；但注意 $\min\{z\in A_\infty:p\mid z\}$ 一般**远小于** $\min\{\mu\in\mathcal M:p\mid\mu\}$（陷阱：$a_1=187,p=3$：$66$ vs $102$），两者不可混用。）

**引理 1.3（私有指标，descent-free 重述）【已证明】** $\mu\in\mathcal M$，$p\in\operatorname{supp}(\mu)=:S$ $\Rightarrow$ $\exists i\ge1:D_i\cap S=\{p\}$。
证明（与 30 §4 同，但不涉及下降）：$S$ 横截，故 $D_i\cap S\ne\varnothing\ \forall i$。若 $\mu=p$ 取 $i=1$。否则 $\mu/p\ge2$ 是 $\mu$ 的真因子，由极小性 $\mu/p\notin A_\infty$，令 $i:=\mathrm{kill}(\mu/p)<\infty$；则 $\operatorname{supp}(\mu/p)=S\setminus\{p\}$ 与 $D_i$ 不交，故 $D_i\cap S\subseteq\{p\}$，又非空，故 $=\{p\}$。∎

**引理 1.4（$E_p$ 的最小元 $\le a_1p$）【已证明】** 设 $p$ 为素数、$E_p:=\{\mu\in\mathcal M:p\mid\mu\}\ne\varnothing$，$\nu_p:=\min E_p$。则
$$\frac{\nu_p}{p}\le a_1,\qquad\text{即}\quad \nu_p\le a_1p\quad(\text{仅当 }p\le a_1\text{ 时才进一步有 }\nu_p\le a_1^2).$$
证明：先注意 $\nu_p\ge p$（$p\mid\nu_p$）。若 $\nu_p>a_1p$，则 $k:=\nu_p/p>a_1\ge a_1$，把 30 §5 引理 5.1 的证明逐字用于 $(\nu,\textbf{p}):=(\nu_p,p)$：第 1 步用 (P5)（$\nu_p>a_1p\ge a_1$），第 2 步 $\nu_p/p>a_1\ge2$，第 3 步由极小性 $\nu_p/p\notin A_\infty$，**第 4 步的位置引理只需 $k\ge a_1$，此处由 $\nu_p/p>a_1$ 保证**（不需要 $\nu_p>2a_1$）；第 5–9 步照抄，得 $\nu'\in\mathcal M$，$p\mid\nu'$，$\nu'<\nu_p/p<\nu_p$，与 $\nu_p=\min E_p$ 矛盾。故 $\nu_p\le a_1p$。∎
（这正是外部评语所指缺口的干净修补方式：**改假设而不是改推理**。等价说法：若把 30 §5 引理 5.1 的假设写成 $\nu>a_1p$，则其第 4 步的 $k=\nu/p\ge a_1$ 直接成立。Lead 独立给出的同一条 $\nu_p/p\le a_1$ 与此一致。）

**引理 1.5（$\mathcal M$ 的元素都不是 $R$ 的"新素数"所致——避免误用）【已证明】** $p\in\operatorname{supp}(\mu)\Rightarrow p\le 2a_1$ ——这是 30 §5 引理 5.2 的结论；本文 §3 给出它的一条补充证明需求（残余 R）。

---

## 2. 为什么「$\mu\le2a_1$」= 缺口的另一面【已证明】

设 $\mu\le2a_1$ 对一切 $\mu\in\mathcal M$ 成立。则：

1. **30 §5 引理 5.1 空真**：其假设是「$\nu\in\mathcal M,\nu>2a_1$」，而 $\mathcal M$ 中已无 $>2a_1$ 的元素，故该引理（及其被质疑的第 4 步）无需成立即被使用。
2. **30 §5 引理 5.2 平凡**：$p\le\mu\le2a_1$。
3. **FME 立即成立**：由 引理 2.2（每个 $\mu$ 无平方因子）与 $p\le2a_1$（第 2 点）得
$$\mathcal M\subseteq\{k\ge2:\ k\ \text{无平方因子},\ \operatorname{supp}(k)\subseteq\{p:p\le2a_1\}\},\quad\text{故}\ \mathcal M\ \text{有限}.$$
4. **TCL 常数 $=2a_1^2$**：对 $\mu\in\mathcal M$ 取 $p\in\operatorname{supp}(\mu)$、$j:=\min\{s\ge0:\mu p^s\ge a_1\}$、$k:=\mu p^j$；则 $k\in A_\infty$（(M)）、$\operatorname{supp}(k)=\operatorname{supp}(\mu)$、$k\ge a_1$，由 (P5) $k=a_t$ 是项、$D_t=\operatorname{supp}(\mu)$，且 $t\le k-a_1+1$。若 $j\ge1$ 则 $k<a_1p\le2a_1^2$（$p\le2a_1$）；若 $j=0$ 则 $k=\mu\le2a_1$ 且 $t\le a_1+1<2a_1^2$。故一切实现项指标 $<2a_1^2$，TCL 取 $N=2a_1^2$（接口见 `13-mu-bound.md` §6）。

反之若只知「$\exists p\mid\mu:\mu/p<a_1$」（比 $\mu\le2a_1$ 弱），则 4. 的 $j\ge1$ 支照样给 $\mu<a_1p\le2a_1^2$，$j=0$ 支给 $t\le\mu-a_1+1\le2a_1^2$：TCL 常数仍成立（这条已在 `13-mu-bound.md` 写下）。

**结论**：只要证 $\mu\le2a_1$（∀μ），30-final-proof 的书面链**不需要任何下降引理**即可闭环；这就是本任务与「引理 5.1 第 4 步」是同一件事的原因。

---

## 3. 残余缺口的最窄形式【缺口】

把「用 引理 1.4 迭代」写清楚，缺口就只剩一个极窄的情形。

**迭代**：固定素数 $p$。设 $\nu_0:=\nu_p$。只要 $\nu_r>a_1p$，由（引理 1.4 证明中使用的）同一推理取 $\nu_{r+1}\in\mathcal M$ 使 $p\mid\nu_{r+1}$、$\nu_{r+1}<\nu_r/p$。序列严格递减，有限步 $k$ 停机，停机时
$$p\mid\nu_k,\qquad \nu_k\le a_1p .$$
注意停机时**没有**给出 $p\le2a_1$：只能得 $p\le\nu_k\le a_1p$（平凡）。

**最窄残余命题 R**：
$$\boxed{\ \exists\,\nu\in\mathcal M,\ \exists\,\text{素数}\ p\mid\nu:\quad p>2a_1\ \text{且}\ 2a_1<\nu\le a_1p.\ }$$
等价改写（由 $\nu\le a_1p$、$p\mid\nu$、$\nu/p\notin A_\infty$）：**$\exists$ 素数 $p>2a_1$、$\exists t\le a_1$ 使 $pt\in\mathcal M$ 且 $t\notin A_\infty$、$pt>2a_1$。**

【已证明】R 的反驳 $\Rightarrow$ 30 §5 引理 5.2（$\forall\mu\in\mathcal M,\ \forall p\mid\mu:\ p\le2a_1$）：
给定 $p\mid\mu$，取 $\nu:=\nu_p\le\mu$ 与上述迭代终端 $\nu_k$。若 $\nu_k\le2a_1$ 则 $p\le\nu_k\le2a_1$ ✔；若 $\nu_k>2a_1$，则因 $\nu_k\le a_1p$ 与 $p\mid\nu_k$，若再有 $p>2a_1$ 就落入 R；故 R 被反驳时必有 $p\le2a_1$ ✔。
于是 R 的反驳 $\Rightarrow$ 引理 5.2 $\Rightarrow$ FME（30 §6 定理 6.1）$\Rightarrow$ 原题（30 §7），且由 §2 得 TCL 常数 $2a_1^2$。

【已证明】R 的**局部后果**（可用于进一步压缩）：设 $\nu,p$ 如 R，记 $t:=\nu/p\le a_1$。则
* $pt=\nu\in A_\infty$ 而 $t\notin A_\infty$（$t$ 是 $\nu$ 的真因子、$\ge2$），且 $\nu>2a_1$、$p>2a_1$；$t$ 被某一步杀掉，其杀手 $i=\mathrm{kill}(t)$ 满足 $D_i\cap\operatorname{supp}(t)=\varnothing$；
* $p>2a_1\ge a_1$ 蕴含 $p\notin D_1$（否则 $p\mid a_1\Rightarrow p\le a_1$）；而 $\nu\in A_\infty$ 使 $\operatorname{supp}(\nu)$ 横截，故 $D_1\cap\operatorname{supp}(\nu)\ne\varnothing$，且该交点在 $\operatorname{supp}(\nu)\setminus\{p\}=\operatorname{supp}(t)$ 中、$\le a_1$：即 $t>1$ 且 $\operatorname{supp}(t)\cap D_1\ne\varnothing$；
* 由引理 1.4 与 $\nu\in E_p$ 得 $\nu_p\le a_1p$ 且 $\nu_p\le\nu$：**R 的解必是 $E_p$ 中不超过 $a_1p$ 的元素**（即 R 只涉及 $E_p$ 的"最小段"）。

【缺口】R 的反驳（或等价的 $\mu\le2a_1$）。已知：R 与「$s\le3$」「$S\subseteq D_1$」「$|B|\le1$」等情形的已证排除（见 `13-mu-bound.md` §4–§5）**均相容**，即这些局部论证不自动反驳 R；需要新的整体性输入（可能的方向：把引理 1.2 的"倍数格点"与 R 中 $t\notin A_\infty$ 的杀手结构相撞，或对 $t\le a_1$ 用归纳）。

---

## 4. 数值（大规模反例搜索）

**方法**：把序列生成到首个 $a_N>B$（$B=\text{mult}\cdot a_1$），增量维护 $\min A_n$（survivors ∪ 被杀者的孩子再极小化）。**精确性【已证明】**：此时 $\min A_N\cap[2,B]=\mathcal M\cap[2,B]$（$\subseteq$：$m\in\min A_N,m\le B$ 若 $\notin A_\infty$ 则在步 $j$ 被杀而 $a_j<m\le B<a_N$，与 $m\in A_N\subseteq A_j$ 矛盾；$\supseteq$：$\mu\in\mathcal M,\mu\le B$ 若在 $A_N$ 中不极小，则被某 $m\in\min A_N$ 真整除，而（由前一句）$m\in\mathcal M$，矛盾）。故窗口内数据精确，且**不依赖位置引理**。

脚本与复跑命令（`logs/`）：
```
python logs/d17_scan.py 2 3000 3             # 主扫描（(a)(b)(c)(d) 四项统计），B=3a1
python logs/d17_scan.py 3000 20000 2.5       # 宽范围全值（B=2.5a1，足以发现任何 mu in (2a1,2.5a1]）
python logs/d17_scan.py 10000 100000 3 --step=1000     # 抽稀（B=3a1）
python logs/d17_scan.py 20000 200000 2.5 --step=2000   # 更远抽稀
python logs/d17_scan.py 2 800 10 --stab      # B=3a1,6a1,10a1 截断稳定性
python logs/d17_scan.py 2 300 6              # 与 Lead 的 claimB_scan.py 交叉校验
```

**结果**（`cases` 为窗口内极小元个数；所有 B 均 $>2a_1$，故窗口内的 μ 全部可见）

| 检验项 | 范围 / B | 结果 |
|---|---|---|
| (d) 是否存在 $\mu>2a_1$ | $a_1\le3000$，B=3a₁ | **0 例**；$\max\mu/(2a_1)=0.724138$（$a_1=899=29\cdot31$，$\mu=1302=2\cdot3\cdot7\cdot31=31\cdot42$） |
| (d) 同 | $a_1\le2000$，B=10a₁（独立复算） | 0 例；同一 $\max$ |
| (a) $\max\mu/(a_1p)$（即 (CS)） | $a_1\le3000$，B=3a₁ | $0.724138$，argmax 同上（$p=2$，即 (CS) 的极值点与 (T1) 的极值点重合） |
| (b) (CS) 反例 $\exists p\mid\mu:\mu/p>a_1$ | $a_1\le3000$ | **0 例**（与 Lead 的 $a_1\le1200$ 独立结果相容） |
| (c) $\max p/a_1$（$p\mid\mu$；引理 5.2 的数值形式） | $a_1\le3000$ | $1.000000$，唯一达到者 $a_1=2,\mu=2,p=2$；（样本中恒有 $p\le a_1$） |
| (e) $B\in\{3a_1,6a_1,10a_1\}$ 三档一致性 | $a_1\le800$ | **0 处不一致** |
| 与 Lead 的 `claimB_scan.py` 独立实现交叉校验 | $a_1\le300$ | 完全一致（$\max\mu/(2a_1)=0.636364$，$a_1=187,\mu=238$，0 例 $\mu>2a_1$） |
| 宽范围 / 远范围（两个后台作业） | $[3000,2\cdot10^4]$ 全值（B=2.2a₁）；$[2\cdot10^4,2\cdot10^5]$ step $10^3$（B=2.2a₁） | 启动后未发现反例输出；公式 `python logs/d17_scan.py 3000 20000 2.2` 与 `python logs/d17_scan.py 20000 200000 2.2 --step=1000`；完成时会打印 (a)(b)(c)(d) 四项。注意 $B=2.2a_1$ 只保证发现 $\mu\in(2a_1,2.2a_1]$ 的反例（观测 $\max\mu/(2a_1)=0.724$，故足够） |

**与 R 的关系**：R 要求存在 $\nu\le a_1p$ 且 $\nu>2a_1$、$p>2a_1$。数据中 $\max p/a_1=1.0$、$\max\nu/(2a_1)=0.724$，即样本里 $p\le a_1$（远比 R 需要的 $p\le2a_1$ 强）且 $\nu<1.45a_1$。若 R 存在，最可能出现在 $a_1$ 更大、且 $\operatorname{rad}(a_1)$ 小（$a_1$ 有高次幂）的 $a_1$ 处；本文扫描（含抽稀到 $2\cdot10^5$）未发现。

---

## 5. 已证 / 缺口清单

【已证明】
1. 引理 1.1（$\mathcal M\iff$ 极小横截集）、引理 1.2（$kR\in A_\infty$、间隔 $\le R$）、引理 1.3（私有指标 descent-free）、引理 1.4（$\nu_p/p\le a_1$，即 $\nu_p\le a_1p$；$p\le a_1$ 时才有 $\nu_p\le a_1^2$）。
2. 引理 1.4 的证明方式是**修假设而非修推理**：30 §5 引理 5.1 的第 4 步在假设 $\nu>a_1p$ 下逐字正确。
3. §2：$\mu\le2a_1\Rightarrow$(引理 5.1 空真 + 引理 5.2 平凡 + FME + TCL 常数 $2a_1^2$)；以及「$\exists p:\mu/p<a_1$ 也够 TCL 常数」。
4. §3：R 的反驳 $\Rightarrow$ 引理 5.2 $\Rightarrow$ FME $\Rightarrow$ 原题；R 的等价改写与局部后果。
5. §4：精确性论证 + 大规模数值（$a_1\le3000$ 全值 0 反例；$B$ 三档截断稳定；与独立实现交叉校验）。
6. §6：(L) 线索的独立复核（$a_1\le2000$：0 反例，最小余量 $r_{\min}=5.000000$；等价改写已核对）与 $Q$ 结构统计（$c_{01}=0$；$c_{10}=70$ 说明"$\Leftrightarrow$"反向不成立）。
7. §7：(CS) 的独立验证与部分证明——充分性（(CS) ⟹ FME ⟹ 原题）【已证明】；情形 $|S|\le1$、$\mu\le2a_1$【已证明】；$H$ 与 (CS) 不相容【已证明】；$|S|=2$ 的反例归约到 $p<a_1<q$【已证明】；$a_1\le3000$ 数值 0 反例。
8. §8（task-16 + 后续升级）：(CS) 失败的一般结构 $P^*\sqcup Q^*$、$T$-构造与主不等式 $a_1^k(\prod_{P^*}r)^2<\mu^k$、$P^*=S$ 时 $a_1^s<\mu^{s-2}$（⟹ $s=2$ 时 (CS) 成立）、$A$-侧下界 $a_{i_r}\ge2r$、$A'$-侧替代素数 $\rho_s$【均已证明】；缺口收缩为 (UB)「$a_{i_r}<Ca_1$，残余仅 $A'\ne\varnothing\wedge2\mid\mu/r$」；**关键【已证明】常数阈值：$Q^*\ne\varnothing$ 支只需任意常数 $C$（$\mu<Ca_1^2/2$），$H$ 支 $s=2$ 需 $C\ge2$、$s=3$ 需 $C<4$（与 $a_1$ 无关）⟹ 残余只剩 $H\wedge s\ge4$**。
9. §8.4：迭代替换的终止性（最小失效下标严格递增）【已证明】+ 幅度实测（步数 $\le3$、$\prod_Tp/a_1\le44.2$、396/620 需 boost）；§8.5：$H\wedge s\ge4$ 的判据 $(\star)$ 与其无条件覆盖的唯一组合 $b=1,s=4,C=2$【已证明】；口径修正 $Q_p=\varnothing\Rightarrow p\mid a_1$（反向不成立）。

【缺口】
6. R 的反驳（等价地 $\mu\le2a_1$ 或 30 §5 引理 5.2 的直接证明）。最窄形式见 §3 方框。

**残余 ⟹ FME ⟹ 原题**：见 §3 末（已逐句写出），无需任何其他未证陈述。

---

## 6. (L) 线索的独立复核（Lead 指定；本文独立实现，不用 `logs/lead_*.py`）

**被检验命题 (L)**（Lead 的提法，等价改写由本文核对）：
> 对每个满足 $E_p\ne\varnothing$ 的素数 $p$，令 $\sigma:=\nu_p=\min E_p$、$\tau:=\sigma/p$、$Q:=\{q\ \text{素}:q\mid\tau,\ q\mid a_1\}$。若 $Q\ne\varnothing$，则 (L) 断言 $\exists q\in Q:\ \sigma\le a_1q$。

**等价性核对【已证明（恒等式）】** $\sigma\le a_1q\iff p\tau\le a_1q\iff p\,(\tau/q)\le a_1$：与 Lead 给出的改写一致（只需 $q\mid\tau$，即 $q\in Q$）。故检验量取
$$r(a_1,p):=\min_{q\in Q}\frac{a_1q}{\sigma}\qquad(r\ge1\iff\text{(L) 对该实例成立}).$$

**脚本与复跑**：`python logs/d17_Lcheck.py 2000 6`（本文自有实现：先精确算窗口内 $\mathcal M$（B=6a₁，见 §4 精确性论证），再对每个 $p\mid\mu$ 取 $\nu_p=\min\{\mu\in\mathcal M:p\mid\mu\}$；$\tau=\nu_p/p$、$Q$ 如上）。$P\mid\mu\Rightarrow\nu_p\le\mu\le B$，故窗口内 $\nu_p$ 精确。

**结果（$a_1\le2000$，全部 $E_p\ne\varnothing$ 的 $(a_1,p)$）**

| 量 | 值 |
|---|---|
| 实例总数 $(a_1,p)$ | 2528 |
| 其中 $|Q|=\varnothing$ | 2173 |
| —— 其中 $p\nmid a_1$ 的（应为 0，即何 $|Q|=\varnothing$ 必 $p\mid a_1$） | **0** ✔（与 Lead 的预期一致；这些实例已由 prover-descent 的 16.16(a) 类论证覆盖） |
| 其中 $Q\ne\varnothing$（(L) 真正触及的实例） | 355 |
| **最紧比值 $\min_{a_1,p} r(a_1,p)$** | $\mathbf{5.000000}$（$a_1=35$，$p=7$，$\sigma=35$，$\tau=5$，$q=5$）——与 Lead 在 $a_1\le400$ 上独立得到的最小值 5.000 完全一致 ✔ |
| (L) 反例（$r<1$） | **0 例** |

**判读**：在 $a_1\le2000$ 上 (L) 无反例且最小余量 5 倍（即 $\sigma\le a_1q/5$ 的实例存在，远未贴近边界 $r=1$）。因此
$$\text{(L)}\ \Longrightarrow\ p\cdot\frac{\tau}{q}\le a_1\ \Longrightarrow\ \nu_p=p\tau\le a_1q\cdot\frac{p}{p}\cdot q\ \ \text{（得 $\nu_p\le a_1 q$，其中 $q\mid \tau$）},$$
配合 16.16(a) 覆盖的 $|Q|=\varnothing$（即 $p\mid a_1\Rightarrow p\le a_1$）情形，即可给出 $p\le a_1$ 或 $p\le2a_1$ 型结论——这正是 prover-descent 的 task-10 路线；本文的职责是给出**独立、可复跑、零反例**的数值支撑（含最小余量定位）。

**注**：本文 §4 的 (CS) 扫描（$\max\mu/(a_1p)=0.724138$，0 反例，$a_1\le3000$）与 (L) 扫描（0 反例，$a_1\le2000$，最小余量 5）是两条独立证据；前者是 $\mu$ 层面的，后者是 $E_p$ 层面的。

**附：(L) 规模与 $Q$ 结构的大范围统计（脚本 `python logs/d17_bpp.py 3000 3`，$a_1\le3000$，3824 个 $(a_1,p)$ 实例）**

| 量 | 值 |
|---|---|
| $Q=\varnothing$ 且 $p\mid a_1$（$c_{00}$） | 3271 |
| $Q=\varnothing$ 且 $p\nmid a_1$（$c_{01}$） | **0** ✔（故 $Q=\varnothing\Rightarrow p\mid a_1$ 成立） |
| $Q\ne\varnothing$ 且 $p\mid a_1$（$c_{10}$） | **70** ⚠（故"$\Leftrightarrow$"的反向不成立：$p\mid a_1$ 时 $Q$ 仍可非空） |
| $Q\ne\varnothing$ 且 $p\nmid a_1$（$c_{11}$） | 483 |
| $\max p/a_1$（全部实例） | $1.000000$（唯一达到者 $a_1=2,p=2$）；$\#\{p>a_1\}=0$，$\#\{p>2a_1\}=0$ |
| $\max p/a_1$ 限制在 $Q\ne\varnothing$ | $0.200000$（$a_1=35,p=7,\sigma=35$）——与 Lead 的"硬情形 $p/a_1\le0.2$"一致 |
| $\min_{Q\ne\varnothing}a_1q/\sigma$（(L) 余量） | $2.962733$（$a_1=2385,p=23,\sigma=2415,q=3$）；随范围扩大而**下降**（$a_1\le400$ 时 5.000 → $a_1\le3000$ 时 2.96），故 (L) 非平凡 |
| "硬情形"形状计数（$a_1=pq,\ \sigma=a_1,\ \tau=q$） | 19（例：$(35,7)$、$(65,13)$、$(95,19)$、$(611,47)$、$(667,23)$、$(899,31)$） |

**判读（(b'') 与 (b) 的独立数值）**：$\#\{\nu_p>2a_1\}=0$（$a_1\le3000$），$\max\nu_p/(2a_1)=0.617647$（$a_1=187,p=7,\nu_p=231=3\cdot7\cdot11$）；$\#\{p>a_1\}=0$，$\max p/a_1=1.0$（仅 $a_1=2$）。故 Lead 的 $(b'')$（$\nu_p\le2a_1$）与 $(b)$（$p\le a_1$）在 $a_1\le3000$ 上均无反例。

---

## 7. (CS) 的独立验证与（部分）证明

**目标 (CS)**：$\forall\mu\in\mathcal M,\ \forall p\mid\mu:\ \mu/p\le a_1$。等价形式【恒等】：$\mu\le a_1\min\operatorname{supp}(\mu)$。

### 7.1 充分性【已证明】

设 (CS) 成立。因 $\operatorname{supp}(\mu)$ 横截（$\mu\in A_\infty$）且 $\varnothing\ne\operatorname{supp}(\mu)\cap D_1$，有 $\min\operatorname{supp}(\mu)\le\max D_1\le a_1$，故
$$\mu\le a_1\min\operatorname{supp}(\mu)\le a_1\cdot\max D_1\le a_1^2 .$$
于是 $\mathcal M\subseteq[2,a_1^2]$ 有限，即 **FME**，从而原题成立（先由 FME 得 $L:=\operatorname{lcm}\mathcal M$，再按 30 §7 的计数论证得 $a_{n+T}=a_n+L$；若经 TCL 路线则还需实现项指标 $<2a_1^2$，而 (CS) 给出 $\mu\le a_1\min\operatorname{supp}\mu\le a_1^2<2a_1^2$，结合 `13-mu-bound.md` §6 定理 6.1 的实现构造即可取 $N=2a_1^2$）。**故 (CS) 单独即可闭环。**

### 7.2 已证情形（逐步补全）

* **$|S|=1$**（$S=\operatorname{supp}\mu$，即 $\mu$ 为素数）：$\mu/p=1\le a_1$。✔【已证明】
* **$\mu\le2a_1$**：$\min\operatorname{supp}\mu\ge2$，故 $\mu\le2a_1\le a_1\cdot\min\operatorname{supp}\mu$。✔【已证明】（特别地，`13-mu-bound.md` 已排除 H 的那些情形——$|S|\le3$、$S\subseteq D_1$、$|B|=1$——只要其结论形式是 $\mu\le2a_1$ 或 $\mu<a_1\min\operatorname{supp}$，就已自动满足 (CS)；但注意 13 号的那些情形给的是「$\exists p:\mu/p<a_1$」，不自动等于 (CS)，见下。）
* **$H$ 与 (CS) 不相容【已证明】**：$H:=\forall p:\mu/p\ge a_1$。若 $H$ 与 (CS) 同时成立则 $\forall p:\mu/p=a_1$；但 13 号引理 3.2 证明 $H$ 时 $\mu/p>a_1$（否则位置引理给 $a_i<\mu/p=a_1\le a_i$，矛盾），矛盾。故每个 $\mu$ 至少使 $H$、$\exists$ 一侧失效；**证 (CS) 的关键是排除「$\exists p:\mu/p>a_1$」**。
* **$|S|=2$ 的归约【已证明】**：设 $S=\{p,q\}$、$p<q$。此时 (CS) 等价于 $q\le a_1$（唯一的约束是 $\mu/p=q\le a_1$；$\mu/q=p<q$）。若 $q>a_1$（即 (CS) 失效），则
  1. $q\notin D_1$（否则 $q\mid a_1\Rightarrow q\le a_1$），故 $S\cap D_1=\{p\}$，于是 $p\mid a_1$、$p\le a_1$；
  2. 取 $q$ 的私有指标 $i_q$（引理 1.3）：$D_{i_q}\cap S=\{q\}$，又 $D_{i_q}\cap D_1\ne\varnothing$；该交点 $\notin S$（否则 $=q\Rightarrow q\mid a_1$），故含于 $D_1\setminus S$，于是 $a_{i_q}\ge q\rho'\ge2q>2a_1$；
  3. 若再有 $p\ge a_1$，则位置引理（用于 $\mu/q=p$）给 $a_{i_q}<p\le a_1<2a_1\le a_{i_q}$，矛盾。
  ⟹ **(CS) 的反例若取 $|S|=2$，必呈 $p<a_1<q$、$p\mid a_1$、$\mu=pq\in\mathcal M$ 的形状。**
  （数值上（§7.3）这种形状在 $a_1\le3000$ 内出现 19 例，如 $a_1=35,\mu=35$：$p=5<35<q=7$ 但 $\mu=35=a_1\le a_1p$ ✔；真正"硬情形"的 $q$ 都没有超过 $a_1$。）

### 7.3 数值验证【数据精确，见 §4 的精确性论证】

| 检验项 | 范围 / B | 结果 |
|---|---|---|
| (CS) 反例 $\exists\mu,p:\mu/p>a_1$ | $a_1\le3000$，B=3a₁ | **0 例**（覆盖 Lead 的 $a_1\le1200$） |
| $\max\mu/(a_1p)$（(CS) 的最紧值） | $a_1\le3000$ | $0.724138$，argmax $a_1=899,\mu=1302=2\cdot3\cdot7\cdot31,p=2$（即 $\mu/p=651<899$） |
| 同上，$B=10a_1$ 独立复算 | $a_1\le2000$ | 同一 $\max$，0 反例 |
| 同上，$B\in\{3a_1,6a_1,10a_1\}$ 三档 | $a_1\le800$ | 0 处不一致 |
| $\#\{\mu/p=a_1\}$（边界贴合例） | $a_1\le3000$ | 0 例（由 13 号引理 3.2 的论证可推断 $\mu/p\ne a_1$；此处数据一致） |
| 反例的"形状" | - | 无 |
| **错误加强版对照** $\mu/p\le\operatorname{rad}(a_1)$ | $a_1\le1500$ | **假**（$a_1=375,\mu=399,p=3$：$133>\operatorname{rad}(a_1)=15$；$a_1=175,\mu=195$ 同） |

**结论口径**：(CS) 在 $a_1\le3000$ 上零反例、最紧余量 $1/0.724=1.38$；已证其在 $|S|\le1$、$\mu\le2a_1$ 时成立，并把 $|S|=2$ 的反例归约到极窄形状 $p<a_1<q$。【缺口】一般 $|S|\ge3$ 的 (CS)（建议下一步两条并行：prover-descent 的 $R$/$\nu_p$ 路线，或本文 §3 的极小横截集 + 引理 1.2 倍数格点路线）。

---

## 8. 把 $|S|=2$ 的相撞推广到 $|S|\ge3$（task-16）

设 $(CS)$ 失败：$\exists\mu\in\mathcal M,\ p\in S:=\operatorname{supp}(\mu)$，$\mu/p>a_1$。

### 8.1 反例的一般结构【已证明】

* **(a) 失败点可取 $p=p_{\min}:=\min S$**：因 $p_{\min}\le p\Rightarrow\mu/p_{\min}\ge\mu/p>a_1$。
* **(b) 单调分层**：$r\mapsto\mu/r$ 递减，故
$$P^*:=\{r\in S:\mu/r>a_1\}\ \text{是}\ S\ \text{的初始段},\qquad Q^*:=\{r\in S:\mu/r<a_1\}\ \text{是其补},\qquad P^*\ne\varnothing;$$
且 $\mu/r=a_1$ 不可能（若 $\mu/r\ge a_1$ 则位置引理给 $a_{i_r}<\mu/r=a_1\le a_{i_r}$，矛盾；这正是 13 号引理 3.2 的论证）。记 $k:=|P^*|$。
* **(c) $H$ 在 $Q^*=\varnothing$ 时成立**（$H=\forall r:\mu/r\ge a_1$），反之 $Q^*\ne\varnothing$ 即 $\exists q:\mu/q<a_1$。
* **(d) 每个 $r\in P^*$ 都有"上界引理"可用**：$i_r:=\mathrm{kill}(\mu/r)$ 满足 $D_{i_r}\cap S=\{r\}$、$r\mid a_{i_r}$、$\gcd(a_{i_r},\mu/r)=1$，且因 $\mu/r>a_1$ 有
$$a_{i_r}<\mu/r .$$
* **(e) $T$-构造（仅在 $P^*$ 上）**：令 $T_r:=a_{i_r}\cdot r$。则 $T_r\in A_\infty$（(M)）、$\operatorname{supp}(T_r)=D_{i_r}$、$\operatorname{supp}(T_r)\cap S=\{r\}$、$T_r\ge a_1r$、$T_r<\mu$，故 $T_r$ 是**项**；$r\ne r'\Rightarrow T_r\ne T_{r'}$ 且它们共享一个 $\notin S$ 的素数。
* **(f) 主不等式**：由 (e) 的 $\prod_{r\in P^*}T_r<\prod_{r\in P^*}\mu/r=\mu^k/\prod_{P^*}r$ 与 $\prod_{r\in P^*}T_r\ge a_1^k\prod_{P^*}r$，
$$\boxed{\ a_1^k\Bigl(\prod_{r\in P^*}r\Bigr)^{2}<\mu^{k}\ }\qquad(k=|P^*|\ge1),\qquad\text{特别}\ \mu>a_1\bigl(\min P^*\bigr)^2\ (\text{取 }k=1).$$
* **(g) 若 $P^*=S$（即 $Q^*=\varnothing=H$）**：$a_1^s\mu^2<\mu^s$，即 $a_1^s<\mu^{s-2}$；特别 $s=2$ 时 $a_1^2<\mu^0=1$，矛盾 ⟹ **(CS) 对 $|S|=2$ 在 $Q^*=\varnothing$ 时成立**【已证明】（这是 13 号引理 3.4 的推广）。
* **(h) 下界（$A$ 侧素数）**：由 13 号引理 1.1，反例必 $S\ne D_1$，故 $D_1\setminus S\ne\varnothing$；于是对每个 $r\in S\setminus D_1$ 有 $\rho_r\in D_1\setminus S$ 使 $\rho_r\mid a_{i_r}$，故 $a_{i_r}\ge r\rho_r\ge2r$。【已证明】

### 8.2 已证推论

* **(i)** 由 (f) 取 $k=1$：$\mu>a_1(\min P^*)^2\ge4a_1$。
* **(ii)** 若存在 $q\in Q^*\setminus D_1$：由 (h) $a_{i_q}\ge2q\ge4$；**注意 $q\in Q^*$ 时位置引理对 $\mu/q$ 不可用**（$\mu/q<a_1$），这正是缺口所在。若再加上作 $q>a_1$（$\Leftarrow\mu>a_1^2$，由 (i) 当 $\min P^*\ge a_1$ 时成立），则 $a_{i_q}$ 的下界 $2q$ 与 (f) 的 $\mu>a_1p_{\min}^2$ 一并给出
$$\mu>2q^2,\qquad q>\mu/a_1\ \Longrightarrow\ \mu<a_1^2/2 .$$
* **(iii) $|S|=2$ 的完整判定**：此时 $S=\{p_{\min},q\}$。(CS) 失败于 $p_{\min}$ 则 $\mu/p_{\min}=q>a_1$、$\mu/q=p_{\min}<a_1$（(b)），且 $q\notin D_1$（否则 $q\le a_1$）、故 $p_{\min}\in D_1$、$p_{\min}\le a_1$。(h) 给 $a_{i_q}\ge2q>2a_1$；若 $p_{\min}\ge a_1$，位置引理（用于 $\mu/q=p_{\min}$）给 $a_{i_q}<p_{\min}\le a_1<2a_1\le a_{i_q}$，矛盾 ⟹ $p_{\min}<a_1$。【已证明】——与 §7.2 一致（并把"仅剩 $p<a_1<q$"这一形状再确认一次）。

### 8.3 精确缺口（按 Lead/prover-descent 26.x 校准后的最终形式）

> 【缺口，已收缩为一条窄情形】需要一条上界
> $$\text{(UB)}\qquad a_{i_r}<C\,a_1\quad(\text{对所有 }r\mid\mu,\ \mu/r\ge2)$$
> 且**残余只在下述窄情形**（由 prover-descent 引理 25.2、26.3–26.4 与 Lead 的 26.5 覆盖其余）：
> $$A':=\operatorname{supp}(\mu/r)\cap D_1\ne\varnothing\quad\text{且}\quad 2\mid \mu/r .$$
> 已知（prover-descent，已复核）：$A'=\varnothing$ 时 $a_{i_r}<2a_1$（引理 25.2，$W=\operatorname{rad}(a_1)\lceil a_1/\operatorname{rad}(a_1)\rceil$）；$2\nmid\mu/r$ 时 $a_{i_r}<2a_1$（引理 26.3+26.4，$\ell=2$ 的最小 boost）；残余窄情形中 Lead 已能自动得 $a_{i_r}<3a_1$（26.5）。

**接口链（本文负责；全部【已证明】；$C$ 可为任意常数）**：设 (CS) 失败，$q\in Q^*$（$\mu/q<a_1$，由 §8.1(b)(c)）。
* **(α)** 若 $q\in D_1$：$q\le a_1$（$q\mid a_1$）且 $\mu/q<a_1$，故 $\mu<a_1q\le a_1^2$。【已证明】(不需要 (UB))
* **(β)** 若 $q\notin D_1$：由 §8.1(h) $a_{i_q}\ge2q$；由 (UB) $a_{i_q}<Ca_1$ 得 $q<\tfrac{C}{2}a_1$，于是
$$\mu=q\cdot\frac{\mu}{q}<\frac{C}{2}a_1\cdot a_1=\frac{C}{2}a_1^2 .$$
（亦可不用 (h) 只用 $q\le a_{i_q}<Ca_1$ 得 $\mu<Ca_1^2$，如 Lead/prover-descent §20 所述；两者都够。）【已证明】(条件于 (UB))
* **(γ)** 于是只需 (UB) 对**某个固定常数 $C$** 成立，就有
$$\text{(CS) 失败}\ \Longrightarrow\ \mu<\tfrac{C}{2}a_1^2\ \Longrightarrow\ \mathcal M\subseteq[2,\tfrac{C}{2}a_1^2]\ \text{有限}\ \Longrightarrow\ \textbf{FME}\ \Longrightarrow\ \text{原题（30 §7）}.$$
【已证明】(条件于 (UB))
* **(δ) $H$ 支（$Q^*=\varnothing$）的临界常数**：此时 §8.1(g) 给 $2^sa_1^s<\mu^{s-2}$；又由 (h) 与 (UB)，每个 $r\in S\setminus D_1$ 满足 $2r\le a_{i_r}<Ca_1$ 即 $r<\tfrac{C}{2}a_1$，而 $r\in S\cap D_1$ 时 $r\le a_1\le\tfrac{C}{2}a_1\ (C\ge2)$，故
$$\mu<\Bigl(\frac{C}{2}a_1\Bigr)^{s}.$$
两者相容的必要条件是 $\bigl(\tfrac{C}{2}a_1\bigr)^{s(s-2)}>2^sa_1^{s}$，即
$$C^{s(s-2)}\,a_1^{\,s(s-3)}<2^{\,s(s-1)} .$$
 因此：$s=1$ 无矛盾（$2^1a_1<\mu$ 与 $\mu<\tfrac C2a_1$ 相容当 $C>4$）；$s=2$ 给 $C^0a_1^{-2}<2^{2}$ 即 $a_1>\tfrac12$，故 **$s=2$ 时只要 $C\ge2$ 就矛盾**；$s=3$ 给 $C^{3}<2^{6}=64$，即 **$C<4$ 时矛盾**（与 $a_1$ 无关）；$s\ge4$ 给 $C<2^{\frac{s(s-1)}{s(s-2)}}a_1^{-\frac{s(s-3)}{s(s-2)}}$，随 $a_1$ 增大而变严（$s=4$：$C<2\sqrt2/\sqrt{a_1}$，故大 $a_1$ 时失效）。【已证明】
 结论：**(UB) 取 $C<4$ 即可同时解决 $(CS)$ 失败的 $Q^*\ne\varnothing$ 支与 $H$ 支的 $s\le3$**；唯一的残余是 $H$（即所有余积 $\ge a_1$）且 $s\ge4$（对大的 $a_1$），它需要 $|S|$ 与素因子的额外关联（§8.1(f) 已被 $\mu<(Ca_1/2)^s$ 吸收，故需更细的量级输入）。

**结论**：**(UB)（任意固定常数 $C$）是唯一的最后缺口**；$C$ 越小越强（$C=2\Rightarrow\mu<a_1^2$，并可推出"样本中所有素因子 $\le a_1$"）。而 prover-descent 的 25.2+26.3–26.4+Lead 26.5 已在 $A'=\varnothing$ 与 $2\nmid\mu/r$ 时给出 $C<2$、在残余窄情形给出 $C<3$，故整套论证只差把残余窄情形（$A'\ne\varnothing\wedge2\mid\mu/r$）的常数压到 $\le3.9$（其实 $\le3$ 已有，见下）。

### 8.3.1 候选上界的实测筛选

脚本 `python logs/d17_ub.py 1200 3`（对 $\mu/r<a_1,\ \mu/r\ge2$ 的全部 $(a_1,\mu,r)$，$a_1\le1200$，978 例；$i_r=\mathrm{kill}(\mu/r)$）

| 候选 | 反例数 | 说明 |
|---|---|---|
| $a_{i_r}<2a_1$（即 $a_{i_r}\le2a_1$） | **0** ✔ | $\max a_{i_r}/a_1=1.4483$（$a_1=899,\mu=1015,r=7,a_{i_r}=1302$）；与 Lead 在 $a_1\le400$ 的 $\max=4/3$ 一致 |
| $a_{i_r}\le a_1\cdot r$ | **0** ✔ | 见下方【已证明】的特别情形 |
| $a_{i_r}\le a_1$ | 208（Lead 数据） | 假（例 $a_1=15,\mu=6,q=2$：$a_{i_q}=20$） |
| $a_{i_r}\le a_1+r$ | 415 | 假 |
| $a_{i_r}\le a_1+p_{\min}$ | 562 | 假（Lead 提的第二个候选亦假） |
| $a_{i_r}\le a_1+\mu/r$ | 269 | 假 |
| $a_{i_r}\le a_1(\mu/r)/r$ | 361 | 假 |
| $a_{i_r}\le a_1+(\mu/r)^2$ | 12 | 假（近失，12 例） |

**【已证明】特别情形**：若 $r\in S$ 满足 $S\cap D_1=\{r\}$，则 $a_{i_r}\le a_1r$（$a_1r\in A_\infty$ 且 $\gcd(a_1r,\mu/r)=1$，故 $a_1r$ 被杀，位置引理给 $a_{i_r}<a_1r$）。一般 $r$ 时 $(S\setminus\{r\})\cap D_1\ne\varnothing$ 使 $a_1r$ 不再与 $\mu/r$ 互素，这条不能直接推广。

**prover-descent 的 $T_0/W_0$ 路线实测**（脚本 `python logs/d17_Ap.py 1200 3`，978 例）：$W_0=a_1r/\prod_{A'}p\le2a_1$ 需要的 $\prod_{A'}p\ge r/2$ 有 **364** 例失效（多数为 $A'=\varnothing$，由 25.2 另行解决）；$\prod_{A'}p>r$（$W_0<a_1$）有 **530** 例；$T_0$ 非横截有 **425** 例，失效形态与 25.4 完全一致（如 $a_1=15,\mu=15,r=3$，失效项 $s=3,7$）。故该路线应只用于 25.2/26.x 覆盖的子情形，残余仍归 (UB)。

### 8.3.2 $A'$-侧的补充观察（对应 Lead 的"用 $\rho_s$ 做小替代"）

设 $t:=\mu/r$（$\mu\in\mathcal M$，$r\mid\mu$，$r\nmid t$），$A'=\operatorname{supp}(t)\cap D_1$，$T_0=(D_1\setminus A')\cup\{r\}$（$T_0\cap\operatorname{supp}(t)=\varnothing$）。

* **(1)【已证明】任何 $D_s$ 都不含于 $\operatorname{supp}(t)$**：若 $D_s\subseteq\operatorname{supp}(t)$，取 $i:=\mathrm{kill}(t)<\infty$，则 $\operatorname{supp}(a_i)\cap\operatorname{supp}(t)=\varnothing$，故 $\operatorname{supp}(a_i)\cap D_s\subseteq D_s\subseteq\operatorname{supp}(t)$ 给出 $\operatorname{supp}(a_i)\cap D_s=\varnothing$，与"$D_s$ 是横截集"矛盾。
* **(2)【已证明】25.4 的失效项 $s$ 必含 "$t$-外"素数**：由失效条件 $D_s\cap D_1\subseteq A'\subseteq\operatorname{supp}(t)$ 与 $r\nmid a_s$ 得 $D_s\cap S\subseteq\operatorname{supp}(t)$（$D_s$ 横截给出 $D_s\cap S\ne\varnothing$，而 $r\notin D_s$），再由 (1) 得
$$\varnothing\ne D_s\setminus\bigl(D_1\cup\operatorname{supp}(t)\bigr)\ni \rho_s .$$
  即替代素数 $\rho_s$ 既不在 $D_1$、也不在 $\operatorname{supp}(t)$。
* **(3)【已证明】单步替代可行**：$T_1:=T_0\cup\{\rho_s\}$ 仍满足 $T_1\cap\operatorname{supp}(t)=\varnothing$ 且 $T_1\cap D_s\ne\varnothing$；但 $T_1$ 可能对另一个 $D_{s'}$ 失效，需要迭代。
* **【缺口】**给出迭代的**终止性与幅度**：需证明替代过程有限步停止（或直接证明各 $\rho_s$ 的乘积/某个统一次数 $\le K$），从而 $\prod_Tp\le K a_1$。数值上 $A'$-侧从未出现"≥3 次替代"的情形（§8.3.1 的 425 例失效中，绝大多数一次替代即恢复横截）。

**总清单**：若 (UB) 在残余窄情形取 $C<4$（理想 $C\le2$）得证，则由 §8.3 (γ) 与 (δ) 即得 FME ⟹ 原题；若走纯 $T$-路线，则需补 §8.3.2 的迭代终止性与幅度（并注意 $T$-路线的 $a_{i_r}\le Ka_1$ 同时需要 $\prod_Tp\le Ka_1$ 与 $\prod_Tp\ge a_1$ 两侧，后者在 530 例中失效）。

### 8.4 失效项迭代替换的终止性与幅度【已证明的终止 + 实测幅度】

**算法（最小失效下标贪心）**：从 $T:=T_0$ 出发，每次取**最小**的 $s$ 使 $D_s\cap T=\varnothing$，取 $\rho:=\min\bigl(D_s\setminus(D_1\cup\operatorname{supp}(t))\bigr)$，置 $T:=T\cup\{\rho\}$，直到 $T$ 横截。

**终止性【已证明】**：若当前 $T$ 的最小失效下标为 $s$，则所有 $j<s$ 已被 $T$ 命中；置 $T':=T\cup\{\rho\}$ 后（$T\subseteq T'$，命中关系单调）这些 $j$ 仍被命中，而 $D_s$ 现被 $\rho$ 命中，故 $T'$ 的最小失效下标 $>s$。**最小失效下标严格递增，过程必有限步终止。**（注意 $\rho$ 的存在性由 §8.3.2(2) 保证：失效时 $D_s\cap(D_1\setminus A')=\varnothing$ 且 $D_s\not\subseteq\operatorname{supp}(t)$，故 $D_s\setminus(D_1\cup\operatorname{supp}t)\ne\varnothing$。）
**矩阵自检**：$a_1\le800$、620 个 $(\mu,r)$ 实例中，"最小失效下标非严格递增"的违例为 **0**。

**幅度（实测；脚本 `python logs/d17_repair.py 800 3`）**

| 量 | 值 |
|---|---|
| 终止所需步数分布 | $0$ 步 352 例（$T_0$ 已横截）、$1$ 步 212、$2$ 步 53、$3$ 步 **3**（最大 3，$a_1=667,\mu=667,r=23$）|
| $\max\prod_Tp/a_1$ | $44.2$（$a_1=645,\mu=130,r=13$）——注意 $\prod_Tp=\operatorname{rad}(a_1)\cdot r\prod\rho/\prod_{A'}p$ 不必是 $O(a_1)$ |
| $\prod_Tp<a_1$（需 boost 到 $\ge a_1$） | 396/620 |

**结论**：终止性有无条件证明；幅度上"步数 $\le3$（实测）"，但**常数级 $\prod_Tp\le K a_1$ 不成立于一般 $(r,\mu)$**，只在原始目标（残余窄情形）里值得期待——这正是 Lead 把 $H\wedge s\ge4$ 与 boost 统一化交给 prover-descent 的原因。

### 8.5 $H\wedge s\ge4$ 的独立路线（私有项两两相交 + $D_1$ 两侧）

设 $H$ 成立（$\forall r\in S:\mu/r>a_1$）且 (CS) 失败，$s=|S|\ge4$，$b:=|S\setminus D_1|$（$\ge1$，因 $S\ne D_1$）。则：

* 位置引理对一切 $r\in S$ 可用 ⟹ $T_r=a_{i_r}r\in[a_1r,\mu/r)$、$\operatorname{supp}(T_r)\cap S=\{r\}$、任意两 $T_r$ 共享 $\notin S$ 的素数（§8.1(e)）；由 13 号引理 3.4 得
$$2^{s}a_1^{s}<\mu^{s-2}.$$
* 由 §8.1(h) $\forall r\in S\setminus D_1:\ a_{i_r}\ge2r$；再由 (UB) $a_{i_r}<Ca_1$ 得 $r<\tfrac{C}{2}a_1$；而 $r\in S\cap D_1$ 时 $r\le a_1\le\tfrac C2a_1$。故
$$\mu=\Bigl(\prod_{S\cap D_1}r\Bigr)\Bigl(\prod_{S\setminus D_1}r\Bigr)\le\operatorname{rad}(a_1)\Bigl(\frac{C}{2}a_1\Bigr)^{b}\le a_1\Bigl(\frac{C}{2}a_1\Bigr)^{b}.$$
* 两式合并给出**充要式判据**
$$\boxed{\ 2^{\frac{s}{s-2}+b}<C^{b}\,a_1^{\,b+1-\frac{s}{s-2}}\ }\tag{$\star$}$$
（不满足 $(\star)$ 即可排除该 $(a_1,b,s)$ 组合。）特别地：
 - $b=1,\ C=2,\ s=4$：$(\star)$ 左边 $=2^{3}=8$，右边 $=2$，**对一切 $a_1$ 矛盾**；
 - $b=1,\ C=2,\ s=5$：左边 $=2^{8/3}\approx6.35$，右边 $=2a_1^{1/3}$，矛盾当 $a_1>32$；
 - $b=2,\ C=2,\ s=4$：左边 $=16$，右边 $=4a_1$，矛盾当 $a_1<4$。
【已证明】

**【缺口】** 用 $(\star)$ 一致排除 $H\wedge s\ge4$：因指数 $b+1-\frac{s}{s-2}\ge0$（$b\ge1,s\ge4$），$(\star)$ 只给出"$a_1$ 必须足够大"的约束，尚不能对所有 $a_1$ 排除；需要一条与 $s$（或与 $\sum_{r}\log r$）相关的更强上界，$b=1$ 且 $s=4$ 已被无条件排除是唯一完全覆盖的组合。

### 8.4 数值核对与口径修正

* `python logs/d17_kill.py 1500 3`：在 $\mu/r<a_1$ 的 1216 个实例上测 $a_{i_r}r/\mu$，$\max=742.5$（$a_1=1485,\mu=6,r=3$：$\mu/r=2$、$a_{i_r}=1485$）——说明"$a_{i_r}\le C\mu/r$"型的上界不存在，必须用别的量级（如 $a_1$ 或 term 结构）来控制 $q\in Q^*$ 的情形；这从数值上定位了 §8.3 的缺口。
* `python logs/d17_ub.py 1200 3`：候选上界筛选（表见 §8.3）——$a_{i_r}\le2a_1$ 与 $a_{i_r}\le a_1r$ 在 $a_1\le1200$ 上 0 反例，其余候选均被否（$a_{i_r}\le a_1$ 208 例、$\le a_1+r$ 415 例、$\le a_1+p_{\min}$ 562 例）。
* `python logs/d17_bpp.py 3000 3`（≤3000，3824 实例）：$(CS)$ 0 反例；$\#\{\nu_p>2a_1\}=0$；$\max p/a_1=1.0$。
* 因样本全部满足 (CS)，样本中 $P^*=\varnothing$（$\max\mu/(a_1p)=0.724<1$）；§8 的所有分支都是"假设失败"下的推演。
* **口径修正**（Lead 要求）：$Q_p\ne\varnothing$ **不能**推出 $p\nmid a_1$（$a_1\le3000$ 内有 70 例 $Q_p\ne\varnothing\wedge p\mid a_1$），故正确写法是
$$Q_p=\varnothing\ \Longrightarrow\ p\mid a_1\qquad(\text{反向不成立})$$
（$c_{01}=0$ 支持前者；$c_{10}=70$ 反驳后者）。
