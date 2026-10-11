# 23. 对 `16-descent-fix.md` §10–§15 与 `17-fme-indep.md` §6–§7 的独立复核

> 复核者：**Lead**（verifier-num 被委派 task-13 但迟迟未落盘，故由 Lead 先做一版；其 21 号对 §5 的复核仍然有效）。
> 口径：**通过** = Lead 独立重推无误、前提每处合法；**存疑** = 结论正确但表述/前提需补；**反驳** = 真错。
> 数值均由 Lead 用自己的脚本复跑：`logs/lead_qbound.py`、`logs/lead_Ltight.py`、`logs/lead_tau.py`、`logs/lead_pa1tight.py`、`logs/cofactor_scan.py`；与 prover-mu 的 `logs/d17_*.py`、prover-descent 的 `logs/d18_*.py` 三套实现互相对表。

## 1. 逐条判定

| 条目 | 判定 | 独立复推要点 |
|---|---|---|
| 16.4（$\nu>a_1p$ 版下降） | **通过** | $\nu>a_1p\ge a_1$ ⇒ (P5) $\nu=a_j$、$T=D_j$ 横截；$k=\nu/p>a_1\ge2$、极小性给 $k\notin A_\infty$、位置引理 3.1 前提 $k\ge a_1$ 合法；$\mathcal F=\{\nu''\mid\operatorname{rad}(a_i),\nu''\in A_\infty\}$ 的极小元确在 $\mathcal M$；$\nu'\le a_i<\nu/p$。逐步无跳。 |
| 18.2（$(L)\Rightarrow(b)$） | **通过** | $q\mid t\Rightarrow q\le t\Rightarrow p=\sigma/t\le a_1q/t\le a_1$。 |
| 18.3（$\neg L$ 下的下降） | **存疑→已修** | 原写"$\nu_q\in E_q\Rightarrow\nu_q\le a_1q$"错（16.6 只给 $\min E_q\le a_1q$）；`16` §12.1 已改为"先取首元、再沿 $q$ 迭代 16.4 到 $\le a_1q$"，迭代前提与不变量（$\operatorname{supp}\cap\operatorname{supp}(\sigma)=\{q\}$、$p\nmid\nu_q$、$<\sigma/q$）均成立 ⇒ 修正后**通过**。 |
| 18.4（成功/stall 二分）+ 19.1（stall ⇒ $\mu^\ast=\nu_q$） | **通过** | 二分穷尽（每步问 $\operatorname{rad}(p\mu_k)$ 是否有 $p$-含 $\mathcal M$-因子）；$\mathcal M$-链 $\mu_{k+1}\mid\mu_k$ 严格递减、有限终止。19.1 用"$\operatorname{supp}(\mu^\ast)$ 横截 + $\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$ ⇒ $q\mid\mu^\ast$ ⇒ $\mu^\ast\in E_q$"，再以 $\nu_q=\min E_q$ 与 $\nu_q\in A_\infty$ 排除严格小于 ⇒ 相等 ✔。 |
| 19.3/19.4/19.5/19.6 | **通过** | 19.3 的 stall $\iff$"无 $p$-含 $\mathcal M$-因子"与 18.4 的失败支定义一致；19.5 的 $p$-free 私有指标由"$p\nu_q/r\notin A_\infty$ + 横截"导出；19.6 的 $t_q<\sigma/q^2$ 由 19.1 与 18.3 的界相除得到。 |
| 18.6（密度必要条件） | **通过** | 每个 $<p$ 的项都 $t$-可除（$p$-可除者 $\ge p$）且由 (P1) 与 $D_1$ 相交 ⇒ 被某 $\operatorname{lcm}(q',q'')$ 整除；配 (P6) 的密度与并集计数 $\le p\Sigma+N$ ⇒ $\Sigma\ge\frac{p-a_1}{p\operatorname{rad}(a_1)}-\frac Np$ ✔（仅必要条件，未被当作充分）。 |
| 21.1（$\tau_p\le\operatorname{rad}(a_1)$） | **通过** | $D_1$ 与每个 $D_s$ 相交 ⇒ $\operatorname{rad}(a_1)\in\mathcal R_p$ ⇒ $\tau_p\le\operatorname{rad}(a_1)$；与 $\tau_p\le t$ 合并。 |
| 21.2（$p\tau_p\ge a_1$ 时 $a_r=p\tau_p$） | **通过（前提已显式）** | 16.15 的恒等式 $a_r=x_p^{\min}=p\tau_p$ **需要 $p\tau_p\ge a_1$**（否则 $x_p^{\min}<a_1$ 不是项）；$p>2a_1$ 时自动，$p\le2a_1$ 时由 §13 分支处理。Lead 复核：16.15 的其余论证（$p\tau_p\in A_\infty$、$x_p^{\min}=p\tau_p$）无误。 |
| 21.3（$t=1$ 时 (c) 成立） | **通过** | $t=1\Rightarrow\sigma=p\in A_\infty\Rightarrow p\mid$ 所有项 $\Rightarrow F_p=\varnothing\Rightarrow\tau_p=1\Rightarrow a_r=a_1\le2a_1$。 |
| 22.1–22.4（机器平移到 (CS)） | **通过** | 22.1 逐条照抄 16.12/16.13（$\sigma\mapsto\mu$，$t=\mu/p$）；(CS) 侧 $t>a_1$ 使位置引理**直接可用**，与 R 侧（16.14 构造必失败）互补；22.2 的下降在两分支都成立；22.4 的 19.x 搬用前提已注明。 |
| 17 §6（$(L)\iff p(\tau/q)\le a_1$） | **通过** | 恒等式核对；$r(a_1,p)=\min_q a_1q/\sigma\ge1\iff(L)$。 |
| 17 §7.1（$(CS)\Rightarrow$FME） | **通过** | $\mu\le a_1\min\operatorname{supp}\mu\le a_1\max D_1\le a_1^2$ ⇒ $\mathcal M\subseteq[2,a_1^2]$ 有限 ⇒ FME ⇒ 原题。 |
| 17 §7.2（$|S|\le1$、$\mu\le2a_1$、$H$ 不相容、$|S|=2$ 归约） | **通过（归约≠闭环）** | 四条都成立；$|S|=2$ 的归约用软点正确处理"反例必 $p<a_1<q$"；$\rho'$-机制（$q\notin D_1\Rightarrow a_{i_q}\ge2q$）核对无误。 |

**无反驳项。** 两处曾出错的地方（18.3 的 $\le a_1q$、16.15 的前提）都已被作者显式修正并标注。

## 2. Lead 独立数值（三套实现互表）

| 量 | Lead 值 | 交叉 |
|---|---|---|
| $\max\mu/(2a_1)$（$a_1\le3000$） | $0.724138$（$a_1{=}899,\mu{=}1302$） | 与 prover-mu、`17` §4 一致 |
| $\max\nu_p/(2a_1)$（$a_1\le300$） | $0.617647$（$a_1{=}187,p{=}7$） | 与 `d16_nu.py` 一致 |
| $\max p/a_1$ | $1.000$（唯一 $a_1{=}p{=}2$）；$Q_p\ne\varnothing$ 时 $0.2$ | 与 `d17_bpp.py` 一致 |
| $R$ 实例 / $\mu>2a_1$ 实例 | $0$ / $0$（$a_1\le10^4$，$B=6a_1$，$B$ 三档稳定） | 三套实现一致 |
| $(CS)$ 反例 | $0$（$a_1\le3000$，$B=3a_1$；Lead 另跑 $a_1\le1200$ 与 $[1200,3000]$） | 与 `17` §7.3 一致 |
| $\min_q a_1q/\sigma$（$(L)$ 余量） | $5.000$（$a_1\le400$）→ $2.963$（$a_1\le3000$） | 与 `d17_Lcheck.py` 一致 |
| $|S|=2$ 的 $\max\operatorname{supp}\mu/a_1$ | $1/3$，零例 $>a_1$（$a_1\le600$，133 例） | 与 `d18_S2.py` 一致 |

## 3. 结论与残余口径

- **归属正确的"已证明"**：16.4、18.2、18.4+19.1、19.3–19.6、18.6、21.1–21.3、22.1–22.4、17 §6/§7.1/§7.2。
- **唯一残余（三条充分路线，任一即闭环）**：$(CS)$（只剩 $(\star\star)$/与 $|S|=2$ 窄形状）；$(b'')\Rightarrow(L)\Rightarrow(b)\Rightarrow\neg R$；$(b'')\Rightarrow(c)\Rightarrow\neg R$。
- **须提醒**：所有残余在实测中**从不触发**，故数值对它们只是必要条件；引用时须写明"残余"而非"已证"。
