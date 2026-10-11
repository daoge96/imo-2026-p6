# 22. 暂停状态（2026-10-10 夜）— 明天早上从这里继续

> **【最新】整题已完整闭环**（联网核对标准解法后）：终版证明 = `33-complete-proof.md`；机制验证 = `logs/verify33.py`（零违例）。此题即 IMO 2026 P6，标准解法的"$\prec$-偏序 + 大素数 $>a_1^2$"一步正是我们缺的上界机制。goal 已置为 complete。
> 以下为旧（独立备用）路线的交接记录。

> Lead 写的交接备忘。**任务已全部暂停**：三名在跑的队友（prover-descent、prover-mu、verifier-num）已被 interrupt，共享任务 task-9（prover-mu）、task-10（prover-descent）保持 `in_progress` 归属不变；Lead 无后台作业在跑。
> 恢复方式：对我说一句"继续"即可；下面 §6 有给队友的原话。

---

## 1. 一句话现状

主证明 `30-final-proof.md` **v3** 已按外部评语修好 §5，并经 verifier-num **对抗式独立复核通过（无反驳项）**；**唯一剩余缺口是一条命题 $R$**，且 $R$ 已证明**恰等于**"素因子界"的取反（不是充分条件）。$R$ 在一切已检验实例（$a_1\le10^4$）中从未出现。

$$\underbrace{\text{(P1)–(P6),(K),(M), 引理 2.2,3.1,4.1,5.1,5.2}}_{\text{无条件、已复核}}\Longrightarrow\ \neg R\ \Longrightarrow\ \text{FME}\ \Longrightarrow\ \S7\ \Longrightarrow\ \text{原题}.$$

## 2. 唯一缺口（精确定义与等价形式）

$$R:\quad \exists\ \text{素 }p\ \exists\mu\in\mathcal M:\ p\mid\mu,\quad p>2a_1,\quad 2a_1<\mu\le a_1p .$$
**等价**（均已证，见 `30-final-proof.md` 引理 5.3′/5.3″、`16-descent-fix.md` 命题 16.9）：
$$R\iff\neg(\forall\mu\in\mathcal M\,\forall p\mid\mu:\ p\le2a_1)\iff\exists p:\ E_p\ne\varnothing\wedge p>2a_1\iff\exists p:\ E_p\ne\varnothing\wedge\nu_p>2a_1 .$$
（$E_p:=\{\mu\in\mathcal M:p\mid\mu\}$，$\nu_p:=\min E_p$。）**不需再弱化**：$R$ 就是要证的命题。

## 3. 今天最优先的目标 (L)（已细化；prover-descent 在主攻）

**重要分情形**（Lead 复核 `logs/lead_Ltight.py` 时发现）：$Q:=\{q\ \text{素}:q\mid t,\ q\mid a_1\}$ 可以为空，且**恰好发生在 $p\mid a_1$ 时**（此时 $p\le a_1$ 已由 16.16(a) 证）。故 (L) 只需在 $p\nmid a_1$ 时陈述（此时 16.12(iv) 保证 $Q\ne\varnothing$）：

$$(L')\qquad p\nmid a_1\ \Longrightarrow\ \exists\ \text{素 }q\mid t\ \text{使}\ q\mid a_1\ \text{且}\ \sigma:=\nu_p\le a_1q .$$

**等价改写**：取 $q:=\max Q$，写 $t=qT$、$a_1=qA$（$T,A\ge1$），则 $(L')\iff\sigma\le a_1q\iff p\,T\le a_1$。

**为什么够**：$q\mid t\Rightarrow q\le t$，故 $p=\sigma/t\le a_1q/t\le a_1$ ⟹ 路线 (b) ⟹ $\neg R$ ⟹ 闭环（并顺带给出 $\nu_p\le a_1^2$ 与常数改进）。$q$ 的存在性 = 16.12(iv)。$t=1$ 的退化情形：$p\in A_\infty\Rightarrow p\mid a_1\Rightarrow p\le a_1$，已证。

**数值（Lead 已跑）**：$a_1\le400$ 内全部 $Q\ne\varnothing$ 实例（67 个）成立，最紧比值 $\min_q a_1q/\sigma=5.000$（$a_1{=}35,p{=}7,\sigma{=}35,t{=}5,Q{=}\{5\}$，即 $pT=A=7$ 取等）。$a_1\le2000$ 全扫：`logs/lead_qbound.py`（后台）。

**反证路线（已推出两条可用事实）**：设 $\forall q\in Q:\sigma>a_1q$（$\neg(L')$）。16.4 沿 $q$ 给 $\nu_q\in E_q$、$p\nmid\nu_q$、$\operatorname{supp}(\nu_q)\cap\operatorname{supp}(\sigma)=\{q\}$、$\nu_q<\sigma/q$；又 $\nu_qp\in A_\infty$ 给出 $\sigma\le(\text{含 }p\text{ 的极小因子})\le\nu_qp$，故 $t\le\nu_q<\sigma/q=pt/q\Rightarrow q<p$；再用 5.2 于 $q$ 得 $\nu_q\le a_1q$，于是 $t\le a_1q<\sigma=pt\Rightarrow a_1q/t<p$，即 $p\,T>a_1$。**故 $(L')\iff$ 排除 $p\,T>a_1$。**

脚本：`logs/lead_qbound.py`（(L) 全扫）、`logs/lead_Ltight.py`（最紧实例）。

---

## 4. 第 12 轮结束时的状态与恢复指令（Lead）

**定稿（清洁自足版）：`31-final.md`**；**未完成任务清单与交接：`32-待办与交接.md`**（换机器／换会话后从该文件接续，含三支残余的精确陈述、可用引理、数值脚本与闭环后 v4 的机械步骤）。工作版：`30-final-proof.md`（含全部勘误与中间尝试）。

**当前定稿**：`imo-p6/30-final-proof.md`（v3，含 §5.8 全部充分路线、§10 v4 升级接口、§11 参考文献）。
**复核**：`21-verification-v3.md`（verifier-num 对 §5）+ `23-verification-L.md`（Lead 对 16 §10–§16、17 §6–§8，14 项通过、无反驳）。
**唯一残余**（三条充分路线，任一即闭环；全部零反例、余量 1.4–5 倍）：
1. $(CS)$：$\forall\mu\forall p\mid\mu:\mu/p\le a_1$ ⟹ FME ⟹ 原题。缺口：$(\star\star)$（$a_1<\mu/p\le a_1p$，`16` §14）或 $|S|=2$ 窄形状（$p<a_1<q$、$p\mid a_1$、$\mu=pq$，约束清单见 `16` 注 24.3），或 $|S|\ge3$ 时的"$a_{i_q}$ 非位置引理上界"（`17` §8，证 $a_{i_q}\le2q$ 或 $\le a_1$ 即闭环）。
2. $(b''):\nu_p\le2a_1\Rightarrow(L)\Rightarrow(b)\Rightarrow\neg R$；缺口＝ stall 支（`16` §10–§12）。
3. $(b'')\Rightarrow(c)\Rightarrow\neg R$；缺口＝分支 $\mathcal A$ 的 $p\min(t,\operatorname{rad}a_1)\le2a_1$（`16` §13）。

**恢复指令**：spawn 一个 prover 攻上表任一条；可用素材已全部落在 `16-descent-fix.md`（16.4、16.12–16.16、18.x、19.x、21.x、22.x、23.x、24.1–24.3）与 `17-fme-indep.md`（§1–§8，主不等式 $a_1^k(\prod_{P^\ast}r)^2<\mu^k$）。闭环后按 `30-final-proof.md` §10 的接口升 v4，再交 verifier-num 复核 `23-verification-L.md` 口径。
**任务台账**：task-9/14/15/17/18/19 已完成；task-16 已完成；task-13 由 Lead 代写（verifier-num 未落盘）。

## 3′. 今日第 2 轮的新结果（Lead）

**三个目标在 $p\nmid a_1$ 时完全等价**：(L) ⟺ (b) ⟺ ¬R。
- (L)⟹(b)：命题 18.2；
- (b)⟹(L)：$p\le a_1<2a_1\Rightarrow\neg R_p$，由 16.9 的 $\neg R\iff$素因子界得 $\nu_p\le2a_1$；取 $q\in Q_p$（$\ge2$）得 $\nu_p\le2a_1\le a_1q$。
（已写入 `30-final-proof.md` §5.8 命题 5.8′。）**故唯一待证就是 (b)：$E_p\ne\varnothing\Rightarrow p\le a_1$**（等价 $\nu_p\le2a_1$）。

**勘误（Lead 发现）**：`16` 的 18.3 中"$\nu_q\in E_q\Rightarrow\nu_q\le a_1q$"须补一步——16.6 只给 $\min E_q\le a_1q$；正解是对 $\nu_q$ 继续沿 $q$ 下降（16.4）到 $\le a_1q$（下降保持 $\nu_q<\sigma/q$ 与 $p\nmid\nu_q$），结论不变。已通知 prover-descent 与 verifier-num。

**prover-descent 的第 12 轮成果（§11，已复核）**：19.1（stall ⟹ μ*=ν_q）、19.2（stall 目标 ⟺ $p t_q\le a_1$）、19.3（stall ⟺ ∄μ'∈E_p 整除 pν_q）、19.4（⟺ ν_q≤a_1q/p）、19.5（stall 下存在 $p$-free 私有指标）、19.6（$t_q<\sigma/q^2$，故 $p<q$ 时 stall 自动成立）。数值：$p\nu_q\le a_1q$ 在 85 个样本中仅 1 例失效。

## 3″. 第 4–6 轮（Lead + prover-descent）新增

**无条件新引理（21.1）**：$\operatorname{rad}(a_1)\in\mathcal R_p$（因 $D_1$ 与每个 $D_s$ 相交），故 $\tau_p\le\min(t,\operatorname{rad}(a_1))\le a_1$。
**修正（21.2 前提）**：恒等式 $a_r=x_p^{\min}=p\tau_p$ **需要 $p\tau_p\ge a_1$**（否则 $x_p^{\min}<a_1$ 不是项）；$p\le2a_1$ 时该前提常失效（312 对中 254 对）。故 (c) 分两支：$\mathcal A$（$p\tau_p\ge a_1$，含全部 $p>2a_1$）由 $p\min(t,\operatorname{rad}(a_1))\le2a_1$ 推出；$\mathcal B$ 用 $p\operatorname{rad}(a_1)\in A_\infty$。$t=1$ 时 (c) 已证（$\tau_p=1,a_r=a_1$）。

**新充分路线 (CS)**：$\forall\mu\forall p\mid\mu:\mu/p\le a_1$ ⟹ $\mu\le a_1\min\operatorname{supp}\mu\le a_1^2$ ⟹ FME ⟹ 原题（**绕开 $R$**）。数值：$a_1\le1200$ 零反例，$[1200,3000]$ 扫描中（`logs/cofactor_scan.py`）。

**当前充分目标（任一即闭环）**：$(CS)$；或 $(b'')\Rightarrow(L)\Rightarrow(b)\Rightarrow\neg R$；或 $(b'')\Rightarrow(c)\Rightarrow\neg R$。

## 4. 已具备的全部工具（可直接用，无需重证）

- `30-final-proof.md`：§1–§4 无条件；(P5) 项 $=A_\infty\cap[a_1,\infty)$ 递增枚举；(P6) 项间隔 $\le\operatorname{rad}(a_1)$；引理 2.2（$\mathcal M$、无平方、$A_\infty=\bigcup\mu\mathbb Z$）；引理 3.1（位置引理，**前提 $k\ge a_1$**）；引理 4.1（私有指标）；**引理 5.1′**（$\nu>a_1p$ 版下降，已复核）；**引理 5.2**（$\nu_p\le a_1p$）；$R$ 的等价与结构（§5.7）。
- `16-descent-fix.md`：16.4（自足下降）、16.6、**16.8**（$R\Rightarrow$ v2 引理 5.1 为假，故"改假设"必需）、**16.9**（$R\iff\neg$素因子界）、16.12–16.15（$R$ 的刚性钳制：$2\le t<a_1$、$t$ 及其一切 $\ge2$ 因子 $\notin A_\infty$、$\exists q\mid t,q\mid a_1$、$p\nmid a_1$、$\operatorname{rad}(a_i)\ge\sigma$、$a_i\ge\sigma$、$\sigma\le a_{i-1}$、$a_r=x_p^{\min}=p\tau_p\le\sigma$、$\nu_q$ 存在且 $p\nmid\nu_q$、$\nu_q<\sigma/q$）、16.16 (a)(b)(c)。
- `17-fme-indep.md`：$\mathcal M\iff$ 极小横截集、$kR\in A_\infty$、descent-free 私有指标、$\nu_p\le a_1p$、$R$ 的最窄形式、$a_1\le10^4$ 扫描。
- 数值脚本：`logs/claimB_scan.py`、`cofactor_scan.py`、`top_ratio.py`、`xpmin_scan.py`、`lead_qbound.py`（Lead）；`logs/d16_*.py`（prover-descent）；`logs/d17_scan.py`（prover-mu）；`logs/v21_scan.py`+`verify.py`（verifier-num，独立实现）。
- 关键"陷阱"备忘：$\nu_p\le x_p^{\min}$ 为**假**（$a_1=187,p=3$：$66<102$）；$\mu/p\le\operatorname{rad}(a_1)$ 为**假**；"$\nu_p\le a_1p\le a_1^2$"的第二段**需要** $p\le a_1$（即待证的 (b)）。

## 5. 数值证据台账（全部零反例）

| 事实 | 范围 | 来源 |
|---|---|---|
| 无 $\mu>2a_1$ | $a_1\le3000$ 全扫 + $[2,2000]$ $B=10a_1$ + $a_1\le10^4$（$B=6a_1$） | Lead / prover-mu |
| $\max\mu/(2a_1)=0.7241$（$a_1=899,\mu=1302$） | $a_1\le10^4$ | 三方一致 |
| $R$ 零实例、$\max p/a_1=1$（唯一 $a_1=p=2$） | $a_1\le10^4$；$a_1\le500$ 三方对齐（$E_p$ 非空对 626） | prover-mu / prover-descent / verifier-num |
| $B\in\{3a_1,6a_1,10a_1\}$ 截断稳定 | $a_1\le2500$ | prover-mu / verifier-num |
| $\sigma\le a_1q$（新线索） | $a_1\le300$，48 个 $t\ge2$ 对，0 反例 | `logs/lead_qbound.py` |

## 6. 恢复指令（对我说"继续"后，Lead 按此执行）

1. `send_message → prover-descent`：接 task-10，**主攻 (L)**（$\exists q\mid t:q\mid a_1\wedge\sigma\le a_1q$）；提示：可用 16.13(ii)（$a_i/p\in\mathcal R_p$、$\tau_p\le a_i/p$）、16.15（$a_r=p\tau_p\le\sigma=pt\Rightarrow\tau_p\le t$）、(P6) 间隔 $\le\operatorname{rad}(a_1)$、16.12(iv) 的 $q$；并先跑 `logs/lead_qbound.py` 到 $a_1\le2000$ 确认线索。
2. `send_message → prover-mu`：接 task-9，继续大范围扫描（$a_1\ge2\times10^4$、抽稀 $10^5$），并独立试 (L)/(b)。
3. `send_message → verifier-num`：收尾 20 号文档汇总行；日后 (L) 若证出，复核 (L) 并重跑 v3（去掉 $\neg R$、升级 $\nu_p\le a_1^2$）。
4. **两处措辞修正待办**：`16-descent-fix.md` 16.6 与 `17-fme-indep.md` 1.4 的 "$\nu_p\le a_1p\le a_1^2$" → 改为 "$\nu_p\le a_1p$（$p\le a_1$ 时 $\le a_1^2$）"；16.12(iv) 补一句 $p\nmid a_1$ 的论证（$p\mid a_1\Rightarrow p\le\operatorname{rad}(a_1)\le a_1<2a_1<p$）。v3 内已改好。
5. 若 (L) 被证：改 `30-final-proof.md` 为 v4（删去 $\neg R$ 假设；引理 5.2 升级为 $\nu_p\le a_1^2$；定理 6.1/§7 无条件），再让 verifier-num 复核后交用户。

## 7. 文件清单（本目录）

- 权威定稿：`30-final-proof.md`（**v3**，156+ 行；§5 = 修正版 + $R$；§5.7 = $R$ 的抓手）
- 修法与结构：`16-descent-fix.md`（220 行）、`17-fme-indep.md`（130 行）
- 对抗式复核：`21-verification-v3.md`（结论：§5 有效，无反驳项）
- 历史/常数攻坚：`10/11/12`（三条独立证明链）、`13/14/15`（$H$ 与常数）、`20-verification.md`+`verify.py`（早期数值）
- 题面与归约：`00-problem.md`、`01-reduction.md`、`02-lead-notes.md`
- 外部评语：`D:\OneDrive\Desktop\30号证明评语.md`
- 脚本与日志：`logs/`（含本次全部扫描）
