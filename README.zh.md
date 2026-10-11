# IMO 2026 第 6 题 —— 一次全自主多智能体攻关，以及它最终给出的证明

> English: [README.md](README.md) · 中文版如下。

**题目（IMO 2026 第 6 题）**：设整数 $a_1>1$，$a_{n+1}$ 定义为"大于 $a_n$ 且与**每一个**前面的项都有公因子的最小整数"。证明：存在正整数 $T,L$ 使 $a_{n+T}=a_n+L$ 对一切 $n\ge1$ 成立。

**结果**：本仓库含一份完整、无条件、自足的证明。

| 文件 | 内容 |
|---|---|
| **[33-complete-proof.md](33-complete-proof.md)** | 简洁完整证明（根号集合偏序 + "大素数"一步 + 剩余类收尾） |
| **[34-own-route-complete.md](34-own-route-complete.md)** | **本项目自己那条路线的完整化**：独立搭出的框架（$A_\infty$、极小元、FME、TCL、格论证），只插入**一步**外来引理；文中有逐项归属表 |
| [31-final.md](31-final.md) | 原路线的自足化归稿（停在一个显式残余上） |
| [30-final-proof.md](30-final-proof.md) | 上述的工作版（含全部勘误与中间尝试） |
| [16-descent-fix.md](16-descent-fix.md)、[17-fme-indep.md](17-fme-indep.md) | 两个由不同子智能体独立搭出的引理库（约 40 节） |
| [23-verification-L.md](23-verification-L.md)、[21-verification-v3.md](21-verification-v3.md)、[20-verification.md](20-verification.md)、[verify.py](verify.py) | 对抗式复核与独立精确整数检验程序 |
| `logs/` | 全部扫描脚本，含针对**引理本身**的机制核验 `verify33.py`、`verify34.py` |
| [32-待办与交接.md](32-待办与交接.md)、[22-pause-state.md](22-pause-state.md) | 运行中的交接备忘 |

> **背景说明**：这题是 IMO 2026 第 6 题（台湾供题），已有两种公开解法。但本项目**起初被要求不联网**，所以下面这套东西是"盲做"出来的，直到最后一刻才去对照文献。本项目自己的路线是独立且明显更重的一条；唯一决定性的一步（下文引理 LP）来自 Evan Chen 的《IMO 2026 Solution Notes》§2.3 与 AoPS 讨论帖，已明确标注为"借入"。

---

## 一、独立发现的部分（原创性所在）

以下全部是在查文献**之前**搭出来的。记号：$D_n=\operatorname{supp}(a_n)$，$A_\infty=\{k\ge2:\operatorname{supp}(k)\cap D_n\ne\varnothing\ \forall n\}$，$\mathcal M$ = $A_\infty$ 中按"整除"极小的元素。

1. **找到了正确的对象。** 序列恰是 $A_\infty\cap[a_1,\infty)$ 的递增枚举；于是整题等价于关于一个集合（对倍数封闭、对乘法封闭）的命题，而贪心规则变成极小性：$a_{n+1}=\min(A_\infty\cap(a_n,\infty))$。这套化归、记号 $\operatorname{kill}(k)=\min\{i:\gcd(k,a_i)=1\}$、以及"横截集（hitting set）"字典都是本项目自造的。
2. **FME 与格论证收尾。** 设 FME 为"$\mathcal M$ 有限"。则 $A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$；取 $L=\operatorname{lcm}\mathcal M$ 得 $x\in A_\infty\iff x+L\in A_\infty$ 且 $L+1\notin A_\infty$，于是计数函数 $k\mapsto|A_\infty\cap(k,k+L]|$ 为常数，序列终成公差 $L$、周期 $T$ 的等差。配合一条 TCL 引理还能给出显式模数。**这与公开解法的收尾不同**（后者用有限支撑族 + 剩余类），且自足。
3. **残余命题 $R$ 的精确化。** $R$："$\exists$ 素 $p$、$\exists\mu\in\mathcal M$，$p\mid\mu$、$p>2a_1$、$2a_1<\mu\le a_1p$"。本项目证得 $R\iff\neg(\text{素因子界})\iff\exists p(E_p\ne\varnothing\wedge p>2a_1)$，即 $R$ **不多不少**就是缺的那条；并证明早期草稿的自然下降引理在 $R$ 情形下**为假**（必须加强假设）——这正是外部评语指出的那处不等式方向错误。这种"残余归一化"是本项目的独立产物。
4. **关于 $R$ 的一整套结构引理**（均已被对抗复核）：位置引理、私有指标引理、修正版下降引理（$\nu>a_1p\Rightarrow\exists\nu'<\nu/p$ 且指定支撑交）、$\min E_p\le a_1p$、$\tau_p\le\min(t,\operatorname{rad}a_1)$、stall 二分、交叉素数计数、$R$ 的刚性钳制等（见 [16-descent-fix.md](16-descent-fix.md)）。
5. **两条让自创路线得以闭合的"桥梁引理"**：(a) $\mu\in\mathcal M\iff\operatorname{supp}(\mu)$ 是 $\subseteq$-极小横截集——把极小元世界接到横截集理论，是外来那一步能被用上的接口；(b) 归约引理：$x\ge a_1$ 是项 $\iff$ 与一切"relevant"（无更早项支撑含于其）项相交。
6. **发现并修复了项目中两处真错误**，并留下对抗复核：[23-verification-L.md](23-verification-L.md) 重推 14 组引理、零反驳，并记录两处修正（下降引理的不等式方向；某"恒等式"引理缺前提 $p\tau_p\ge a_1$）。
7. **机制级数值核验。** 不只验结论，而是用 [logs/verify33.py](logs/verify33.py)、[logs/verify34.py](logs/verify34.py) 对 14 个 $a_1$ 在**真序列**上核验关键引理本身（借入的 LP 与由此得的支撑界，零违例）；其余全部扫描（$R$、$(CS)$、素因子界、$H$、$H_{1/2}$）在 $a_1\le10^4$ 内**零反例**。

## 二、没发现的部分 —— 以及为什么（诚实复盘）

唯一决定性的一步是**引理 LP**：*含素因子 $p>a_1^2$ 的项不可能是根号集合偏序下的极小项——它必有更早的项，其支撑含于自身*（用几何级数 $q^kc$ 一步证出）。这一步来自文献。根因如下：

1. **推理方向反了。** 工具箱里几乎每条结论都是**下界**（$\mu\ge p$、$\mu\ge2p$、交叉素数乘积 $\ge\cdots$），而 FME 需要的是**上界**。于是不断加约束，却没去找"能产生上界"的机制——四十节残余链正是这一点的纪念碑。
2. **把 $a_1$ 钉死了。** 全程没有对 $a_1$ 归纳，也没做"全局极小反例"；而问题本身是自相似的（尾序列满足规则的变体）。
3. **用分情形代替不变量。** 每一轮都产出新的必要条件，残余不断"变形"（$R\to(L)\to$ stall $\to(CS)\to H_{1/2}\to$ 三支）却始终不死——缺少全局想法的典型症状。
4. **残余在数值上不可见。** $H$ 与 $H_{1/2}$ 在 $a_1\le10^4$ 内从不出现，于是"靠实验猜引理"这条常规路子失效：所有扫描都是零反例，几乎不提供信息。
5. **过程：有体量没有靶心。** 8 个子智能体各自产出大量正确但"局部动机"的引理（某个文件到 122 KB、40 节），却始终没有共同的"一页纸目标"，于是工作没有收敛成那条本来存在的短论证。verifier 队友长期不落盘，对抗复核最后由 Lead 自己写。
6. **过度工程偏好。** 优化的是"局部严格"（每条引理无懈可击、每个边界都分情形），而不是"找关键机制"；并且在化归一旦自洽后就把它当成了既定计划（FME + TCL + 显式模数）。

一句话总结：本项目给出的是一条**正确但明显偏重**的路线、若干确实新的辅助结果，而那个决定性想法是在最后联网时才被引入的。

## 三、运行遥测

- 挂钟时间：**约 590 分钟**，全自主（goal 驱动、自动续轮）。
- **8 个子智能体**：`prover-tcl`、`prover-alt`、`prover-fme`、`prover-h`、`prover-x`、`prover-mu`、`prover-descent`、`verifier-num`；共享任务板 20+ 条（含依赖与写作用域）。
- token 消耗：**约 4×10⁸**（Lead + 子智能体合计，近似）。
- 产物：145 个文件、约 2.1 MB（证明、40 节引理库、对抗复核、108 个日志/扫描文件）。

## 四、如何复现数值

```bash
python logs/verify33.py 4000   # 机制核验：刻画 + 支撑界        -> ALL: OK
python logs/verify34.py 3000   # 机制核验：引理 LP + 极小元界   -> ALL: OK
python verify.py               # 小 $a_1$ 的精确整数检验程序
python logs/cofactor_scan.py 2 3000 3   # 残余扫描（零反例）
```

## 五、一页纸的证明思路

取"与每个项都有公因子的整数之集" $A_\infty$，序列即 $A_\infty\cap[a_1,\infty)$ 的枚举。称一项 *relevant*，若不存在更早的项其支撑含于自身；则一项是否为项，只由它与 relevant 项的 gcd 条件决定。若某项含素数 $p>a_1^2$，几何级数 $q^kc$（$q\mid\gcd(a_1,a_n)$，$c=a_n/p$）给出一个更早且支撑被包含的项，于是 relevant 项、从而"要紧的支撑"都落在有限素数集 $\{p\le a_1^2\}$ 内。因此序列恰是那些 $a\ge a_1$、其小素因子集合属于某个固定有限族的整数，只依赖 $a\bmod L$（$L=\prod_{p\le a_1^2}p$）；数出任意长度 $L$ 的窗口内的剩余类个数，即得 $a_{n+T}=a_n+L$。

## 六、归属一句话

借入：根号集合偏序/relevance 归约、"大素数"几何级数一步，以及（短证明中的）剩余类收尾。其余——$A_\infty$/极小元框架、FME + 格论证收尾、残余 $R$ 及其结构引理、极小横截桥梁、relevant 归约、全部复核与数值——均为本项目在运行中独立建立。
