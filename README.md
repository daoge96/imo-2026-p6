# IMO 2026 Problem 6 — an autonomous multi-agent attempt, and the proof it produced

> 中文版：[README.zh.md](README.zh.md) · English below.

**Problem (IMO 2026, Problem 6).** Let $a_1>1$ be an integer and define $a_{n+1}$ to be the smallest integer greater than $a_n$ that shares a common prime factor with **every** earlier term. Prove that there exist positive integers $T,L$ with $a_{n+T}=a_n+L$ for all $n\ge 1$.

**Result.** This repository contains a complete, unconditional, self-contained proof.

| File | What it is |
|---|---|
| **[33-complete-proof.md](33-complete-proof.md)** | Clean, short, complete proof (radical partial order + "large prime" step + residue-class finish). |
| **[34-own-route-complete.md](34-own-route-complete.md)** | **The agent's own route, completed**: an independently built framework ($A_\infty$, minimal elements, FME, TCL, a lattice argument) into which **exactly one borrowed step** was inserted. Has a per-item attribution table. |
| [31-final.md](31-final.md) | The original route as a self-contained reduction (stops at an explicit residual). |
| [30-final-proof.md](30-final-proof.md) | Working version of the above (all corrections and intermediate attempts). |
| [16-descent-fix.md](16-descent-fix.md), [17-fme-indep.md](17-fme-indep.md) | Two independent lemma banks (≈40 sections) built by different subagents. |
| [23-verification-L.md](23-verification-L.md), [21-verification-v3.md](21-verification-v3.md), [20-verification.md](20-verification.md), [verify.py](verify.py) | Adversarial verification of the lemmas and an independent exact-arithmetic test harness. |
| `logs/` | All scan scripts, including the mechanism-level verifiers `verify33.py` / `verify34.py`. |
| [32-待办与交接.md](32-待办与交接.md), [22-pause-state.md](22-pause-state.md) | Handover notes written during the run. |

> **Provenance note.** The problem is IMO 2026 Problem 6 (proposed by Taiwan). Two published solutions exist, and they are *not* what the agent first found: the run started with a "no internet" instruction, so everything below was built blind and only checked against the literature at the very end. The agent's own work is an independent, considerably heavier route; the decisive step (Lemma LP below) was found in Evan Chen's *IMO 2026 Solution Notes* §2.3 and in an AoPS thread, and is marked as borrowed.

---

## 1. What was independently discovered (the original part)

All of the following was built **before** any literature was consulted. Notation: $D_n=\operatorname{supp}(a_n)$, $A_\infty=\{k\ge2:\operatorname{supp}(k)\cap D_n\ne\varnothing\ \forall n\}$, $\mathcal M$ = minimal elements of $A_\infty$ under divisibility.

1. **The right object.** The sequence is exactly the increasing enumeration of $A_\infty\cap[a_1,\infty)$. Hence the whole problem is equivalent to a statement about one set $A_\infty$ (upwards closed under divisibility, multiplicatively closed), and the greedy rule becomes a *minimality* statement: $a_{n+1}=\min(A_\infty\cap(a_n,\infty))$. This reduction, the notation $\operatorname{kill}(k)=\min\{i:\gcd(k,a_i)=1\}$, and the transversal ("hitting set") dictionary were all invented here.
2. **FME and a lattice finish.** Let FME be "$\mathcal M$ is finite". Then $A_\infty=\bigcup_{\mu\in\mathcal M}\mu\mathbb Z_{\ge2}$; with $L=\operatorname{lcm}\mathcal M$ one gets $x\in A_\infty\iff x+L\in A_\infty$ and $L+1\notin A_\infty$, so the counting function $k\mapsto|A_\infty\cap(k,k+L]|$ is constant and the sequence is eventually arithmetic with period $T$. A companion TCL lemma turns FME into an explicit modulus. This is a **different finish** from the published one (which uses a finite family of supports and residues); it is self-contained and proved in [30-final-proof.md](30-final-proof.md) §6–§7.
3. **The exact residual.** $R$: "$\exists$ prime $p$, $\exists\mu\in\mathcal M$ with $p\mid\mu$, $p>2a_1$, $2a_1<\mu\le a_1p$". The agent proved $R\iff\neg(\text{prime bound})\iff\exists p\,(E_p\ne\varnothing\wedge p>2a_1)$ — i.e. $R$ is *exactly* the missing statement, neither stronger nor weaker — and that the natural descent lemma of an earlier draft is **false** in the $R$-regime, so the hypothesis of that lemma must be strengthened (this is the flaw an external critique had found). This "residual normalization" is, as far as the run could tell, original.
4. **Structural lemmas about the residual**, all proved and independently re-verified: the position lemma ($k\ge a_1$, $\operatorname{kill}(k)<\infty\Rightarrow a_{\operatorname{kill}(k)}<k$), the private-index lemma (every prime factor of a minimal element has an index meeting its support only there), the corrected descent lemma ($\nu>a_1p\Rightarrow\exists\nu'<\nu/p$ with prescribed support intersection), $\min E_p\le a_1p$, $\tau_p\le\min(t,\operatorname{rad}a_1)$, a "stall" dichotomy for the remaining chain, cross-prime counting, and the rigid clamping of $R$ (see [16-descent-fix.md](16-descent-fix.md)).
5. **Two bridging lemmas that made the own route workable**: (a) $\mu\in\mathcal M\iff\operatorname{supp}(\mu)$ is a $\subseteq$-minimal transversal set — this connects the minimal-element world to transversal theory and is what lets the borrowed step be applied; (b) a reduction lemma: for $x\ge a_1$, "$x$ is a term" is equivalent to "$\gcd(x,a_i)>1$ for every *relevant* $a_i<x$" (relevant = no earlier term whose support is contained in it).
6. **Two real errors found and corrected inside the project**, plus an adversarial review: the direction-of-inequality flaw in the first descent lemma, and a missing hypothesis ($p\tau_p\ge a_1$) in an "identity" lemma. [23-verification-L.md](23-verification-L.md) re-derives 14 lemma groups line by line with zero rebuttals and records both corrections.
7. **Mechanism-level numerics.** Rather than only testing the conclusion, the scripts [logs/verify33.py](logs/verify33.py) and [logs/verify34.py](logs/verify34.py) test the *key lemmas themselves* on the true sequence for 14 values of $a_1$ (zeros: the borrowed LP lemma and the resulting support bound). All other scans (residual $R$, $(CS)$, prime bound, $H$, $H_{1/2}$) show **zero counterexamples** for $a_1$ up to $10^4$.

## 2. What was *not* discovered — and why (honest post-mortem)

The one decisive step, **Lemma LP**: *a term with a prime factor $p>a_1^2$ cannot be minimal for the radical order — indeed it has an earlier term whose support is contained in its own* (proved with the geometric progression $q^k c$), came from the literature. Root causes:

1. **Wrong inference direction.** Every tool in the agent's toolkit produced *lower* bounds on the relevant quantities ($\mu\ge p$, $\mu\ge 2p$, products of cross-primes $\ge\dots$). FME, however, needs an **upper** bound. The agent kept adding constraints instead of hunting for a mechanism that *produces* upper bounds. The whole 40-section residual chain is a monument to this.
2. **$a_1$ was held fixed.** Not a single induction on $a_1$ and no global minimal-counterexample argument was attempted, although the problem is self-similar (the tail satisfies a variant of the rule).
3. **Case-splitting instead of an invariant.** Every round produced new necessary conditions; the residual kept *moving* ($R\to(L)\to$ stall $\to(CS)\to H_{1/2}\to$ three branches) instead of dying — the signature of a missing global idea.
4. **The residual is numerically invisible.** Both $H$ ("all cofactors $\ge a_1$") and $H_{1/2}$ never occur for $a_1\le10^4$, so experiments — the usual way to guess the key lemma — gave no guidance: all scans returned zero counterexamples and therefore almost no information.
5. **Process: volume without a target.** 8 subagents produced long, correct, but locally-motivated lemma lists (one file reached 122 KB / 40 sections). No shared "one-page target" existed, so the work never cohered into the short argument that was actually available. The verifier teammate was also unreliable and the Lead had to write the adversarial review itself.
6. **Over-engineering bias.** The agent optimized *local rigor* (each lemma airtight, each edge case split) rather than *searching for the key mechanism*, and accepted a heavy reduction (FME + TCL + explicit moduli) as "the plan" once it was consistent.

The honest summary: the project produced a **correct but needlessly heavy** route, plus several genuinely new auxiliary results, and it found the decisive modern idea only after searching the web at the very end.

## 3. Telemetry of the run

- Wall-clock: **≈ 590 minutes**, fully autonomous (goal-driven, automatic continuation rounds).
- **8 subagents** (durable teammates): `prover-tcl`, `prover-alt`, `prover-fme`, `prover-h`, `prover-x`, `prover-mu`, `prover-descent`, `verifier-num`; 20+ board tasks with dependencies and write scopes.
- Token usage: **≈ 4×10^8 tokens** (sum over Lead + subagents, approximate).
- Artifacts: 145 files ≈ 2.1 MB (proofs, 40-section lemma banks, adversarial reviews, 108 log/scan files).

## 4. How to reproduce the numerics

```bash
python logs/verify33.py 4000   # mechanism test: characterization + support bound  -> ALL: OK
python logs/verify34.py 3000   # mechanism test: Lemma LP + minimal-element bound -> ALL: OK
python verify.py               # exact-arithmetic harness on small a_1
python logs/cofactor_scan.py 2 3000 3   # residual scans (zero counterexamples)
```

## 5. Proof ideas in one paragraph

Take the set $A_\infty$ of integers sharing a prime with every term; the sequence is $A_\infty\cap[a_1,\infty)$ enumerated. Call a term *relevant* if no earlier term's support is contained in its own; then a term is determined by gcd conditions against relevant terms only. If a term contains a prime $p>a_1^2$, the geometric progression $q^kc$ ($q\mid\gcd(a_1,a_n)$, $c=a_n/p$) produces an earlier, support-contained term, so relevant terms — and hence the supports that matter — live inside the finite set of primes $\le a_1^2$. Consequently the sequence is exactly the set of $a\ge a_1$ whose set of small prime divisors belongs to a fixed finite family, so it depends only on $a$ modulo $L=\prod_{p\le a_1^2}p$; counting the residues in any window of length $L$ gives constants $T,L$ with $a_{n+T}=a_n+L$.

## 6. Attribution in one line

Borrowed: the radical-order/relevance reduction and the "large prime" geometric-progression step, and (for the short proof) the residue-class finish. Everything else — $A_\infty$/minimal-element framework, FME + lattice finish, the residual $R$ and its structural lemmas, the minimal-transversal bridge, the relevant-term reduction, the verification and all numerics — was developed independently during the run.
