#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
imo-p6 / task-3：独立数值验证工具（精确整数运算，仅标准库，不联网）。

记号（与 00-problem.md / 01-reduction.md 一致）：
  a_1 >= 2 固定；a_{n+1} = min{ k > a_n : gcd(k,a_i) > 1  ∀ i<=n }；
  D_n = supp(a_n)；A_n = { k >= 2 : supp(k) ∩ D_i ≠ ∅ ∀ i<=n }；A_∞ = ∩_n A_n；
  kill(k) = min{ i : gcd(k,a_i)=1 }（无则 ∞）；kill(k) > n ⟺ k ∈ A_n。
  注意 A_n 对取倍数封闭，且 A_n = ∩_{i<=n} C_i，其中 C_i = ∪_{p∈D_i} pℤ。

三套独立精确生成器（互相比对，避免共因错误）：
  1) naive_gen  —— 逐字按定义（升序扫 k，对 i 逐个 gcd 且早退）。作为"定义真值"。
  2) window_gen —— 位掩码：固定窗口 [a_1,a_1+W) 内维护 A_n ∩ 窗口，每步对 D_n 的素数
                   取「倍数之并」再 AND（击杀）。窗口按需加倍。
  3) fast_gen   —— 维护 M_n := {D_1..D_n} 的 ⊆-极小元（A_n = ∩_{S∈M_n} C_S），
                   用恒等式（本工具证明并数值检验）：
                      A_n ⊆ C_D  ⟺  ∃ S ∈ M_n : S ⊆ D
                   （⟸ 显然；⟹ 取 k = Π_{S∈M}(S\\D 中任一素数) ∈ A_n \\ C_D，只要每个 S ⊄ D）
                   做**精确**击杀判定；下一项用小滑窗掩码（|M|=1 时直接用倍数跳跃）。
                   该生成器与 a_1 大小无关（大 a_1 亦可）。

周期结构：稳定后 A_∞ = A_{N0}（N0 = 最后击杀步）。枚举 A_∞ 的整除极小元 B
（A_∞ 对取倍数封闭 ⇒ A_∞ = ∪_{b∈B} bℤ），A_∞ 的极小正周期 L = lcm(B)，
T = |A_∞ ∩ (0,L]|；再用 KMP（位串最小周期）独立检验 L 的极小性。

用法：
  python verify.py --quick                 # 数十秒
  python verify.py                         # 完整模式（默认）
  python verify.py --tasks gen,period,fme  # 只跑指定任务
  python verify.py --a1 15015 --tasks period,fme
日志：imo-p6/logs/<mode>.log 与 <mode>-summary.json。
"""

from __future__ import annotations

import argparse
import json
import os
import random
import sys
import time
from math import gcd, isqrt

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.path.join(HERE, "logs")

try:
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    sys.stderr.reconfigure(encoding="utf-8", errors="replace")
except Exception:
    pass

INF = float("inf")
_LOG_FH = None
_T0 = time.time()


def set_log(path):
    global _LOG_FH
    if _LOG_FH:
        _LOG_FH.close()
        _LOG_FH = None
    if path:
        os.makedirs(os.path.dirname(path), exist_ok=True)
        _LOG_FH = open(path, "w", encoding="utf-8")


def log(msg=""):
    print(msg, flush=True)
    if _LOG_FH:
        _LOG_FH.write(msg + "\n")
        _LOG_FH.flush()


def logt(msg=""):
    log("[%7.2fs] %s" % (time.time() - _T0, msg))


# ---------------------------------------------------------------------------
# 1. 数论
# ---------------------------------------------------------------------------
def sieve(n):
    if n < 2:
        return []
    bs = bytearray([1]) * (n + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if bs[i]:
            bs[i * i :: i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(2, n + 1) if bs[i]]


PRIMES = sieve(100003)


def factorize(n):
    f = []
    for p in PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            f.append(p)
            while n % p == 0:
                n //= p
    if n > 1:
        f.append(n)
    return tuple(f)


def rad(n):
    r = 1
    for p in factorize(n):
        r *= p
    return r


def lcm_list(xs):
    L = 1
    for x in xs:
        L = L * x // gcd(L, x)
    return L


# ---------------------------------------------------------------------------
# 2. 位掩码工具
# ---------------------------------------------------------------------------
_PAT_CACHE = {}


def _pattern(p, r):
    key = (p, r)
    pat = _PAT_CACHE.get(key)
    if pat is not None:
        return pat
    b = bytearray(p)
    for j in range(p):
        i0 = (r - 8 * j) % p
        while i0 < 8:
            b[j] |= 1 << i0
            i0 += p
    pat = bytes(b)
    _PAT_CACHE[key] = pat
    return pat


def mult_mask(p, lo, n):
    """位 q (0<=q<n) 置 1 ⟺ (lo+q) ≡ 0 (mod p)。"""
    r = (-lo) % p
    nb = (n + 7) // 8
    if p <= 512:
        pat = _pattern(p, r)
        m = int.from_bytes((pat * (nb // p + 2))[:nb], "little")
    else:
        ba = bytearray(nb)
        q = r
        while q < n:
            ba[q >> 3] |= 1 << (q & 7)
            q += p
        m = int.from_bytes(bytes(ba), "little")
    if nb * 8 > n:
        m &= (1 << n) - 1
    return m


def union_mask(S, lo, n):
    m = 0
    for p in S:
        m |= mult_mask(p, lo, n)
    return m


def mask_of_M(M, lo, n):
    m = (1 << n) - 1
    for S in M:
        m &= union_mask(S, lo, n)
    return m


_BITPOS = [[i for i in range(8) if (x >> i) & 1] for x in range(256)]


def set_bits(m):
    if not m:
        return
    raw = m.to_bytes((m.bit_length() + 7) // 8, "little")
    for j, x in enumerate(raw):
        if x:
            base = j * 8
            for i in _BITPOS[x]:
                yield base + i


def min_period(b):
    """有限 0/1 串最小周期（KMP 最长 border）。"""
    n = len(b)
    fail = [0] * n
    k = 0
    for i in range(1, n):
        c = b[i]
        while k and b[k] != c:
            k = fail[k - 1]
        if b[k] == c:
            k += 1
        fail[i] = k
    return n - fail[n - 1]


# ---------------------------------------------------------------------------
# 3. 生成器 1：逐字定义
# ---------------------------------------------------------------------------
def naive_gen(a1, nterms):
    terms = [a1]
    for _ in range(nterms - 1):
        k = terms[-1] + 1
        while True:
            ok = True
            for ai in terms:
                if gcd(k, ai) == 1:
                    ok = False
                    break
            if ok:
                break
            k += 1
        terms.append(k)
    return terms


# ---------------------------------------------------------------------------
# 4. 生成器 2：固定窗口位掩码
# ---------------------------------------------------------------------------
def window_gen(a1, W0, nterms_cap, stable_S=300, W_cap=1 << 26, record_kills=False):
    lo = a1
    W = max(W0, 64)
    full = (1 << W) - 1
    alive = full
    Dlist = [factorize(a1)]
    kill_step = {}
    alive &= union_mask(Dlist[0], lo, W)
    if record_kills:
        for q in set_bits(full ^ alive):
            kill_step[lo + q] = 1
    terms = [a1]
    last_kill, nkill, extensions, steps, maxgap = 1, 1, 0, 1, 0
    stable, hit_cap = False, False
    kill_steps = [1]
    while len(terms) < nterms_cap:
        t = alive >> (terms[-1] - lo + 1)
        if t == 0:
            if W >= W_cap:
                hit_cap = True
                break
            delta = W
            ext = (1 << delta) - 1
            for i, D in enumerate(Dlist, 1):
                before = ext
                ext &= union_mask(D, lo + W, delta)
                if record_kills:
                    for q in set_bits(before ^ ext):
                        kill_step[lo + W + q] = i
            alive |= ext << W
            W += delta
            extensions += 1
            continue
        nxt = terms[-1] + 1 + ((t & -t).bit_length() - 1)
        maxgap = max(maxgap, nxt - terms[-1])
        terms.append(nxt)
        D = factorize(nxt)
        Dlist.append(D)
        before = alive
        alive &= union_mask(D, lo, W)
        steps += 1
        if alive != before:
            last_kill = steps
            nkill += 1
            kill_steps.append(steps)
            if record_kills:
                for q in set_bits(before ^ alive):
                    kill_step[lo + q] = steps
        if steps - last_kill >= stable_S:
            stable = True
            break
    return dict(terms=terms, alive=alive, W=W, lo=lo, last_kill=last_kill, nkill=nkill,
                extensions=extensions, stable=stable, hit_cap=hit_cap, maxgap=maxgap,
                nsteps=steps, kill_steps=kill_steps,
                kill_step=kill_step if record_kills else None)


def w_kill_steps(w):
    return w["kill_steps"]


# ---------------------------------------------------------------------------
# 5. 生成器 3：极小族 M + 精确击杀判定（主生成器）
# ---------------------------------------------------------------------------
def minimal_sets(sets):
    """{D_i} 的 ⊆-极小元（A = ∩_S C_S 只依赖极小元：S ⊆ T 时 C_T ⊆ C_S）。"""
    out = []
    for S in sorted(sets, key=len):
        if any(o <= S for o in out):
            continue
        out = [o for o in out if not (S < o)]
        out.append(S)
    return out


def M_add(M, D, buckets=None):
    """把新约束 D 并入极小族；返回 (是否发生击杀, 桶)。
    击杀 ⟺ ¬∃S∈M: S ⊆ D（文件头恒等式）。用「按最大素数分桶」使判定 ~O(ω(D))。
    注：为效率不做冗余删除（M 可能非极小，但 ∩_{S∈M}C_S = A_n 始终精确，击杀判定仍精确）。"""
    if buckets is None:
        buckets = {}
        for S in M:
            buckets.setdefault(max(S), []).append(S)
    for p in D:
        for S in buckets.get(p, ()):
            if S <= D:
                return False, buckets
    M.append(D)
    buckets.setdefault(max(D), []).append(D)
    return True, buckets


def fast_gen(a1, nterms, stable_S=400, W_extra=128, record_kill_values=False):
    """精确击杀判定 + 小滑窗掩码找下一项；与 a_1 规模无关。"""
    lo = a1
    R = rad(a1)
    M = [frozenset(factorize(a1))]
    buckets = None
    W = max(4096, R + max(R // 2, 64) + W_extra)
    alive = mask_of_M(M, lo, W)

    def next_from(t):
        nonlocal lo, alive
        if len(M) == 1:
            S = M[0]
            return min(((t // p) + 1) * p for p in S)
        while True:
            if t - lo + 1 >= W:
                lo = max(lo + W // 2, t - W // 4)
                alive = mask_of_M(M, lo, W)
            tt = alive >> (t - lo + 1)
            if tt:
                return t + 1 + ((tt & -tt).bit_length() - 1)
            lo = t + 1
            alive = mask_of_M(M, lo, W)

    terms = [a1]
    last_kill, nkill, steps, maxgap = 1, 1, 1, 0
    stable = False
    kill_steps = [1]
    smallest_killed = []
    while len(terms) < nterms:
        nxt = next_from(terms[-1])
        maxgap = max(maxgap, nxt - terms[-1])
        terms.append(nxt)
        D = frozenset(factorize(nxt))
        steps += 1
        kill, buckets = M_add(M, D, buckets)
        if kill:
            if record_kill_values:
                u = union_mask(D, lo, W)
                diff = alive & ~u                      # 窗口内被击杀的位置
                if diff:
                    q = (diff & -diff).bit_length() - 1
                    smallest_killed.append((steps, lo + q))
            last_kill = steps
            nkill += 1
            kill_steps.append(steps)
            alive &= union_mask(D, lo, W)              # A_{n+1} = A_n ∩ C_D（就地更新）
        if steps - last_kill >= stable_S:
            stable = True
            break
    M = minimal_sets(M)
    return dict(terms=terms, M=M, last_kill=last_kill, nkill=nkill, stable=stable,
                maxgap=maxgap, nsteps=steps, kill_steps=kill_steps,
                smallest_killed=smallest_killed)


def in_M(M, k):
    """A = ∩_{S∈M} C_S 的成员判定（按 |S| 升序检查，便于早退）。"""
    for S in M:
        ok = False
        for p in S:
            if k % p == 0:
                ok = True
                break
        if not ok:
            return False
    return True


# ---------------------------------------------------------------------------
# 6. A_∞ 极小元与周期
# ---------------------------------------------------------------------------
def first_ge(B, x):
    return min(((x + b - 1) // b) * b for b in B)


def next_term(B, t):
    return min(((t // b) + 1) * b for b in B)


def enumerate_terms(B, t0, count):
    out = []
    t = t0
    for _ in range(count):
        t = next_term(B, t)
        out.append(t)
    return out


def minimal_elements(M, a1, upto):
    B = []
    for k in range(2, upto + 1):
        if not in_M(M, k):
            continue
        if any(k % b == 0 for b in B):
            continue
        B.append(k)
    return B


def period_from_B(B):
    L = lcm_list(B)
    if L <= 20_000_000:
        buf = bytearray(L + 1)
        for b in B:
            if b <= L:
                buf[b::b] = b"\x01" * len(range(b, L + 1, b))
        return L, sum(buf[1:])
    t = min(B)
    c = 0
    while t <= L:
        c += 1
        t = next_term(B, t)
    return L, c


def first_attainment(terms, T, L):
    if len(terms) - T <= 0:
        return None
    last_bad = -1
    for i in range(len(terms) - T):
        if terms[i + T] - terms[i] != L:
            last_bad = i
    return last_bad + 1


# ---------------------------------------------------------------------------
# 7. (P1)/(P6)/逐字定义
# ---------------------------------------------------------------------------
def check_pairwise(terms, cap=50000):
    """(P1)：∀i≠j, gcd(a_i,a_j)>1。前 cap 项用位掩码全查；更长时另抽样尾部。"""
    n = min(len(terms), cap)
    divmask = {}
    for idx in range(n):
        D = factorize(terms[idx])
        uncov = (1 << idx) - 1
        for p in D:
            uncov &= ~divmask.get(p, 0)
        if uncov:
            bad = (uncov & -uncov).bit_length() - 1
            return False, (bad + 1, idx + 1)
        for p in D:
            divmask[p] = divmask.get(p, 0) | (1 << idx)
    if n >= len(terms):
        return True, None
    step = max(1, (len(terms) - n) // 8)
    for j in range(n, len(terms), step):
        for i in range(j):
            if gcd(terms[j], terms[i]) == 1:
                return False, (i + 1, j + 1)
    return True, None


def verify_literal(terms, upto, gap_sample=4000):
    """逐字检验：gcd 条件 + 区间内每个 k 都不合格（大间隙时按固定步长抽样）。"""
    sampled = 0
    for n in range(min(upto, len(terms) - 1)):
        an, an1 = terms[n], terms[n + 1]
        for i in range(n + 1):
            if gcd(an1, terms[i]) == 1:
                return False, "n=%d gcd(a_{n+1},a_%d)=1" % (n, i + 1)
        gap = an1 - an
        step = 1 if gap <= gap_sample else max(1, gap // gap_sample)
        if step > 1:
            sampled += 1
        for k in range(an + 1, an1, step):
            if all(gcd(k, terms[i]) > 1 for i in range(n + 1)):
                return False, "n=%d k=%d 亦合格但 a_{n+1}=%d" % (n, k, an1)
    return True, ("ok（其中 %d 个间隙为抽样）" % sampled if sampled else "ok")


# ---------------------------------------------------------------------------
# 8. 单值综合分析
# ---------------------------------------------------------------------------
def analyze(a1, opt):
    t_start = time.time()
    gen = fast_gen(a1, opt.nterms_cap, stable_S=opt.stable_S,
                   record_kill_values=opt.record_kills)
    terms, M = gen["terms"], gen["M"]
    out = dict(a1=a1, rad=rad(a1), nterms=len(terms), N0=gen["last_kill"],
               nkill=gen["nkill"], stable=gen["stable"], maxgap=gen["maxgap"],
               M=[sorted(S) for S in M])

    ok_p1, wit = check_pairwise(terms)
    out["P1_ok"], out["P1_witness"] = ok_p1, wit
    out["P6_ok"] = gen["maxgap"] <= out["rad"]
    out["P6_maxgap"] = gen["maxgap"]

    ln = opt.literal_n if a1 <= 100000 else min(opt.literal_n, 8)
    ok_lit, msg = verify_literal(terms, ln)
    out["literal_ok"], out["literal_msg"] = ok_lit, msg
    out["literal_n"] = ln

    nn = min(opt.naive_n, len(terms))
    if a1 > 100000:
        nn = min(nn, 4)
    elif a1 > 30000:
        nn = min(nn, 8)
    if nn >= 2:
        out["naive_match"] = (naive_gen(a1, nn) == terms[:nn])
        out["naive_n"] = nn

    wg = window_gen(a1, max(1024, 4 * out["rad"]), min(3000, len(terms)),
                    stable_S=opt.stable_S, W_cap=min(opt.W_cap, 1 << 22))
    out["window_terms"] = len(wg["terms"])
    out["window_match"] = (wg["terms"] == terms[: len(wg["terms"])])
    out["window_hit_cap"] = wg["hit_cap"]

    # 独立交叉：A_∞ 成员判定（M-表示 vs 逐项 gcd）
    def in_by_terms(k):
        for ai in terms:
            if gcd(k, ai) == 1:
                return False
        return True

    out["Ainf_membership_mismatch"] = None
    lim = min(3000, 4 * a1 + 100)
    for k in range(2, lim):
        if in_M(M, k) != in_by_terms(k):
            out["Ainf_membership_mismatch"] = k
            break

    B = minimal_elements(M, a1, opt.KB(a1))
    out["FME"] = B
    out["FME_count"] = len(B)
    out["FME_max"] = max(B) if B else None
    out["FME_max_ratio"] = (max(B) / a1) if B else None
    out["omega_a1"] = len(factorize(a1))
    # 交叉：每个 FME 元必须属于 A_∞，且任意两个互不整除
    out["FME_ok"] = (all(in_M(M, b) for b in B) and
                     all(b2 % b1 for i, b1 in enumerate(B) for b2 in B[i + 1:]))

    L, T = period_from_B(B)
    out["T"], out["L"] = T, L
    out["L_over_T"] = L / T
    out["Ainf_equals_union_B"] = all(in_M(M, k) == any(k % b == 0 for b in B)
                                     for k in range(2, min(5000, 4 * a1 + 100)))

    n_extra = min(3 * T + 10, opt.tail_cap)
    tail = enumerate_terms(B, terms[-1], n_extra)
    allt = terms + tail
    n0 = first_attainment(allt, T, L) if len(allt) > T else None
    out["first_attain"] = n0
    out["tail_terms"] = len(tail)
    out["period_ok"] = n0 is not None
    out["period_ok_tail"] = bool(n0 is not None and
                                 ((len(allt) - n0) >= 3 * T or (len(allt) - n0) >= opt.tail_cap))
    g2 = fast_gen(a1, len(terms) + 60, stable_S=opt.stable_S)
    k = min(len(g2["terms"]), len(allt))
    out["exact_tail_match"] = (g2["terms"][:k] == allt[:k])
    out["exact_tail_len"] = k

    if opt.kmp and 3 * L <= opt.kmp_span_cap:
        Wk = max(3 * L + 8, 4096)
        base = terms[-1]
        bits = bytearray(Wk)
        for b in B:
            start = ((base + b - 1) // b) * b
            if start - base < Wk:
                bits[start - base :: b] = b"\x01" * len(range(start, base + Wk, b))
        out["kmp_minperiod"] = min_period(bytes(bits))
        out["kmp_ok"] = (out["kmp_minperiod"] == L)
        out["kmp_window"] = Wk
    else:
        out["kmp_minperiod"] = out["kmp_ok"] = None

    if opt.record_kills:
        sk = gen["smallest_killed"]
        out["kill_smallest_values"] = sk[:8]
        out["kill_max_step"] = gen["last_kill"]
        if opt.kill_window and out["rad"] * 8 <= opt.W_cap:
            wg2 = window_gen(a1, max(1024, 4 * out["rad"]), opt.kill_nterms,
                             stable_S=opt.stable_S, W_cap=opt.W_cap, record_kills=True)
            ks = wg2["kill_step"] or {}
            out["kill_values_count"] = len(ks)
            out["kill_max_step_window"] = max(ks.values()) if ks else None
            out["kill_window_W"] = wg2["W"]
            out["kill_window_stable"] = wg2["stable"]

    out["seconds"] = round(time.time() - t_start, 3)
    return out


# ---------------------------------------------------------------------------
# 9. TCL / UCL / 危险 m
# ---------------------------------------------------------------------------
def lemmas_case(a1, opt):
    """对 10-tcl-proof.md 的引理 2.1 / 4.1 / 4.2 做直接数值核对。
    引理 2.1：kill(k)=i<∞ 且 k>=a_1 ⇒ a_i < k（用窗口掩码记录的 (k,i) 对）。
    引理 4.2：极小元 μ 的每个素因子 p <= 2a_1。
    引理 4.1：μ>2a_1、p|μ ⇒ ∃ν'∈𝒮（极小元）: p|ν' 且 ν'<μ/p。"""
    gen = fast_gen(a1, opt.nterms_cap, stable_S=opt.stable_S)
    terms, M = gen["terms"], gen["M"]
    B = minimal_elements(M, a1, opt.KB(a1))
    out = dict(a1=a1, n_terms=len(terms), n_min=len(B))
    # 引理 4.2
    bad42 = next(((b, p) for b in B for p in factorize(b) if p > 2 * a1), None)
    out["lemma42_bad"] = bad42
    # 引理 4.1
    bad41 = None
    for nu in B:
        if nu <= 2 * a1:
            continue
        for p in factorize(nu):
            if not any(v % p == 0 and v * p < nu for v in B):
                bad41 = (nu, p)
                break
        if bad41:
            break
    out["lemma41_bad"] = bad41
    # 引理 2.1：被杀 k 位置
    wg = window_gen(a1, max(1024, 4 * rad(a1)), min(opt.kill_nterms, len(terms) + 200),
                    stable_S=opt.stable_S, W_cap=opt.W_cap, record_kills=True)
    ks = wg["kill_step"] or {}
    bad21 = None
    nchk = 0
    for k, i in ks.items():
        if k < a1:
            continue
        nchk += 1
        if not (i <= len(wg["terms"]) and wg["terms"][i - 1] < k):
            bad21 = (k, i)
            break
    out["lemma21_bad"] = bad21
    out["lemma21_checked"] = nchk
    out["lemma21_window"] = wg["W"]
    return out


def primorial_upto(x):
    r = 1
    for p in PRIMES:
        if p > x:
            break
        r *= p
    return r


def tcl_analysis(terms, upto):
    """
    w(m) = min{ i < m : D_i ⊆ D_m }（无则 ∞，"危险 m"）。
    TCL 最小可行 N* = min{ N : ∀ m ∈ (N,M] : w(m) ≤ N }。
    UCL（∃非空 J⊆{1..N}: ∪_{j∈J} D_j ⊆ D_m）与 TCL 等价：
      J={i} 给 TCL⟹UCL；反之 ∪_{j∈J}D_j ⊆ D_m 蕴含每个 D_j ⊆ D_m。
    """
    M = min(upto, len(terms) - 1)
    D = [None] + [set(factorize(terms[i - 1])) for i in range(1, M + 1)]
    w = [INF] * (M + 1)
    for m in range(2, M + 1):
        dm = D[m]
        for i in range(1, m):
            if D[i] <= dm:
                w[m] = i
                break
    dangerous = [m for m in range(1, M + 1) if w[m] is INF]
    suf = [-INF] * (M + 1)
    cur = -INF
    for N in range(M - 1, 0, -1):
        cur = max(cur, w[N + 1])
        suf[N] = cur
    Nstar = next((N for N in range(1, M + 1) if suf[N] <= N), None)
    return dict(M=M, w=w, dangerous=dangerous, Nstar=Nstar, suf=suf,
                range_insufficient=(Nstar == M))


def ucl_check(terms, N, M):
    P = [None] + [set(factorize(terms[i - 1])) for i in range(1, M + 1)]
    for m in range(N + 1, M + 1):
        U, J = set(), 0
        for j in range(1, min(N, m - 1) + 1):
            if P[j] <= P[m]:
                U |= P[j]
                J += 1
        if J == 0 or not (U <= P[m]):
            return False, (m, J)
    return True, None


# ---------------------------------------------------------------------------
# 10. 影子命题反例
# ---------------------------------------------------------------------------
def shadow_case(a1, M, opt):
    gen = fast_gen(a1, max(M + 1, 200), stable_S=opt.stable_S)
    terms = gen["terms"]
    M = min(M, len(terms) - 1)
    D = [None] + [set(factorize(terms[i - 1])) for i in range(1, M + 1)]
    ex_ne = ex_em = None
    cnt_ne = 0
    for N in range(1, M):
        PN = set()
        for i in range(1, N + 1):
            PN |= D[i]
        fam = [D[i] for i in range(1, N + 1)]
        for m in range(N + 1, M + 1):
            I = D[m] & PN
            if I in fam:
                continue
            if I:
                cnt_ne += 1
                if ex_ne is None:
                    ex_ne = dict(a1=a1, N=N, m=m, inter=sorted(I), Dm=sorted(D[m]))
            elif ex_em is None:
                ex_em = dict(a1=a1, N=N, m=m, Dm=sorted(D[m]))
    return dict(a1=a1, M=M, ex_nonempty=ex_ne, ex_empty=ex_em, cnt_nonempty_fail=cnt_ne)


# ---------------------------------------------------------------------------
# 11. 极小横截集被杀 ⟺ 危险 m（暴力等价检验）
# ---------------------------------------------------------------------------
def minimal_transversals(family):
    P = sorted(set().union(*family)) if family else []
    idx = {p: i for i, p in enumerate(P)}
    masks = [sum(1 << idx[p] for p in F) for F in family]
    out = []
    for S in range(1, 1 << len(P)):
        if all(S & m for m in masks):
            if not any((S >> j & 1) and all((S ^ (1 << j)) & m for m in masks)
                       for j in range(len(P))):
                out.append(frozenset(P[j] for j in range(len(P)) if S >> j & 1))
    return out


def trans_case(a1, M, opt):
    gen = fast_gen(a1, max(M + 1, 200), stable_S=opt.stable_S)
    terms = gen["terms"]
    M = min(M, len(terms) - 1)
    D = [None] + [frozenset(factorize(terms[i - 1])) for i in range(1, M + 1)]
    last_ev = None
    cnt = 0
    for m in range(2, M + 1):
        if any(D[i] <= D[m] for i in range(1, m)):
            continue
        cnt += 1
        last_ev = m
    Ms = min(M, opt.trans_brute_max)
    mism = None
    for m in range(2, Ms + 1):
        mts = minimal_transversals([D[i] for i in range(1, m)])
        ev_brute = any(not (b & D[m]) for b in mts)
        ev_wit = not any(D[i] <= D[m] for i in range(1, m))
        if ev_brute != ev_wit:
            mism = (m, ev_brute, ev_wit)
            break
    return dict(a1=a1, M=M, last_kill_stage=last_ev, count_kill_stages=cnt,
                brute_max=Ms, brute_mismatch=mism)


# ---------------------------------------------------------------------------
# 12. 案例与参数
# ---------------------------------------------------------------------------
def structured_values(quick):
    vals = [2 ** k for k in range(1, 14)] + [3 ** k for k in range(1, 12)]
    vals += [5 ** k for k in range(1, 8)] + [7 ** k for k in range(1, 6)]
    vals += [11 ** k for k in range(1, 5)]
    if quick:
        vals += [35, 105, 210, 385, 1001, 1155, 2310, 3003, 15015]
    else:
        vals += [35, 105, 210, 385, 1001, 1155, 2310, 3003, 15015, 30030, 510510]
        vals += [255255, 720720, 45045, 60060, 46410, 2 ** 16, 3 ** 12,
                 1000003, 999983, 333667]
    return sorted(set(v for v in vals if v >= 2))


def random_values(quick, seed):
    rng = random.Random(seed)
    n = 3 if quick else 8
    lo, hi = (10 ** 4, 10 ** 5) if quick else (10 ** 5, 10 ** 6)
    out = []
    while len(out) < n:
        x = rng.randrange(lo, hi + 1)
        if rng.random() < 0.7:
            x |= 1
        out.append(x)
    return out


class Opt:
    pass


def make_opt(args):
    o = Opt()
    o.quick = args.quick
    o.stable_S = 200 if args.quick else 400
    o.nterms_cap = 8000 if args.quick else 200000
    o.kill_nterms = 4000 if args.quick else 12000
    o.W_cap = (1 << 22) if args.quick else (1 << 25)
    o.kill_window = True
    o.tail_cap = 60_000 if args.quick else 600_000
    o.kmp = True
    o.kmp_span_cap = 400_000 if args.quick else 3_000_000
    o.trans_brute_max = 12
    o.naive_n = 40 if args.quick else 60
    o.literal_n = 30 if args.quick else 50
    o.record_kills = True
    o.seed = args.seed
    o.KB = (lambda a1: max(4000, 2 * a1 + 10)) if args.quick else \
           (lambda a1: max(20000, 2 * a1 + 10))
    o.tcl_max = args.tcl_max
    return o


def tcl_range(a1, opt):
    if opt.quick:
        return min(opt.tcl_max, 8000 if a1 <= 30 else 2000)
    return min(opt.tcl_max, 20000 if a1 <= 60 else (4000 if a1 <= 300 else 3000))


# ---------------------------------------------------------------------------
# 13. 主流程
# ---------------------------------------------------------------------------
def run(args):
    opt = make_opt(args)
    tasks = args.tasks.split(",") if args.tasks != "all" else \
        ["warm", "gen", "period", "kill", "tcl", "shadow", "fme", "trans", "kmp", "lemmas"]
    mode = "quick" if args.quick else "full"
    logdir = args.logdir or LOGDIR
    os.makedirs(logdir, exist_ok=True)
    set_log(os.path.join(logdir, "%s.log" % mode))
    summary = dict(mode=mode, started=time.strftime("%Y-%m-%d %H:%M:%S"),
                   python=sys.version.split()[0], tasks=tasks,
                   argv=" ".join(sys.argv[1:]), seed=opt.seed)
    logt("=== imo-p6 独立数值验证（mode=%s, tasks=%s）===" % (mode, ",".join(tasks)))
    logt("解释器：%s" % sys.executable)
    logt("参数：stable_S=%d nterms_cap=%d W_cap=%d tcl_max=%d seed=%d"
         % (opt.stable_S, opt.nterms_cap, opt.W_cap, opt.tcl_max, opt.seed))

    if "warm" in tasks:
        logt("--- [warm] 自检：三生成器互比 + 逐字定义 + M-击杀恒等式 ---")
        bad = []
        for a1 in list(range(2, 31)) + [35, 105, 2310]:
            n = 60
            naive = naive_gen(a1, n)
            cg = fast_gen(a1, n, stable_S=10 ** 9)["terms"]
            wg = window_gen(a1, 4096, n, stable_S=10 ** 9, W_cap=1 << 22)["terms"]
            if naive != cg or wg[:min(len(wg), 20)] != naive[:min(len(wg), 20)]:
                bad.append(a1)
        logt("  [warm] naive / fast / window 逐项一致：%s（32 个 a_1）"
             % ("全部通过" if not bad else "不一致 %s" % bad))
        lb = []
        for a1 in list(range(2, 21)) + [35, 105, 2310]:
            cg = fast_gen(a1, 120, stable_S=10 ** 9)["terms"]
            ok, msg = verify_literal(cg, 30)
            if not ok:
                lb.append((a1, msg))
        logt("  [warm] 逐字定义（k 极小性 + gcd 条件）：%s"
             % ("全部通过" if not lb else "失败 %s" % lb))
        # 恒等式 A_n ⊆ C_D ⟺ ∃S∈M: S⊆D：与"存在 k<=BOUND 见证 A_n\C_D"对照
        mm = None
        beyond = 0
        BOUND = 20000
        for a1 in list(range(2, 16)) + [35, 105, 210]:
            g = fast_gen(a1, 40, stable_S=10 ** 9)
            M = [frozenset(factorize(a1))]
            for term in g["terms"][1:]:
                D = frozenset(factorize(term))
                ident = not any(S <= D for S in M)          # 恒等式：有击杀
                wit = None
                for k in range(2, BOUND + 1):
                    if in_M(M, k) and not any(k % q == 0 for q in D):
                        wit = k
                        break
                if wit is not None and not ident:
                    mm = (a1, term, "见证 %d 但恒等式说无击杀" % wit)
                    break
                if ident and wit is None:
                    beyond += 1
                M = minimal_sets(M + [D])
            if mm:
                break
        logt("  [warm] 击杀恒等式（对 k<=%d 的见证比对；%d 步见证超出该界）：%s"
             % (BOUND, beyond, "一致" if mm is None else "矛盾 %s" % (mm,)))
        summary["warm_bad"] = bad
        summary["warm_literal_bad"] = lb
        summary["warm_identity_bad"] = mm

    a1s = sorted(set(int(x) for x in args.a1_list.split(","))) if args.a1_list else \
        sorted(set(list(range(2, (61 if args.quick else 301))) +
                   structured_values(args.quick) + random_values(args.quick, opt.seed)))
    logt("案例数：%d（a_1 范围 %d..%d）" % (len(a1s), min(a1s), max(a1s)))

    rows, shadow_rows, tcl_rows, trans_rows = [], [], [], []
    lemma_rows = []
    for a1 in a1s:
        need_ana = any(t in tasks for t in ("gen", "period", "fme", "kill", "kmp"))
        ana = analyze(a1, opt) if need_ana else None
        if ana is not None:
            rows.append(ana)
            logt("a1=%-8d P1=%s P6=%s stable=%s N0=%d 击杀次数=%d (T,L)=(%d,%d) FME|B|=%d "
                 "L/T=%.3f kmp=%s 朴素=%s 窗口=%s %.2fs"
                 % (a1, "ok" if ana["P1_ok"] else "FAIL", "ok" if ana["P6_ok"] else "FAIL",
                    ana["stable"], ana["N0"], ana["nkill"], ana["T"], ana["L"],
                    ana["FME_count"], ana["L_over_T"], ana.get("kmp_ok"),
                    ana.get("naive_match"), ana.get("window_match"), ana["seconds"]))
            if "period" in tasks:
                logt("          首达位置 n0=%s；尾部项数=%d；精确尾部一致=%s；"
                     "A_∞ 成员判定不一致=%s；A_∞=∪B 一致=%s"
                     % (ana["first_attain"], ana["tail_terms"], ana["exact_tail_match"],
                        ana["Ainf_membership_mismatch"], ana["Ainf_equals_union_B"]))
            if "fme" in tasks:
                logt("          FME=%s%s（个数=%d，最大/a1=%.3f，FME校验=%s）"
                     % (ana["FME"][:14], "..." if len(ana["FME"]) > 14 else "",
                        ana["FME_count"], ana["FME_max_ratio"] or 0, ana["FME_ok"]))
            if "kill" in tasks and "kill_max_step_window" in ana:
                logt("          kill：窗口内被击杀值=%d 个，窗口内最大 kill 步=%s（=N0? %s）；"
                     "最小被杀值样例=%s"
                     % (ana["kill_values_count"], ana["kill_max_step_window"],
                        ana["kill_max_step_window"] == ana["N0"],
                        ana["kill_smallest_values"][:4]))

        if "tcl" in tasks:
            M = tcl_range(a1, opt)
            g = fast_gen(a1, max(M + 1, 200), stable_S=opt.stable_S)
            ta = tcl_analysis(g["terms"], M)
            row = dict(a1=a1, M=ta["M"], Nstar=ta["Nstar"],
                       n_dangerous=len(ta["dangerous"]),
                       last_dangerous=(ta["dangerous"][-1] if ta["dangerous"] else None),
                       nterms=len(g["terms"]), stable=g["stable"],
                       range_insufficient=ta["range_insufficient"])
            if ta["Nstar"] is not None:
                # 显式常数核对：N* 是否 <= 2a_1^2（证明中原用的界；Lead 已改为 max{2a_1^2, Π_{p<=2a_1}p}）
                row["two_a1sq"] = 2 * a1 * a1
                row["Nstar_le_2a1sq"] = ta["Nstar"] <= 2 * a1 * a1
                row["primorial_2a1_gt_2a1sq"] = primorial_upto(2 * a1) > 2 * a1 * a1
                ok, wit = ucl_check(g["terms"], ta["Nstar"], ta["M"])
                row["ucl_ok_at_Nstar"] = ok
                row["ucl_witness"] = wit
                if ta["Nstar"] > 1:
                    ok2, _ = ucl_check(g["terms"], ta["Nstar"] - 1, ta["M"])
                    row["fail_at_Nstar_minus1"] = (not ok2)
            tcl_rows.append(row)
            logt("TCL a1=%-8d M=%-6d N*=%s 危险m个数=%-4d 最后危险m=%s UCL@N*=%s N*-1反例=%s%s"
                 % (a1, ta["M"], ta["Nstar"], len(ta["dangerous"]),
                    ta["dangerous"][-1] if ta["dangerous"] else None,
                    row.get("ucl_ok_at_Nstar"), row.get("fail_at_Nstar_minus1"),
                    " [区间或不足]" if ta["range_insufficient"] else ""))

        if "shadow" in tasks and (args.quick or a1 <= 60 or
                                  a1 in (105, 385, 1001, 2310, 3003, 15015)):
            sc = shadow_case(a1, 220, opt)
            shadow_rows.append(sc)
            if sc["ex_nonempty"]:
                e = sc["ex_nonempty"]
                logt("影子反例 a1=%-6d 首个非空反例：N=%d m=%d D_m∩P_N=%s（D_m=%s）"
                     % (a1, e["N"], e["m"], e["inter"], e["Dm"]))

        if "trans" in tasks:
            tc = trans_case(a1, min(tcl_range(a1, opt), 2000), opt)
            trans_rows.append(tc)
            logt("被杀极小横截集 a1=%-8d 最后阶段=%s 阶段数=%d 暴力等价检验(m<=%d)=%s"
                 % (a1, tc["last_kill_stage"], tc["count_kill_stages"], tc["brute_max"],
                    "一致" if tc["brute_mismatch"] is None else "不一致 %s" % tc["brute_mismatch"]))

        if "lemmas" in tasks:
            lc = lemmas_case(a1, opt)
            lemma_rows.append(lc)
            logt("引理核对 a1=%-8d 极小元=%-3d 引理2.1(已核%-6d个被杀值)=%s 引理4.1=%s 引理4.2=%s"
                 % (a1, lc["n_min"], lc.get("lemma21_checked", 0),
                    "ok" if lc["lemma21_bad"] is None else "FAIL %s" % (lc["lemma21_bad"],),
                    "ok" if lc["lemma41_bad"] is None else "FAIL %s" % (lc["lemma41_bad"],),
                    "ok" if lc["lemma42_bad"] is None else "FAIL %s" % (lc["lemma42_bad"],)))

    logt("=== 汇总 ===")
    if rows:
        g_ = lambda f: [r["a1"] for r in rows if f(r)]
        logt("分析案例=%d；P1 反例=%s；P6 反例=%s；逐字定义失败=%s；朴素不一致=%s；窗口不一致=%s"
             % (len(rows), g_(lambda r: not r["P1_ok"]) or "无",
                g_(lambda r: not r["P6_ok"]) or "无", g_(lambda r: not r["literal_ok"]) or "无",
                g_(lambda r: r.get("naive_match") is False) or "无",
                g_(lambda r: r.get("window_match") is False) or "无"))
        logt("周期：不成立=%s；KMP 交叉失败=%s；A_∞成员判定不一致=%s；FME校验失败=%s；未稳定=%s"
             % (g_(lambda r: not r["period_ok"]) or "无", g_(lambda r: r.get("kmp_ok") is False) or "无",
                g_(lambda r: r["Ainf_membership_mismatch"] is not None) or "无",
                g_(lambda r: not r["FME_ok"]) or "无", g_(lambda r: not r["stable"]) or "无"))
        d = max(rows, key=lambda r: r["L_over_T"]); w = max(rows, key=lambda r: r["L"])
        mf = max(rows, key=lambda r: r["FME_count"]); mr = max(rows, key=lambda r: r["FME_max_ratio"] or 0)
        logt("最大 L/T=%.3f（a1=%d）；最大 L=%d（a1=%d）；最大 N0=%d（a1=%d）"
             % (d["L_over_T"], d["a1"], w["L"], w["a1"],
                max(r["N0"] for r in rows), max(rows, key=lambda r: r["N0"])["a1"]))
        logt("FME 个数最大=%d（a1=%d, omega=%d）；最大极小元/a1=%.3f（a1=%d）；"
             "偶数 a1 的 FME=%s" % (mf["FME_count"], mf["a1"], mf["omega_a1"],
                                    mr["FME_max_ratio"] or 0, mr["a1"],
                                    sorted({tuple(r["FME"]) for r in rows if r["a1"] % 2 == 0})[:4]))
        summary["rows"] = rows
    if tcl_rows:
        logt("TCL/UCL：案例=%d；无 N*=%s；N* 最大=%s（a1=%s）；UCL@N* 失败=%s；区间不足=%s；"
             "N*>2a_1^2 的案例=%s（显式界核对）"
             % (len(tcl_rows), [r["a1"] for r in tcl_rows if r["Nstar"] is None] or "无",
                max(tcl_rows, key=lambda r: r["Nstar"] or 0)["Nstar"],
                max(tcl_rows, key=lambda r: r["Nstar"] or 0)["a1"],
                [r["a1"] for r in tcl_rows if r.get("ucl_ok_at_Nstar") is False] or "无",
                [r["a1"] for r in tcl_rows if r["range_insufficient"]] or "无",
                [r["a1"] for r in tcl_rows if r.get("Nstar_le_2a1sq") is False] or "无"))
        summary["tcl"] = tcl_rows
    if shadow_rows:
        ne = [s for s in shadow_rows if s["ex_nonempty"]]
        logt("影子命题：案例=%d；有非空反例的案例=%d；最小反例=%s"
             % (len(shadow_rows), len(ne),
                min([(s["a1"], s["ex_nonempty"]["N"], s["ex_nonempty"]["m"]) for s in ne],
                    default=None)))
        summary["shadow"] = shadow_rows
    if trans_rows:
        logt("被杀极小横截集（⟺危险 m）：案例=%d；最后阶段最大=%s（a1=%s）；暴力等价检验不一致=%s"
             % (len(trans_rows), max(t["last_kill_stage"] or 0 for t in trans_rows),
                max(trans_rows, key=lambda t: t["last_kill_stage"] or 0)["a1"],
                [t["a1"] for t in trans_rows if t["brute_mismatch"]] or "无"))
        summary["trans"] = trans_rows
    if lemma_rows:
        logt("10-tcl-proof 引理核对：案例=%d；引理2.1 反例=%s（共核 %d 个被杀值）；"
             "引理4.1 反例=%s；引理4.2 反例=%s"
             % (len(lemma_rows), [r["a1"] for r in lemma_rows if r["lemma21_bad"]] or "无",
                sum(r.get("lemma21_checked", 0) for r in lemma_rows),
                [r["a1"] for r in lemma_rows if r["lemma41_bad"]] or "无",
                [r["a1"] for r in lemma_rows if r["lemma42_bad"]] or "无"))
        summary["lemmas"] = lemma_rows

    summary["finished"] = time.strftime("%Y-%m-%d %H:%M:%S")
    summary["seconds"] = round(time.time() - _T0, 2)
    jpath = os.path.join(logdir, "%s-summary.json" % mode)
    with open(jpath, "w", encoding="utf-8") as fh:
        json.dump(summary, fh, ensure_ascii=False, indent=1, default=str)
    logt("总耗时 %.2fs；摘要：%s；日志：%s" % (summary["seconds"], jpath,
                                              os.path.join(logdir, "%s.log" % mode)))


def main():
    ap = argparse.ArgumentParser(description="imo-p6 独立数值验证（task-3）")
    ap.add_argument("--quick", action="store_true", help="快速模式（数十秒）")
    ap.add_argument("--tasks", default="all",
                    help="warm,gen,period,kill,tcl,shadow,fme,trans,kmp,all")
    ap.add_argument("--a1", dest="a1_list", default=None, help="逗号分隔 a_1 列表")
    ap.add_argument("--tcl-max", dest="tcl_max", type=int, default=20000)
    ap.add_argument("--seed", dest="seed", type=int, default=20261010)
    ap.add_argument("--logdir", dest="logdir", default=None)
    args = ap.parse_args()
    run(args)


if __name__ == "__main__":
    main()
