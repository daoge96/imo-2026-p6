"""d17: 大规模扫描（扩展版）。

统计量（全部只依赖窗口内精确的极小元集）：
  (a) max mu/(a1*p)  以及 argmax；            [强不变量 CS: mu/p <= a1]
  (b) CS 反例列表（mu/p > a1 的 (a1,mu,p)）；
  (c) max p/a1 over p|mu；                    [引理 5.2 的数值形式]
  (d) max mu/(2a1)、count(mu>2a1)；
  (e) --stab: 对 B=3a1,6a1,10a1 各自算窗口内极小元，检查三者在 [2,3a1] 上一致（截断稳定性）。

精确性（13-mu-bound.md §7 已证）：a_N > B 时 min A_N ∩ [2,B] = M ∩ [2,B]。
用法: python d17_scan.py LO HI [mult] [--detail|--stab]
"""
import sys, time
from math import gcd

def sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

LIM = 4_000_000
SPF = sieve(LIM)

def fac(n):
    s = []
    while n > 1:
        p = SPF[n] if n <= LIM else None
        if p is None:
            d = 2
            while d * d <= n:
                if n % d == 0:
                    s.append(d)
                    while n % d == 0:
                        n //= d
                d += 1
            if n > 1:
                s.append(n)
            return s
        s.append(p)
        while n % p == 0:
            n //= p
    return s

def minimize(lst):
    out = []
    for x in sorted(set(lst)):
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def run(a1, B):
    seq_last = a1
    fs1 = fac(a1)
    Z = {q: 0 for q in fs1}
    M = minimize(fs1)
    n = 1
    full = 1                      # (1<<n)-1，增量维护
    while seq_last <= B:
        k = seq_last + 1
        while True:
            comp = full
            x = k
            while x > 1:
                q = SPF[x]
                if q in Z:
                    comp &= Z[q]
                    if comp == 0:
                        break
                while x % q == 0:
                    x //= q
            if comp == 0:
                break
            k += 1
        D = fac(k)
        dead = [b for b in M if gcd(b, k) == 1]
        cand = [b for b in M if gcd(b, k) > 1]
        for b in dead:
            for p in D:
                cand.append(b * p)
        M = minimize(cand)
        seq_last = k
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        full = (full << 1) | 1
    return [m for m in M if m <= B]

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    mult = float(sys.argv[3]) if len(sys.argv) > 3 else 6.0
    step = 1
    for a in sys.argv[1:]:
        if a.startswith("--step="):
            step = int(a.split("=")[1])
    stab = "--stab" in sys.argv
    t0 = time.time()
    worst2 = (0.0, 0, 0)
    worstCS = (0.0, 0, 0, 0)
    worstP = (0.0, 0, 0, 0)
    bad2, badCS, mism = [], [], []
    tot = 0
    for a1 in range(lo, hi + 1, step):
        if stab:
            Mw = {}
            for mm in (3.0, 6.0, 10.0):
                B = int(mm * a1) + 8
                Mw[mm] = [m for m in run(a1, B) if m <= 3 * a1 + 8]
            if not (Mw[3.0] == Mw[6.0] == Mw[10.0]):
                mism.append((a1, Mw[3.0], Mw[6.0], Mw[10.0]))
            M = Mw[10.0]
        else:
            B = int(mult * a1) + 8
            M = run(a1, B)
        for mu in M:
            tot += 1
            if mu > 2 * a1:
                bad2.append((a1, mu))
            r2 = mu / (2 * a1)
            if r2 > worst2[0]:
                worst2 = (r2, a1, mu)
            for p in fac(mu):
                rc = mu / (a1 * p)
                if rc > worstCS[0]:
                    worstCS = (rc, a1, mu, p)
                if rc > 1.0:
                    badCS.append((a1, mu, p))
                rp = p / a1
                if rp > worstP[0]:
                    worstP = (rp, a1, mu, p)
    print(f"[d17] range [{lo},{hi}] mult={mult} stab={stab} cases={tot} elapsed={time.time()-t0:.1f}s")
    print(f"[d17] (a) max mu/(a1*p) = {worstCS[0]:.6f} at a1={worstCS[1]} mu={worstCS[2]} p={worstCS[3]}")
    print(f"[d17] (b) CS violations (mu/p > a1): {len(badCS)} first20={badCS[:20]}")
    print(f"[d17] (c) max p/a1 = {worstP[0]:.6f} at a1={worstP[1]} mu={worstP[2]} p={worstP[3]}")
    print(f"[d17] (d) max mu/(2a1) = {worst2[0]:.6f} at a1={worst2[1]} mu={worst2[2]}; count(mu>2a1)={len(bad2)} first20={bad2[:20]}")
    if stab:
        print(f"[d17] (e) B-truncation mismatches: {len(mism)} first5={mism[:5]}")

main()
