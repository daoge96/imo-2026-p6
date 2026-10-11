"""d18_pa1.py -- 攻 (b): E_p != empty => p <= a1 (prover-descent, task-10).

对每个 a1: 计算 M; 对每个 p in union supp(M): 记录
  p, sigma=nu_p, t=sigma/p, tau_p (F_p 的最小实现元), a_r (首个 p-项), i=kill(t), a_i, rad(a_i)
统计 max p/a1, max p/rad(a1), 并打印 p/a1 最大的若干实例细节.
用法: python d18_pa1.py LO HI [topN]
"""
import sys
from math import gcd

def spf_sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

def supp(x, spf):
    out = []
    while x > 1:
        p = spf[x]
        out.append(p)
        while x % p == 0:
            x //= p
    return out

def build(a1, B):
    spf = spf_sieve(B)
    alive = bytearray([1]) * (B + 1)
    alive[0] = 0
    alive[1] = 0
    stamp = [0] * (B + 1)
    tid = 0

    def add(v):
        nonlocal tid
        tid += 1
        for q in supp(v, spf):
            for j in range(q, B + 1, q):
                stamp[j] = tid
        for j in range(2, B + 1):
            if alive[j] and stamp[j] != tid:
                alive[j] = 0

    add(a1)
    terms = [a1]
    x = a1
    while True:
        k = x + 1
        while k <= B and not alive[k]:
            k += 1
        if k > B:
            break
        terms.append(k)
        add(k)
        x = k
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return spf, alive, terms, M

def tau_p_of(p, terms):
    """F_p 的最小实现元: 最小 s>=1 使 supp(s) 与每个 D_t (p ∤ a_t) 相交."""
    s = 1
    while True:
        if all(gcd(s, at) > 1 for at in terms if at % p != 0):
            return s
        s += 1

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    topN = int(sys.argv[3]) if len(sys.argv) > 3 else 15
    rows = []
    worst_pa1 = (0.0,)
    worst_prad = (0.0,)
    worst_pmaxD1 = (0.0,)
    nE = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        rad1 = 1
        D1 = supp(a1, spf)
        for q in D1:
            rad1 *= q
        maxD1 = max(D1)
        primes = sorted({p for mu in M for p in supp(mu, spf)})
        for p in primes:
            nE += 1
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            tau = tau_p_of(p, terms)
            ar = next(at for at in terms if at % p == 0)
            i = next((idx for idx, at in enumerate(terms, 1) if gcd(at, t) == 1), None)
            ai = terms[i - 1] if i else None
            rad_ai = 1
            if ai:
                for q in supp(ai, spf):
                    rad_ai *= q
            rec = (p / a1, a1, p, sigma, t, tau, ar, i, ai, rad_ai, rad1)
            rows.append(rec)
            if p / a1 > worst_pa1[0]:
                worst_pa1 = (p / a1, a1, p)
            if p / rad1 > worst_prad[0]:
                worst_prad = (p / rad1, a1, p, rad1)
            if p / maxD1 > worst_pmaxD1[0]:
                worst_pmaxD1 = (p / maxD1, a1, p, maxD1)
            if tau > t:
                print("!! TAU>T: a1=%d p=%d sigma=%d t=%d tau=%d" % (a1, p, sigma, t, tau))
            if ar > sigma:
                print("!! AR>SIGMA: a1=%d p=%d sigma=%d ar=%d" % (a1, p, sigma, ar))
    print("(a1,p) with E_p nonempty:", nE)
    print("max p/a1 =", worst_pa1)
    print("max p/rad(a1) =", worst_prad)
    print("max p/max(D1) =", worst_pmaxD1)
    print("count tau_p != t:", sum(1 for r in rows if r[5] != r[4]))
    print("count x_p^min != sigma (p*tau_p != sigma):", sum(1 for r in rows if r[2] * r[5] != r[3]))
    worst_pt = max(rows, key=lambda r: (r[2] + r[4]) / r[1])
    print("max (p+t)/a1 =", ((worst_pt[2] + worst_pt[4]) / worst_pt[1], worst_pt[1], worst_pt[2], worst_pt[4]))
    rows3 = [r for r in rows if r[0] <= 1.0]
    rows.sort(reverse=True)
    print("--- p/a1 最大的 %d 个实例 ---" % topN)
    for r in rows[:topN]:
        print("p/a1=%.3f a1=%d p=%d sigma=%d t=%d tau_p=%d a_r=%d i=%s a_i=%s rad(a_i)=%s rad(a1)=%d"
              % (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10]))
    rows2 = [r for r in rows if r[4] >= 2]
    rows2.sort(reverse=True)
    print("--- 仅 t>=2: p/a1 最大的 %d 个实例 ---" % topN)
    for r in rows2[:topN]:
        print("p/a1=%.3f a1=%d p=%d sigma=%d t=%d tau_p=%d a_r=%d i=%s a_i=%s rad(a_i)=%s rad(a1)=%d"
              % (r[0], r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9], r[10]))
    print("t>=2 实例数:", len(rows2), " max p/a1 (t>=2) =", rows2[0][:4] if rows2 else None)

main()
