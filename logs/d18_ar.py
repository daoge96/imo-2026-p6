"""d18_ar.py -- 路线 (c): a_r <= 2a1 的定位扫描 (task-15).

对每个 (a1,p) with E_p != empty: 记录
  sigma=nu_p, t=sigma/p, tau_p (F_p 最小实现元), rad(a1), a_r (首个 p-项)
统计: (i) a_r > 2a1 的反例; (ii) "易界" p*min(t,rad(a1)) > 2a1 的残余情形 (含细节).
用法: python d18_ar.py LO HI
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
    s = 1
    while True:
        if all(gcd(s, at) > 1 for at in terms if at % p != 0):
            return s
        s += 1

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    n = 0
    bad = []
    resid = []
    worst = (0.0,)
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        rad1 = 1
        for q in supp(a1, spf):
            rad1 *= q
        for p in sorted({q for mu in M for q in supp(mu, spf)}):
            n += 1
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            tau = tau_p_of(p, terms)
            ar = next(at for at in terms if at % p == 0)
            r = ar / a1
            if r > worst[0]:
                worst = (r, a1, p, t, tau, ar, rad1)
            if ar > 2 * a1:
                bad.append((a1, p, t, tau, ar))
            m = min(t, rad1)
            if p * m > 2 * a1:
                resid.append((a1, p, t, tau, rad1, ar, p * m / (2 * a1)))
            if tau > m:
                print("!! tau > min(t,rad): a1=%d p=%d t=%d rad=%d tau=%d" % (a1, p, t, rad1, tau))
    print("(a1,p) with E_p nonempty:", n)
    print("a_r > 2a1 的反例数:", len(bad), bad[:10])
    print("max a_r/a1 =", worst)
    print("易界失效（残余情形）数:", len(resid))
    for r in resid[:15]:
        print("   a1=%d p=%d t=%d tau_p=%d rad(a1)=%d a_r=%d  p*min/2a1=%.2f" % r)
    lowx = [(a1, p, t, tau, ar) for (a1, p, t, tau, ar) in
            [(r[1], r[2], r[3], r[4], r[5]) for r in []]]
    print("--- p*tau_p < a1 的情形 ---")
    cnt = 0
    worst2 = (0.0,)
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        for p in sorted({q for mu in M for q in supp(mu, spf)}):
            sigma = min(mu for mu in M if mu % p == 0)
            tau = tau_p_of(p, terms)
            if p * tau < a1:
                cnt += 1
                ar = next(at for at in terms if at % p == 0)
                r = ar / a1
                if r > worst2[0]:
                    worst2 = (r, a1, p, tau, ar)
    print("count p*tau_p < a1:", cnt, " max a_r/a1 in this case:", worst2)

main()
