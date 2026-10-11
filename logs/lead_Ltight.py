"""报告 (L) 的最紧实例, 观察结构:
(L): 存在素 q | t, q | a1 使 sigma = nu_p <= a1*q.
输出 margin = min_q a1*q/sigma 最小的若干实例 (margin>=1 即 (L) 成立).
用法: python lead_Ltight.py LO HI [TOPN]
"""
import sys

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

def analyze(a1, mult=4, extra=80):
    B = int(mult * a1) + extra
    spf = spf_sieve(B + 1)
    alive = bytearray([1]) * (B + 2)
    alive[0] = 0; alive[1] = 0
    stamp = [0] * (B + 2)
    st = [0]
    def add(v):
        st[0] += 1
        t = st[0]
        for q in supp(v, spf):
            for j in range(q, B + 1, q):
                stamp[j] = t
        for j in range(2, B + 1):
            if alive[j] and stamp[j] != t:
                alive[j] = 0
    add(a1)
    x = a1
    while True:
        k = x + 1
        while k <= B and alive[k] == 0:
            k += 1
        if k > B:
            break
        add(k); x = k
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return spf, M

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    topn = int(sys.argv[3]) if len(sys.argv) > 3 else 12
    rows = []
    bad = []
    for a1 in range(lo, hi + 1):
        spf, M = analyze(a1)
        D1 = set(supp(a1, spf))
        Ep = {}
        for mu in M:
            for p in supp(mu, spf):
                Ep.setdefault(p, mu)
        for p, sigma in Ep.items():
            t = sigma // p
            if t == 1:
                continue
            Q = [q for q in supp(t, spf) if q in D1]
            if not Q:
                bad.append((a1, p, sigma, t, "Q empty")); continue
            margin = min(a1 * q / sigma for q in Q)
            rows.append((margin, a1, p, sigma, t, Q, supp(sigma, spf)))
    rows.sort()
    print("instances with t>=2:", len(rows), " bad:", len(bad))
    print("tightest (margin = min_q a1*q/sigma, >=1 means (L) holds):")
    for r in rows[:topn]:
        print("margin=%.3f a1=%d p=%d sigma=%d t=%d Q=%s supp(sigma)=%s" % r)
    if bad[:5]:
        print("bad:", bad[:5])

main()
