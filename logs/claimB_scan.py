"""独立扫描：极小元 mu 的界。
用法:  python claimB_scan.py LO HI [d]
  默认统计 max mu/(2a1) 以及 是否存在 mu>2a1;
  加 d 逐 a1 打印 M 与各量。
方法: 模拟序列到 B=mult*a1, 维护 alive[k] (与所有已处理项互素则剔除).
对 k>=a1, k in A_inf  <=>  alive[k] (由位置引理, 杀手 < k).
"""
import sys, time

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

def analyze(a1, mult=3, extra=60):
    B = mult * a1 + extra
    spf = spf_sieve(B + 1)
    alive = bytearray([1]) * (B + 2)
    alive[0] = 0
    alive[1] = 0
    stamp = [0] * (B + 2)
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
    x = a1
    terms = [a1]
    while True:
        k = x + 1
        while k <= B and alive[k] == 0:
            k += 1
        if k > B:
            break
        terms.append(k)
        add(k)
        x = k
    D1 = set(supp(a1, spf))
    M = []
    for k in range(2, B + 1):
        if alive[k] and not any(k % m == 0 for m in M):
            M.append(k)
    return M, D1, spf, terms

def main():
    lo = int(sys.argv[1]); hi = int(sys.argv[2])
    detail = len(sys.argv) > 3
    t0 = time.time()
    worst_g = (0.0, None, None)
    worst_h = (0.0, None, None)
    worst_p = (0.0, None, None)
    bad, hitH = [], []
    ncase = 0
    for a1 in range(lo, hi + 1):
        M, D1, spf, terms = analyze(a1)
        for mu in M:
            ncase += 1
            if mu > 2 * a1:
                bad.append((a1, mu))
            if mu / (2 * a1) > worst_g[0]:
                worst_g = (mu / (2 * a1), a1, mu)
            gam = min([q for q in D1 if mu % q == 0] or [0])
            if gam and mu / (a1 * gam) > worst_h[0]:
                worst_h = (mu / (a1 * gam), a1, mu, gam)
            S = supp(mu, spf)
            pmax = max(S)
            if mu / (a1 * pmax) > worst_p[0]:
                worst_p = (mu / (a1 * pmax), a1, mu)
            if all(mu // p >= a1 for p in S):
                hitH.append((a1, mu))
        if detail:
            print(f"a1={a1} D1={sorted(D1)} |M|={len(M)} M={M[:12]}")
    print("cases:", ncase, "values(a1):", hi - lo + 1)
    print("max mu/(2a1) =", worst_g)
    print("max mu/(a1*gamma) =", worst_h)
    print("max mu/(a1*pmax) =", worst_p)
    print("count mu>2a1:", len(bad), bad[:20])
    print("count mu with H_p for ALL p (mu/p>=a1):", len(hitH), hitH[:20])
    print("elapsed %.1fs" % (time.time() - t0))

main()
