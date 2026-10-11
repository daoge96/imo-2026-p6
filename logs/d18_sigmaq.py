"""d18_sigmaq.py -- 检验关键量 sigma/(a1*q)  (prover-descent, task-10).

对每个 (a1,p) with E_p != empty, sigma=nu_p, t=sigma/p:
  对每个 q | t 且 q | a1: 记录 sigma/(a1*q).
若 sigma <= a1*q 对某 q 成立, 则 p <= a1*q/t <= a1, 即 R 不成立.
输出: 反例数 (sigma > a1*q), max sigma/(a1*q), max t/(a1) 等.
用法: python d18_sigmaq.py LO HI
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

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    ncase = 0
    bad = []
    worst = (0.0,)
    worst_ratio_none = []
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        D1 = set(supp(a1, spf))
        for p in sorted({q for mu in M for q in supp(mu, spf)}):
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            qs = [q for q in supp(t, spf) if q in D1]
            if not qs:
                worst_ratio_none.append((a1, p, sigma, t, p <= a1))
                continue
            for q in qs:
                ncase += 1
                r = sigma / (a1 * q)
                if r > worst[0]:
                    worst = (r, a1, p, q, sigma, t)
                if sigma > a1 * q:
                    bad.append((a1, p, q, sigma, t))
    print("(a1,p,q) 三元组数:", ncase)
    print("sigma > a1*q 的反例数:", len(bad), bad[:10])
    print("max sigma/(a1*q) =", worst)
    print("无 q|a1 的 (a1,p) 数:", len(worst_ratio_none),
          "其中 p<=a1 全真:", all(w[4] for w in worst_ratio_none))

main()
