"""d18_q2.py -- 检验充分条件 q^2 >= p t (prover-descent, task-12).

对每个 (a1,p) with E_p != empty, t = sigma/p, Q_p = {q|t : q|a1}:
  统计 (i) |Q_p| > 0 的对数;  (ii) 其中是否存在 q in Q_p 使 q^2 >= p t;
  并记录 max (p t)/q^2, max p(t/q)/a1 = max sigma/(a1 q).
用法: python d18_q2.py LO HI
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
    nQ = 0
    ncond = 0
    worst_ptq2 = (0.0,)
    worst_L = (0.0,)
    fails = []
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        D1 = set(supp(a1, spf))
        for p in sorted({q for mu in M for q in supp(mu, spf)}):
            sigma = min(mu for mu in M if mu % p == 0)
            t = sigma // p
            Q = [q for q in supp(t, spf) if q in D1]
            if not Q:
                continue
            nQ += 1
            best = min(Q, key=lambda q: (p * t) / (q * q))
            r = (p * t) / (best * best)
            if r > worst_ptq2[0]:
                worst_ptq2 = (r, a1, p, best, t)
            R = min(a1 * q / sigma for q in Q)
            if R > worst_L[0]:
                worst_L = (R, a1, p, t, Q)
            if any(q * q >= p * t for q in Q):
                ncond += 1
            else:
                fails.append((a1, p, t, Q))
    print("(a1,p) with Q_p nonempty:", nQ)
    print("其中满足 exists q: q^2 >= p t 的对数:", ncond, " 不满足:", len(fails))
    print("max min_q (p t)/q^2 =", worst_ptq2)
    print("max min_q a1 q/sigma =", worst_L)
    print("前 10 个不满足 q^2>=pt 的样本:", fails[:10])

main()
