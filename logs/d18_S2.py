"""d18_S2.py -- |S|=2 的 (CS) 反例形态核对 (task-18).

(CS) 在 mu=pq in M 处失败 <=> q > a1. prover-mu: 反例必呈 p<a1<q, p|a1, q notin D1.
本脚本: 对 a1<=HI 列出所有 |supp(mu)|=2 的 mu in M 及 max supp, 统计有多少满足 max supp>a1.
用法: python d18_S2.py LO HI
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
    tot = 0
    viol = []
    worst = (0.0,)
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        D1 = set(supp(a1, spf))
        for mu in M:
            S = supp(mu, spf)
            if len(S) != 2:
                continue
            tot += 1
            pmin, pmax = min(S), max(S)
            r = pmax / a1
            if r > worst[0]:
                worst = (r, a1, mu, S)
            if pmax > a1:
                viol.append((a1, mu, S, pmin in D1, pmax in D1))
    print("|S|=2 的 mu 数:", tot, " a1 in [%d,%d]" % (lo, hi))
    print("max max(S)/a1 =", worst)
    print("max(S) > a1 的实例数 (即 (CS) 在 |S|=2 处的反例):", len(viol), viol[:10])

main()
