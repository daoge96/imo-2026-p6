"""d18_crude.py -- 检验"粗糙版 ¬H_half": exists p|mu: mu/p <= a1/2 (task: Lead 新方向).

对每个 a1: 遍历 M, 记录 min_{p|mu} mu/(p a1) 的最大值 (分 |S|=1 / >=2).
用法: python d18_crude.py LO HI
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
    worst1 = (0.0,)
    worst2 = (0.0,)
    worst_all = (0.0,)
    nbad = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        for mu in M:
            S = supp(mu, spf)
            r = min(mu // p for p in S) / a1
            if r > worst_all[0]:
                worst_all = (r, a1, mu, S)
            if len(S) == 1:
                if r > worst1[0]:
                    worst1 = (r, a1, mu, S)
            else:
                if r > worst2[0]:
                    worst2 = (r, a1, mu, S)
                if r > 0.5:
                    nbad += 1
    print("max min_p mu/(p a1) (all):", worst_all)
    print("  |S|=1 分支:", worst1)
    print("  |S|>=2 分支:", worst2)
    print("  |S|>=2 且 >0.5 的反例数:", nbad)

main()
