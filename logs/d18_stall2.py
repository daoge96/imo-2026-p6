"""d18_stall2.py -- 检验 stall 型代数命题 (task-12, task-12b).

对 a1 <= HI 与每个素数 p <= B、每个 mu in M:
  若 p∤mu、p*mu in A_inf、且 mu 是 p*mu 的唯一 M-因子 (stall 型), 则
  检查 exists q | mu, q | a1: p*mu <= a1*q.
用法: python d18_stall2.py LO HI
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
    terms = []

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
    nstall = 0
    bad = []
    worst = (0.0,)
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        D1 = set(supp(a1, spf))
        primes = [q for q in range(2, B + 1) if spf[q] == q]
        for mu in M:
            for p in primes:
                if p > B // max(mu, 1):
                    break
                if mu % p == 0:
                    continue
                pm = p * mu
                if pm > B:
                    continue
                if not alive[pm]:
                    continue
                divs = [m for m in M if pm % m == 0]
                if divs != [mu]:
                    continue
                Q = [q for q in supp(mu, spf) if q in D1]
                if not Q:
                    continue
                nstall += 1
                q = max(Q)
                r = pm / (a1 * q)
                if r > worst[0]:
                    worst = (r, a1, p, mu, q, pm, a1 * q)
                if pm > a1 * q:
                    bad.append((a1, p, mu, q, pm, a1 * q))
    print("stall 型 (a1,p,mu) 数:", nstall)
    print("反例数:", len(bad), bad[:10])
    print("max p*mu/(a1*max q) =", worst)

main()
