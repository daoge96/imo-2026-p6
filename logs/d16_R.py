"""d16_R.py -- 针对残余 R 的独立扫描 (prover-descent).

R: exists p, mu in M: p|mu, p>2a1, 2a1<mu<=a1 p.
等价 (本文档证明): exists p: E_p != empty and p > 2a1.
输出: R 反例数, max p/a1, max nu_p/(2a1), max nu_p/(a1 p), 及 R 具体实例.
用法: python d16_R.py LO HI
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

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    R = []          # R 实例
    maxp = (0.0, None, None)
    nE = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        primes = sorted({p for mu in M for p in supp(mu, spf)})
        for p in primes:
            nE += 1
            nu = min(mu for mu in M if mu % p == 0)
            if p / a1 > maxp[0]:
                maxp = (p / a1, a1, p, nu)
            if p > 2 * a1:
                if nu > 2 * a1:
                    R.append((a1, p, nu, nu <= a1 * p))
                else:
                    R.append(("nu<=2a1!", a1, p, nu))
    print("a1 in [%d,%d];  (a1,p) with E_p nonempty: %d" % (lo, hi, nE))
    print("max p/a1 =", maxp)
    print("R 实例数:", len(R), R[:20])

main()
