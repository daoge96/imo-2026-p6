"""d16_nu.py -- 检验 nu_p := min{mu in M : p | mu} 的界 (prover-descent).

输出: max nu_p/(2a1), max nu_p/a1, max nu_p/p/a1 (即 (CS) 形式), 违反数.
用法: python d16_nu.py LO HI [detailA1]
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
    lo = int(sys.argv[1]); hi = int(sys.argv[2])
    detailA1 = int(sys.argv[3]) if len(sys.argv) > 3 else -1
    g = (0.0, None, None, None)   # max nu_p/(2a1)
    h = (0.0, None, None, None)   # max nu_p/a1
    cs = (0.0, None, None, None)  # max nu_p/(a1*p)
    bad2, bad1, badcs = [], [], []
    nE = 0
    for a1 in range(lo, hi + 1):
        B = 6 * a1 + 60
        spf, alive, terms, M = build(a1, B)
        primes = sorted({p for mu in M for p in supp(mu, spf)})
        Ep = {}
        for p in primes:
            Ep[p] = [mu for mu in M if mu % p == 0]
        for p in primes:
            nE += 1
            nu = min(Ep[p])
            if nu > 2 * a1:
                bad2.append((a1, p, nu))
            if nu > a1:
                bad1.append((a1, p, nu))
            if nu > a1 * p:
                badcs.append((a1, p, nu))
            g = max(g, (nu / (2 * a1), a1, p, nu))
            h = max(h, (nu / a1, a1, p, nu))
            cs = max(cs, (nu / (a1 * p), a1, p, nu))
        if a1 == detailA1:
            print("a1=%d D1=%s M=%s" % (a1, sorted(supp(a1, spf)), M))
            for p in primes:
                print("   p=%d nu_p=%d nu_p/p=%s E_p=%s" % (p, min(Ep[p]), min(Ep[p]) // p, Ep[p]))
    print("count (a1,p) with E_p nonempty:", nE, " a1 in [%d,%d]" % (lo, hi))
    print("max nu_p/(2a1) =", g)
    print("max nu_p/a1    =", h)
    print("max nu_p/(a1 p)=", cs)
    print("count nu_p > 2a1:", len(bad2), bad2[:10])
    print("count nu_p > a1 :", len(bad1), bad1[:10])
    print("count nu_p > a1*p:", len(badcs), badcs[:10])

main()
