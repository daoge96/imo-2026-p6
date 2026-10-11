"""独立小脚本(无 import 副作用)：周期化核对 + mu 界核对。"""
import sys
from math import gcd

def sieve(limit):
    bs = bytearray([1]) * (limit + 1); bs[0] = bs[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if bs[i]:
            bs[i * i::i] = bytearray(len(bs[i * i::i]))
    return [i for i in range(limit + 1) if bs[i]]

PRIMES = sieve(300000)

def factor(n):
    f = {}
    for p in PRIMES:
        if p * p > n: break
        while n % p == 0:
            f[p] = f.get(p, 0) + 1; n //= p
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def min_elems(xs):
    out = []
    for x in sorted(set(xs)):
        if not any(x % y == 0 for y in out): out.append(x)
    return out

def run(a1, nmax):
    seq = [a1]; Z = {q: 0 for q in factor(a1)}; M = sorted(factor(a1))
    hist = [list(M)]; n = 1
    while n < nmax:
        k = seq[-1] + 1
        while True:
            f = factor(k)
            if any(q in Z for q in f):
                m = (1 << n) - 1
                for q in f:
                    if q in Z:
                        m &= Z[q]
                        if m == 0: break
                if m == 0: break
            k += 1
        an = k; D = set(factor(an))
        dead = [b for b in M if gcd(b, an) == 1]
        cand = [b for b in M if gcd(b, an) > 1] + [b * p for b in dead for p in D]
        M = min_elems(cand); seq.append(an)
        for q in list(Z.keys()):
            if q not in D: Z[q] |= (1 << n)
        for q in D:
            if q not in Z: Z[q] = (1 << n) - 1
        n += 1; hist.append(list(M))
    return seq, hist

def check(a1, nmax):
    seq, hist = run(a1, nmax)
    pers = sorted(set(hist[nmax // 2]) & set(hist[-1]))
    L = 1
    for mu in pers: L = L * mu // gcd(L, mu)
    inA = lambda k: k >= 2 and any(k % mu == 0 for mu in pers)
    per_ok = all(inA(k) == inA(k + L) for k in range(2, 4000))
    T = sum(1 for k in range(2, L + 1) if inA(k))
    L1 = inA(L + 1)
    nT_ok = all(seq[n - 1 + T] == seq[n - 1] + L for n in range(1, len(seq) - T + 1))
    mx = max(pers) if pers else 0
    Pi = max(factor(a1))
    print(f"a1={a1:7d} |M|={len(pers):2d} maxmu={mx:8d} mu/(2a1)={mx/(2*a1):6.3f} "
          f"mu/(a1*Pi)={mx/(a1*Pi):6.3f} L={L} T={T} 周期={per_ok} L+1inA={L1} a_(n+T)=a_n+L={nT_ok}")
    return mx

worst = 0.0
for a1 in [2, 3, 15, 35, 187, 385, 1001, 15015, 15016]:
    nmax = 150 if a1 > 10000 else 250
    mx = check(a1, nmax)
    worst = max(worst, mx / (2 * a1))
print("max mu/(2a1) over sample =", round(worst, 4))
