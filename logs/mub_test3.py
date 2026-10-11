"""Test refined structural claims:
 (M7) every prime p | mu satisfies p <= a1   (i.e. max supp(mu) <= a1)
 (M8) |supp(mu) \\ D1| <= |D1 \\ supp(mu)|  (injection B -> A)
 (M9) mu <= a1 * pmin
 (M10) for the smallest prime p0 | mu:  mu/p0 <= a1
 (M11) mu <= 2 pmax
 (M12) mu <= 2 pmin * something ...
Also worst-case report.
"""
import sys
from math import gcd

def sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

LIM = 8_000_000
spf = sieve(LIM)

def fac(n):
    s = []
    while n > 1:
        p = spf[n] if n <= LIM else None
        if p is None:
            d = 2
            while d * d <= n:
                if n % d == 0:
                    s.append(d)
                    while n % d == 0:
                        n //= d
                d += 1
            if n > 1:
                s.append(n)
            return s
        s.append(p)
        while n % p == 0:
            n //= p
    return s

def minimize(lst):
    out = []
    for x in sorted(set(lst)):
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def run(a1, B):
    seq = [a1]
    Z = {q: 0 for q in fac(a1)}
    M = minimize(fac(a1))
    n = 1
    while seq[-1] <= B:
        k = seq[-1] + 1
        while True:
            comp = (1 << n) - 1
            for q in fac(k):
                if q in Z:
                    comp &= Z[q]
                    if comp == 0:
                        break
            if comp == 0:
                break
            k += 1
        an = k
        D = fac(an)
        dead = [b for b in M if gcd(b, an) == 1]
        cand = [b for b in M if gcd(b, an) > 1]
        for b in dead:
            for p in D:
                cand.append(b * p)
        M = minimize(cand)
        seq.append(an)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
    return [m for m in M if m <= B], seq

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    B = 8
    v = {k: [] for k in ["M7", "M8", "M9", "M11"]}
    worstP = (0, 0, 0)
    for a1 in range(lo, hi + 1):
        M, seq = run(a1, B * a1)
        D1 = set(fac(a1))
        for mu in M:
            S = fac(mu)
            if max(S) / a1 > worstP[0]:
                worstP = (max(S) / a1, a1, mu)
            if max(S) > a1:
                v["M7"].append((a1, mu, max(S)))
            if len(set(S) - D1) > len(D1 - set(S)):
                v["M8"].append((a1, mu, sorted(set(S) - D1), sorted(D1 - set(S))))
            if mu > a1 * min(S):
                v["M9"].append((a1, mu, min(S)))
            if mu > 2 * max(S):
                v["M11"].append((a1, mu, max(S)))
    print(f"range [{lo},{hi}]")
    for k in v:
        print(f"  {k}: {len(v[k])} viol  {v[k][:4]}")
    print(f"worst pmax/a1 = {worstP[0]:.4f} at a1={worstP[1]} mu={worstP[2]}")

main()
