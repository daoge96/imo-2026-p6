"""Test strong conjectures:
 (M1) for all mu in M, for all p | mu :  mu/p <= a1
 (M2) for all mu in M :  mu / min(supp mu) <= a1
 (M3) for all mu in M :  mu / max(supp mu) <= a1
 (M4) for all mu :  mu <= a1 * min(supp mu)
 (M5) all elements of M pairwise non-coprime
 (M6) mu <= 2a1^2
Also: ratio distribution split by 2 in supp(mu) or not.
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

LIM = 6_000_000
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
    viol = {k: [] for k in ["M1", "M2", "M3", "M4", "M5", "M6"]}
    worst_even = (0, 0, 0)
    worst_odd = (0, 0, 0)
    for a1 in range(lo, hi + 1):
        M, seq = run(a1, B * a1)
        for mu in M:
            S = fac(mu)
            if 2 in S:
                if mu / a1 > worst_even[0]:
                    worst_even = (mu / a1, a1, mu)
            else:
                if mu / a1 > worst_odd[0]:
                    worst_odd = (mu / a1, a1, mu)
            if mu > 2 * a1 * a1:
                viol["M6"].append((a1, mu))
            for p in S:
                if mu // p > a1:
                    viol["M1"].append((a1, mu, p))
            if mu // min(S) > a1:
                viol["M2"].append((a1, mu, min(S)))
            if mu // max(S) > a1:
                viol["M3"].append((a1, mu, max(S)))
            if mu > a1 * min(S):
                viol["M4"].append((a1, mu, min(S)))
        for i1, x in enumerate(M):
            for y in M[i1 + 1:]:
                if gcd(x, y) == 1:
                    viol["M5"].append((a1, x, y))
    print(f"range [{lo},{hi}] B={B}a1")
    for k in viol:
        print(f"  {k}: {len(viol[k])} violations  e.g. {viol[k][:5]}")
    print(f"worst mu/a1 with 2|mu  : {worst_even}")
    print(f"worst mu/a1 with 2 nmid: {worst_odd}")

main()
