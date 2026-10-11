"""Focus: K = mu/pmax and X = prod(S \\ D1).  Report extremes + candidate inequalities."""
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
        p = spf[n]
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
    topK = []
    worstX = (0, 0, 0, 0)
    violX = []
    for a1 in range(lo, hi + 1):
        M, seq = run(a1, B * a1)
        D1 = set(fac(a1))
        for mu in M:
            S = fac(mu)
            P = max(S)
            K = mu // P
            X = 1
            for p in S:
                if p not in D1:
                    X *= p
            topK.append((K / a1, a1, mu, P, K, S))
            if X / a1 > worstX[0]:
                worstX = (X / a1, a1, mu, X)
            if X > a1:
                violX.append((a1, mu, X))
    topK.sort(reverse=True)
    print(f"range [{lo},{hi}]")
    print("top 12 by K/a1  (K = mu/pmax):")
    for t in topK[:12]:
        print(f"   a1={t[1]} mu={t[2]} pmax={t[3]} K={t[4]} K/a1={t[0]:.4f} S={t[5]}")
    print(f"max X/a1 = {worstX[0]:.4f} at a1={worstX[1]} mu={worstX[2]} X={worstX[3]}")
    print(f"violations of X<=a1: {len(violX)} e.g. {violX[:6]}")

main()
