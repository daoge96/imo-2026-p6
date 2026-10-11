"""Top ratios mu/(a1*pmin) with support sizes, to see which |S| approach the H-threshold."""
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
    return [m for m in M if m <= B]

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    B = 10
    top = []
    for a1 in range(lo, hi + 1):
        for mu in run(a1, B * a1):
            S = fac(mu)
            top.append((mu / (a1 * min(S)), a1, mu, len(S), min(S), max(S)))
    top.sort(reverse=True)
    print(f"range [{lo},{hi}] top20 by mu/(a1*pmin)  (H: >=1 fails)")
    for t in top[:20]:
        print(f"  ratio={t[0]:.4f} a1={t[1]} mu={t[2]} |S|={t[3]} pmin={t[4]} pmax={t[5]}")
    # max per support size
    best = {}
    for t in top:
        if t[3] not in best:
            best[t[3]] = t
    print("best per |S|:", {k: (round(v[0], 4), v[1], v[2]) for k, v in sorted(best.items())})

main()
