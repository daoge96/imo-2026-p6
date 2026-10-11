"""Wide-B scan: does H ever hold when mu is allowed to be much larger than a1?
H requires mu = prod(S) >= a1*max(S), so mu >= 2a1; with |S| large mu/a1 can be big,
so B = 8a1 scans may have missed H cases.  MULT=50..400."""
import sys
from math import gcd, prod
from collections import Counter

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

LIM = 1 << 22
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
    while seq[-1] <= B and len(seq) < 100000:
        k = seq[-1] + 1
        while True:
            comp = (1 << n) - 1
            for q in fac(k):
                z = Z.get(q)
                if z is not None:
                    comp &= z
                    if comp == 0:
                        break
            if comp == 0:
                break
            k += 1
        an = k
        D = fac(an)
        surv = [b for b in M if gcd(b, an) > 1]
        cand = list(surv)
        for b in M:
            if gcd(b, an) == 1:
                for p in D:
                    cand.append(b * p)
        M = minimize(cand)
        seq.append(an)
        for q in list(Z):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
    return seq, M

def main():
    lo, hi, mult = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    H = []
    best = (0.0, None)
    bestM = (0.0, None)
    bestX = (0.0, None)
    sb = Counter()
    for a1 in range(lo, hi + 1):
        B = int(mult * a1)
        seq, M = run(a1, B)
        D1 = set(fac(a1))
        for mu in M:
            if mu > B or mu < a1:
                continue
            S = sorted(fac(mu)); m = max(S)
            C = sorted(set(S) & D1); Bs = sorted(set(S) - D1); A = sorted(D1 - set(S))
            X = prod(Bs) if Bs else 1
            rH = mu / (a1 * m)
            sb[(len(Bs), len(S))] += 1
            if rH >= 1:
                H.append((a1, mu, S, A, Bs, C, X, mu / a1))
            if rH > best[0]: best = (rH, (a1, mu, S, A, Bs, C, X, mu / a1, mu / (2 * a1 * a1)))
            if mu / a1 > bestM[0]: bestM = (mu / a1, (a1, mu, S, A, Bs, C, X, rH))
            if X / a1 > bestX[0]: bestX = (X / a1, (a1, mu, S, A, Bs, C, X, rH))
    print(f"a1 in [{lo},{hi}], B={mult}a1")
    print("=== H CASES:", len(H))
    for h in H[:40]:
        print("   ", h)
    print("max rH =", best)
    print("max mu/a1 =", bestM)
    print("max X/a1 =", bestX)
    print("(|B|,|S|) dist:", dict(sb))

main()
