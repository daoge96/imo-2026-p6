"""Check the |B|=1 branch and the branch mu/p < a1 (X = p vs a1)."""
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
    while seq[-1] <= B and len(seq) < 400000:
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
        cand = [b for b in M if gcd(b, an) > 1]
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
    lo, hi, Bmul = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    b1 = []      # (p/a1, a1, mu, p, mu/p vs a1)
    branch = []  # cases mu/p < a1 with X=p  (|B|=1)
    bad = []
    for a1 in range(lo, hi + 1):
        B = int(Bmul * a1)
        seq, M = run(a1, B)
        for mu in M:
            if mu > B or mu < 2:
                continue
            S = fac(mu)
            D1 = fac(a1)
            Bset = sorted(set(S) - set(D1))
            X = prod(Bset) if Bset else 1
            if X > a1:
                bad.append((a1, mu, X, S))
            if len(Bset) == 1:
                p = Bset[0]
                b1.append((p / a1, a1, mu, p, mu // p >= a1))
                if mu // p < a1:
                    branch.append((p / a1, a1, mu, p, mu // p))
    print(f"a1 in [{lo},{hi}], B={Bmul}*a1;  |B|=1 cases: {len(b1)}")
    print("max p/a1 over |B|=1 cases:", max(b1) if b1 else None)
    print("  (branch mu/p < a1) count:", len(branch), " max p/a1:",
          max(branch) if branch else None)
    print("violations of X <= a1:", bad[:10], " count:", len(bad))

main()
