"""Print ALL minimal elements of A_inf up to B for the given a1 list (large B).
Exactness: M cap [a1,B] = min(A_N) cap [a1,B] when a_N > B (position lemma)."""
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

def minimize_trunc(lst, B):
    """minimal elements of the set; keep only <= 4*B to control growth"""
    out = []
    for x in sorted(set(lst)):
        if x > 8 * B:
            continue
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def run(a1, B):
    seq = [a1]
    Z = {q: 0 for q in fac(a1)}
    M = minimize(fac(a1))
    n = 1
    while seq[-1] <= B and len(seq) < 3_000_000:
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
    a1s = [int(x) for x in sys.argv[1].split(',')]
    Bmul = float(sys.argv[2])
    for a1 in a1s:
        B = int(Bmul * a1)
        seq, M = run(a1, B)
        Ml = [m for m in M if m <= B and m >= 2]
        print(f"a1={a1} B={B} |seq|={len(seq)} last={seq[-1]}")
        for mu in Ml:
            S = fac(mu)
            pmax = max(S)
            print(f"   mu={mu} mu/a1={mu/a1:.4f} s={len(S)} S={S} pmax={pmax} "
                  f"mu/(a1*pmax)={mu/(a1*pmax):.4f}")
        # leftovers beyond B (to see how big minimal elements get)
        big = sorted(m for m in M if m > B)
        print(f"   [>B minimal elements]: {big[:12]}{' ...' if len(big) > 12 else ''}")

main()
