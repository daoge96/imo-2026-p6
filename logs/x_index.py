"""Test conjecture (C): for mu in M with mu >= a1, the term index t(mu) satisfies
t(mu) <= mu / max supp(mu).   Also test t <= mu/m variants and record worst cases.
t(mu) = number of A_inf elements in [a1, mu] = index of mu in the sequence."""
import sys
from math import gcd, prod

def sieve(n):
    spf = list(range(n + 1)); i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j: spf[j] = i
        i += 1
    return spf
LIM = 1 << 22
spf = sieve(LIM)

def fac(n):
    s = []
    while n > 1:
        p = spf[n]
        s.append(p)
        while n % p == 0: n //= p
    return s

def minimize(lst):
    out = []
    for x in sorted(set(lst)):
        if not any(x % y == 0 for y in out): out.append(x)
    return out

def run(a1, B):
    seq = [a1]; Z = {q: 0 for q in fac(a1)}; M = minimize(fac(a1)); n = 1
    while seq[-1] <= B and len(seq) < 200000:
        k = seq[-1] + 1
        while True:
            comp = (1 << n) - 1
            for q in fac(k):
                z = Z.get(q)
                if z is not None:
                    comp &= z
                    if comp == 0: break
            if comp == 0: break
            k += 1
        an = k; D = fac(an)
        cand = [b for b in M if gcd(b, an) > 1]
        for b in M:
            if gcd(b, an) == 1:
                for p in D: cand.append(b * p)
        M = minimize(cand); seq.append(an)
        for q in list(Z):
            if q not in D: Z[q] |= (1 << n)
        for q in D:
            if q not in Z: Z[q] = (1 << n) - 1
        n += 1
    return seq, M

def main():
    lo, hi, mult = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    worstC = (-9, None); worstT = (-9, None); viol = []
    for a1 in range(lo, hi + 1):
        B = int(mult * a1)
        seq, M = run(a1, B)
        idx = {v: i + 1 for i, v in enumerate(seq)}
        for mu in M:
            if mu > B or mu < a1 or mu not in idx: continue
            S = sorted(fac(mu)); m = max(S); t = idx[mu]
            D1 = set(fac(a1)); Bs = sorted(set(S) - D1)
            # (C): t <= mu/m
            if t - mu / m > worstC[0]: worstC = (t - mu / m, (a1, mu, S, t, mu / m))
            if t / (mu / m) > worstT[0]: worstT = (t / (mu / m), (a1, mu, S, t, mu / m, len(Bs)))
            if t > mu / m: viol.append((a1, mu, S, t, mu / m))
    print(f"[{lo},{hi}] B={mult}a1  violations of t<=mu/maxS: {len(viol)}")
    print(" worst (t - mu/m):", worstC)
    print(" worst t/(mu/m):", worstT)
    print(" sample viol:", viol[:15])

main()
