"""Scan: exact minimal elements mu of A_N (N = first index with a_N > B), for many a1.

Fact used: if a_N > B then  M ∩ [2,B] = min(A_N) ∩ [2,B]  exactly
  (<=): m in min(A_N), m<=B  =>  m in A_inf (else killed at step j with a_j < m <= B < a_N,
        but m in A_N ⊆ A_j, contradiction) => m in M.
  (>=): mu in M, mu<=B => mu in A_N; if mu not minimal in A_N, pick m | mu, m in min(A_N), m<mu;
        then m in M (just shown) and m | mu properly => contradicts minimality of mu.
So min(A_N)∩[2,B] is exactly the set of minimal elements of A_inf up to B.

Incremental rule for min(A_n):  survivors ∪ children(b*p, p | a_{n+1}) for killed b, then minimize.
"""
import sys
from math import gcd
from time import time

LIM = 4_000_000
spf = list(range(LIM + 1))
i = 2
while i * i <= LIM:
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j:
                spf[j] = i
    i += 1

def fac(n):
    s = []
    while n > 1:
        p = spf[n] if n <= LIM else None
        if p is None:
            # trial division fallback
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

def rad_of(n):
    r = 1
    for p in fac(n):
        r *= p
    return r

def minimize(lst):
    out = []
    for x in sorted(set(lst)):
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def run(a1, B):
    """returns (M, nsteps, last_term, seq) with M = min(A_N) as list."""
    seq = [a1]
    Z = {q: 0 for q in fac(a1)}
    M = minimize(fac(a1))          # min A_1 = primes | a1
    n = 1
    while seq[-1] <= B:
        k = seq[-1] + 1
        while True:
            f = fac(k)
            # k in A_n  <=>  supp(k) hits every D_i (i<=n)
            #            <=>  AND over q|k of Z[q] == 0 ,  Z[q] = {i<=n : q not| a_i}
            comp = (1 << n) - 1
            for q in f:
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
        surv = [b for b in M if gcd(b, an) > 1]
        cand = list(surv)
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
    return M, n, seq[-1], seq

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    Bmul = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    t0 = time()
    worst = []
    bad = []
    for a1 in range(lo, hi + 1):
        B = Bmul * a1
        M, n, last, seq = run(a1, B)
        Ml = [m for m in M if m <= B]
        mx = max(Ml) if Ml else 0
        r1 = mx / a1
        r2 = mx / (2 * a1)
        r3 = mx / rad_of(a1)
        worst.append((r2, a1, mx, r1, r3, len(seq) - 1, seq[:4]))
        if mx > 2 * a1:
            bad.append((a1, mx, r1))
    worst.sort(reverse=True)
    print(f"scanned a1 in [{lo},{hi}], B={Bmul}*a1, {time()-t0:.1f}s")
    print("top 15 by mu/(2a1):")
    for w in worst[:15]:
        print(f"  a1={w[1]} mu={w[2]} mu/a1={w[3]:.4f} mu/(2a1)={w[0]:.4f} mu/rad={w[4]:.4f} steps={w[5]} seq0={w[6]}")
    print("top 8 by mu/rad(a1):")
    for w in sorted(worst, key=lambda x: -x[4])[:8]:
        print(f"  a1={w[1]} mu={w[2]} mu/a1={w[3]:.4f} mu/rad={w[4]:.4f}")
    print(f"violations of mu<=2a1: {len(bad)}")
    for b in bad[:20]:
        print("   ", b)

main()
