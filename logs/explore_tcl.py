import sys
from math import gcd
from collections import defaultdict
sys.setrecursionlimit(10000)

def gen(a1, steps):
    a = [a1]
    for _ in range(steps):
        k = a[-1] + 1
        while True:
            ok = True
            for x in reversed(a):
                if gcd(k, x) == 1:
                    ok = False
                    break
            if ok:
                break
            k += 1
        a.append(k)
    return a

def spf_sieve(N):
    spf = list(range(N + 1))
    i = 2
    while i * i <= N:
        if spf[i] == i:
            for j in range(i * i, N + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

def factor_primes(x, spf):
    s = []
    while x > 1:
        p = spf[x]
        s.append(p)
        while x % p == 0:
            x //= p
    return s

def analyze(a1, steps, B, label=""):
    a = gen(a1, steps)
    n = len(a)
    A = [None] + a  # 1-indexed
    print("=" * 70)
    print(f"a1={a1} {label}  terms={n}  amax={a[-1]}  last terms={a[-8:]}")
    # masks of occurrence indices per prime
    masks = defaultdict(int)
    spf_small = spf_sieve(max(10, min(B, 200000)))
    for idx, x in enumerate(a, 1):
        y = x
        d = 2
        while d * d <= y:
            if y % d == 0:
                masks[d] |= (1 << (idx - 1))
                while y % d == 0:
                    y //= d
            d += 1
        if y > 1:
            masks[y] |= (1 << (idx - 1))
    full = (1 << n) - 1
    occ_count = {p: bin(m).count('1') for p, m in masks.items()}
    R = sorted(p for p, c in occ_count.items() if c >= 0.5 * n and c >= 3)
    print("R (primes appearing >=50% of terms):", R[:40], " count:", len(R))
    print("num distinct primes seen:", len(masks))

    # supports of terms; dict frozenset -> min index
    D = [frozenset()] + [frozenset(factor_primes(x, spf_small)) for x in a]
    first = {}
    for i in range(1, n + 1):
        if D[i] not in first:
            first[D[i]] = i
    # w(m)
    w = [None] * (n + 1)
    for m in range(2, n + 1):
        dm = sorted(D[m])
        best = None
        for r in range(1, len(dm) + 1):
            from itertools import combinations
            for sub in combinations(dm, r):
                idx = first.get(frozenset(sub))
                if idx is not None and (best is None or idx < best):
                    best = idx
        w[m] = best
    maxw = [None] * (n + 2)
    cur = 0
    for m in range(n, 0, -1):
        if w[m] is not None:
            cur = max(cur, w[m])
        maxw[m] = cur
    Nstar = None
    for N in range(1, n):
        if maxw[N + 1] <= N:
            Nstar = N
            break
    print("TCL minimal N* =", Nstar)
    if Nstar:
        argm = [m for m in range(Nstar + 1, n + 1) if w[m] == maxw[Nstar + 1]]
        print("  binding m (w(m)=N*):", argm[:10], " w:", [w[m] for m in argm[:10]])
        print("  witness support D_i:", [sorted(D[w[m]]) for m in argm[:5]])
    print("  w(m)=None (no witness) for m:", [m for m in range(2, n + 1) if w[m] is None][:20])

    # small-support terms
    small = sorted(range(2, n + 1), key=lambda i: (len(D[i]), A[i]))
    print("  terms with smallest supports:")
    for i in small[:15]:
        print(f"    i={i} a_i={A[i]} D_i={sorted(D[i])}")

    # minimal elements of A_infinity up to B
    covered = [0] * (B + 1)
    mins = []
    for k in range(2, B + 1):
        c = 0
        ks = factor_primes(k, spf_small)
        for p in ks:
            c |= masks.get(p, 0)
        covered[k] = c
        if c == full:
            if not any(k % mm == 0 for mm in mins):
                mins.append(k)
    print("  minimal elements of A_inf (<= %d): %s" % (B, mins[:30]))
    for mu in mins[:30]:
        su = frozenset(factor_primes(mu, spf_small))
        fi = None
        for i in range(1, n + 1):
            if su <= D[i]:
                fi = i
                break
        print(f"    mu={mu} supp={sorted(su)} first i with supp(mu) subset D_i: {fi}")
    return a, n, w, Nstar, mins

if __name__ == "__main__":
    for a1 in [2, 4, 6, 12, 15, 30, 35, 77, 105, 210, 385]:
        analyze(a1, 1200, 20000)
