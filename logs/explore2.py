import sys
from math import gcd
from collections import defaultdict

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

def fp(x, spf):
    s = []
    while x > 1:
        p = spf[x]
        s.append(p)
        while x % p == 0:
            x //= p
    return s

def minimal_hitting_sets(families, universe_cap=None):
    """Berge algorithm: list of minimal transversals (as frozensets)."""
    cur = [frozenset()]
    for D in families:
        new = []
        for S in cur:
            if S & D:
                new.append(S)
            else:
                for p in D:
                    new.append(S | {p})
        # prune supersets
        new = list(set(new))
        new.sort(key=len)
        keep = []
        for S in new:
            if not any(K <= S for K in keep):
                keep.append(S)
        cur = keep
    return cur

def analyze(a1, steps, B, Ks):
    a = gen(a1, steps)
    n = len(a)
    A = [None] + a
    print("=" * 78)
    print(f"a1={a1} n={n} amax={a[-1]}")
    print("first 30 terms:", A[1:31])
    spf = spf_sieve(max(1000, min(B, 300000)))
    D = [None] + [frozenset(fp(x, spf)) for x in a]
    print("first 30 supports:", [sorted(D[i]) for i in range(1, 31)])
    # prime occurrence info
    occ = defaultdict(list)
    for i in range(1, n + 1):
        for p in D[i]:
            occ[p].append(i)
    late = sorted([p for p, l in occ.items() if l[-1] > n - 40 and len(l) >= 5])
    print("primes with >=5 occ and last occ in tail:", late)
    print("primes in D_1:", sorted(D[1]))
    for p in sorted(D[1]):
        print(f"   p={p}: count={len(occ[p])} last={occ[p][-1]}")
    # how many primes die out early
    from collections import Counter
    cnt = Counter()
    for p, l in occ.items():
        cnt[l[-1] // 100 * 100] += 1
    print("histogram of last-occurrence index (bucket):", sorted(cnt.items())[:12])

    # masks for A_inf test
    masks = defaultdict(int)
    for i in range(1, n + 1):
        for p in D[i]:
            masks[p] |= (1 << (i - 1))
    full = (1 << n) - 1
    covered = [0] * (B + 1)
    mins = []
    for k in range(2, B + 1):
        c = 0
        for p in fp(k, spf):
            c |= masks.get(p, 0)
        covered[k] = c
        if c == full and not any(k % mm == 0 for mm in mins):
            mins.append(k)
    print("minimal elements of A_inf up to %d: %s" % (B, mins))
    print("  (max prime in them:", max((max(fp(m, spf)) for m in mins), default=None), ")")
    for mu in mins:
        su = frozenset(fp(mu, spf))
        exact = next((i for i in range(1, n + 1) if D[i] == su), None)
        contain = next((i for i in range(1, n + 1) if su <= D[i]), None)
        print(f"   mu={mu} supp={sorted(su)} first_index_with_supp(mu)<=D_i: {contain}  first_exact: {exact}")

    # minimal transversals of prefixes, and whether they survive
    Ks = [K for K in Ks if K <= n]
    for K in Ks:
        MT = minimal_hitting_sets([D[i] for i in range(1, K + 1)])
        surv = [sorted(T) for T in MT if all(T & D[i] for i in range(1, n + 1))]
        dead = [sorted(T) for T in MT if not all(T & D[i] for i in range(1, n + 1))]
        print(f" K={K}: #MT={len(MT)} #surviving={len(surv)} #dead={len(dead)}")
        if K <= 60 and len(dead) <= 6:
            print(f"    dead ones: {dead}")
    return a, n, D, mins

if __name__ == "__main__":
    for a1 in [15, 35, 105, 385, 1001]:
        analyze(a1, 1500, 200000, [5, 10, 15, 20, 30, 40, 60, 100, 200, 400, 800, 1500])
