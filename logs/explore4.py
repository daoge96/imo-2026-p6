import sys, random
from math import gcd
from collections import defaultdict
from itertools import combinations

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

def analyze(a1, steps, spf):
    a = gen(a1, steps)
    n = len(a)
    masks = defaultdict(int)
    for i, x in enumerate(a, 1):
        for p in fp(x, spf):
            masks[p] |= (1 << (i - 1))
    full = (1 << n) - 1
    D = [None] + [fp(x, spf) for x in a]
    bvals = {}
    bad = []
    for m in range(2, n + 1):
        # find min squarefree k with supp(k) subset of D_m and k in A_inf
        best = None
        ps = sorted(set(D[m]))
        for r in range(1, len(ps) + 1):
            for sub in combinations(ps, r):
                k = 1
                for p in sub:
                    k *= p
                c = 0
                for p in sub:
                    c |= masks[p]
                if c == full:
                    if best is None or k < best:
                        best = k
        if best is None:
            bad.append(m)
        else:
            bvals.setdefault(best, []).append(m)
    return a, n, bvals, bad

if __name__ == "__main__":
    B = 2000000
    spf = spf_sieve(B)
    cases = []
    for a1 in list(range(2, 100)):
        cases.append(a1)
    random.seed(12)
    cases += [random.randint(100, 3000) for _ in range(140)]
    cases += [2*3*5*7*11, 3*5*7*11*13, 2**10, 3**7, 5**5, 1024, 2187, 3125, 999983 % 3000 + 100]
    worst = []
    for a1 in cases:
        a, n, bvals, bad = analyze(a1, 400, spf)
        maxb = max(bvals)
        nb = len(bvals)
        ratio = maxb / a1
        worst.append((ratio, a1, maxb, nb, sorted(bvals)[:12]))
        if bad:
            print("a1=", a1, "NO b_m for m:", bad[:5])
    worst.sort(reverse=True)
    print("top 25 by max_b/a1:")
    for w in worst[:25]:
        print(f"  ratio={w[0]:.3f} a1={w[1]} max_b={w[2]} #distinct_b={w[3]} smallest_b={w[4]}")
    print("max ratio:", worst[0][0], "  max #distinct b:", max(w[3] for w in worst))
    # also check b_m <= a1 + rad always
    def rad(x):
        r = 1
        for p in set(fp(x, spf)):
            r *= p
        return r
    viol = [w for w in worst if w[2] > w[1] + rad(w[1])]
    print("cases with max_b > a1 + rad(a1):", [(w[1], w[2]) for w in viol][:20], " count:", len(viol))
    viol2 = [w for w in worst if w[2] > 2 * w[1]]
    print("cases with max_b > 2a1:", [(w[1], w[2]) for w in viol2], " count:", len(viol2))
