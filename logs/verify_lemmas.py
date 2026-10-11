"""Verify the engine lemmas of the TCL proof on data.

Lemma 2.1 (position lemma): kill(k)=i and k>=a1  =>  a_i < k.
Lemma 2.3: every prime in the support of a minimal element of A_inf is <= 2*a1;
           also (L1) of 02-lead-notes: dangerous m has no witness i<m.
Lemma 4.1: every minimal element is the exact support of some term.
"""
import random
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

def masks_of(a, spf):
    masks = defaultdict(int)
    for i, x in enumerate(a, 1):
        for p in fp(x, spf):
            masks[p] |= (1 << (i - 1))
    return masks

def check(a1, steps, spf, LIM):
    a = gen(a1, steps)
    n = len(a)
    masks = masks_of(a, spf)
    full = (1 << n) - 1
    bad1 = []
    for k in range(a1, LIM):
        c = 0
        for p in fp(k, spf):
            c |= masks.get(p, 0)
        unc = full & ~c
        if unc:
            i = (unc & -unc).bit_length()      # kill(k)
            if i <= n and not (a[i - 1] < k):
                bad1.append((k, i, a[i - 1]))
    mins = []
    for k in range(2, LIM):
        c = 0
        for p in fp(k, spf):
            c |= masks.get(p, 0)
        if c == full and not any(k % m == 0 for m in mins):
            mins.append(k)
    bad2 = [(mu, p) for mu in mins for p in fp(mu, spf) if p > 2 * a1]
    # (L1) check: dangerous m has no earlier witness
    Dsup = [frozenset(fp(x, spf)) for x in a]
    bad3 = []
    n2 = min(n, 300)
    for m in range(2, n2 + 1):
        omega = Dsup[m - 1] & set().union(*Dsup[:m - 1])
        dang = any(not (Dsup[mm - 1] & omega) for mm in range(m + 1, n2 + 1))
        if dang:
            wit = [i for i in range(1, m) if Dsup[i - 1] <= Dsup[m - 1]]
            if wit:
                bad3.append((m, wit[:3]))
    return bad1, mins, bad2, bad3, a

if __name__ == "__main__":
    spf = spf_sieve(3_000_000)
    random.seed(7)
    cases = list(range(2, 120)) + [random.randint(120, 2000) for _ in range(60)]
    tot1 = tot3 = 0
    for a1 in cases:
        b1, mins, b2, b3, a = check(a1, 400, spf, max(3000, 4 * a1))
        tot1 += len(b1); tot3 += len(b3)
        if b1 or b2 or b3:
            print("VIOLATION a1=", a1, "pos:", b1[:4], "prime>2a1:", b2[:4], "(L1):", b3[:4])
    print(f"position-lemma violations: {tot1}; (L1) violations: {tot3}  over {len(cases)} cases")
    # realization lemma (Lemma 4.1): exact support of a term, with enough terms generated
    bad4 = []
    for a1 in range(2, 101):
        b1, mins, b2, b3, a = check(a1, 20000, spf, max(3000, 4 * a1))
        sups = {frozenset(fp(x, spf)) for x in a}
        for mu in mins:
            if frozenset(fp(mu, spf)) not in sups:
                bad4.append((a1, mu))
    print("Lemma 4.1 violations (a1<=100, 20000 terms):", bad4[:10], "count", len(bad4))
    print("bounds seen: max minimal element / a1 =",
          max((max(check(a1, 400, spf, max(3000, 4 * a1))[1] or [0])) / a1 for a1 in range(2, 101)))
