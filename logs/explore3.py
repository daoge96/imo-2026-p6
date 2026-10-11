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

def rad(x):
    r = 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            r *= d
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        r *= x
    return r

def run(a1, steps, B, spf):
    a = gen(a1, steps)
    n = len(a)
    masks = defaultdict(int)
    D1 = set(fp(a1, spf))
    for i, x in enumerate(a, 1):
        for p in fp(x, spf):
            masks[p] |= (1 << (i - 1))
    full = (1 << n) - 1
    mins = []
    for k in range(2, B + 1):
        if not any(k % p == 0 for p in D1):
            continue
        c = 0
        for p in fp(k, spf):
            c |= masks.get(p, 0)
        if c == full and not any(k % mm == 0 for mm in mins):
            mins.append(k)
    return a, n, mins

if __name__ == "__main__":
    B = 300000
    spf = spf_sieve(B)
    worst = []
    rows = []
    cases = list(range(2, 121)) + [143, 165, 195, 231, 273, 385, 455, 595, 715, 935, 1001, 1105, 1309, 1547, 1729, 2431, 3003, 4641, 15015]
    for a1 in cases:
        a, n, mins = run(a1, 500, B, spf)
        r = rad(a1)
        maxmu = max(mins) if mins else None
        maxp = max((max(fp(m, spf)) for m in mins), default=None)
        maxsz = max((len(fp(m, spf)) for m in mins), default=None)
        rows.append((a1, r, maxmu, maxp, maxsz, len(mins), len(fp(a1, spf))))
        flag = ""
        if maxmu and maxmu > 2 * r:
            flag += " M>2rad"
        if maxp and maxp > 2 * a1:
            flag += " P>2a1"
        if flag:
            worst.append((a1, r, maxmu, maxp, flag, mins[:8]))
        print(f"a1={a1:6d} rad={r:6d} maxmin={maxmu} maxprime_in_min={maxp} maxsize={maxsz} #min={len(mins)}{flag}")
    print("\n=== violations of mu<=2rad or p<=2a1 ===")
    for w in worst:
        print(w)
    print("\nmax ratio maxmu/rad:", max((row[2] / row[1], row[0]) for row in rows if row[2]))
    print("max ratio maxmu/a1:", max((row[2] / row[0], row[0]) for row in rows if row[2]))
    print("max ratio maxp/a1:", max((row[3] / row[0], row[0]) for row in rows if row[3]))
    print("max |supp| =", max(row[4] for row in rows if row[4]), " max |D1| =", max(row[6] for row in rows))
