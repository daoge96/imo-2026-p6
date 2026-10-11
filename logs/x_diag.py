"""Diagnostics for target X := prod_{p in S \\ D1} p <= a1.
Prints the worst cases (X/a1) with full structure + witness data."""
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

def rad(n):
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
    rows = []
    for a1 in range(lo, hi + 1):
        B = int(Bmul * a1)
        seq, M = run(a1, B)
        for mu in M:
            if mu > B or mu < 2:
                continue
            S = fac(mu)
            D1 = fac(a1)
            A = sorted(set(D1) - set(S))
            SB = sorted(set(S) & set(D1))      # S cap D1
            Bset = sorted(set(S) - set(D1))    # S \ D1
            X = prod(Bset) if Bset else 1
            # witness terms: least term with D_t cap S = {p}
            wit = {}
            for p in S:
                for t, v in enumerate(seq):
                    if p in fac(v) and not (set(fac(v)) & (set(S) - {p})):
                        wit[p] = v
                        break
            rows.append(dict(a1=a1, mu=mu, s=len(S), S=S, A=A, SB=SB, Bset=Bset, X=X,
                             xr=X / a1, wit=wit, ml=D1))
    print(f"rows={len(rows)}")
    nb2 = [r for r in rows if len(r['Bset']) >= 2]
    print(f"cases with |S\\D1|>=2: {len(nb2)};  max X/a1 = {max((r['xr'] for r in nb2), default=0):.4f}")
    print(f"all cases: |S\\D1| dist = {Counter(len(r['Bset']) for r in rows)}")
    print("violations X > a1:", [(r['a1'], r['mu'], r['X']) for r in rows if r['X'] > r['a1']][:10])
    print("\n--- top 15 by X/a1 (|S\\D1|>=2 only) ---")
    for r in sorted(nb2, key=lambda r: -r['xr'])[:15]:
        print(f"a1={r['a1']} mu={r['mu']} X={r['X']} X/a1={r['xr']:.4f} S={r['S']} S∩D1={r['SB']} A={r['A']} B={r['Bset']} rad={rad(r['a1'])}")
        for p in r['Bset']:
            T = r['wit'].get(p)
            qs = [q for q in r['A'] if T and T % q == 0]
            print(f"     p={p} mu/p={r['mu']//p} (>=a1? {r['mu']//p >= r['a1']}) T_p={T} T>=p*q? {[q for q in qs]} p^2*q_p<mu? {any(p*p*q < r['mu'] for q in qs)}")
    print("\n--- top 15 by mu/a1 (|S\\D1|>=2 only) ---")
    for r in sorted(nb2, key=lambda r: -r['mu']/r['a1'])[:15]:
        print(f"a1={r['a1']} mu={r['mu']} mu/a1={r['mu']/r['a1']:.4f} X={r['X']} S={r['S']} B={r['Bset']} A={r['A']}")

main()
