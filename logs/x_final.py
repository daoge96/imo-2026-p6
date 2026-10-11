"""Scan for the true tight inequality in the H-gap.  For each a1 and each minimal
element mu (exact, via min-A_n maintenance) report the candidate ratios:
  rH  = mu/(a1*max S)      [H  <=> rH >= 1]
  rM  = mu/a1              [T1 <=> rM <= 2 kills H]
  rX  = X/a1               [G2, X = prod of S \\ D1]
  rXA = X/(prod(A)*max S)  [suffices for mu <= a1*max S since a1 >= rad(a1)]
"""
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
    while seq[-1] <= B and len(seq) < 200000:
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
        surv = [b for b in M if gcd(b, an) > 1]
        cand = list(surv)
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
        D1 = sorted(set(fac(a1)))
        for mu in M:
            if mu > B or mu < a1:
                continue
            S = sorted(fac(mu))
            m = max(S)
            C = sorted(set(S) & set(D1))
            Bs = sorted(set(S) - set(D1))
            A = sorted(set(D1) - set(S))
            X = prod(Bs) if Bs else 1
            pA = prod(A) if A else 1
            rows.append(dict(a1=a1, mu=mu, S=S, m=m, C=C, B=Bs, A=A, X=X, pA=pA,
                             rH=mu / (a1 * m), rM=mu / a1, rX=X / a1,
                             rXA=X / (pA * m), k=len(Bs), s=len(S)))
    def top(key, n=10):
        return sorted(rows, key=lambda r: -r[key])[:n]
    def show(rs):
        for r in rs:
            print(f"  a1={r['a1']} mu={r['mu']} s={r['s']} S={r['S']} A={r['A']} B={r['B']} C={r['C']} "
                  f"X={r['X']} rH={r['rH']:.4f} rM={r['rM']:.4f} rX={r['rX']:.4f} rXA={r['rXA']:.4f}")
    print(f"rows={len(rows)} a1 in [{lo},{hi}] B={Bmul}a1")
    print("H cases (rH>=1):", sum(1 for r in rows if r['rH'] >= 1))
    print("rH>0.5:", [(r['a1'], r['mu'], r['rH']) for r in rows if r['rH'] > 0.5])
    print("rM>2:", [(r['a1'], r['mu'], r['rM']) for r in rows if r['rM'] > 2])
    print("rX>1:", [(r['a1'], r['mu'], r['rX']) for r in rows if r['rX'] > 1])
    print("rXA>1:", [(r['a1'], r['mu'], r['rXA']) for r in rows if r['rXA'] > 1])
    print("rX>0.5:", len([r for r in rows if r['rX'] > 0.5]), "rXA>0.5:", len([r for r in rows if r['rXA'] > 0.5]))
    print("MAX rH:"); show(top('rH', 8))
    print("MAX rM:"); show(top('rM', 8))
    print("MAX rX:"); show(top('rX', 8))
    print("MAX rXA:"); show(top('rXA', 8))
    g = [r for r in rows if r['k'] >= 2]
    print(f"|B|>=2 rows: {len(g)}; MAX rH over them:"); show(sorted(g, key=lambda r: -r['rH'])[:8])
    print("k dist:", Counter(r['k'] for r in rows), " s dist:", Counter(r['s'] for r in rows))
    print("max mu/m:", max((r['mu'] / r['m'], r['a1'], r['mu']) for r in rows))

main()
