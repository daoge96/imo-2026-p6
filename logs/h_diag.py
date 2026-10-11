"""Structure diagnostics for minimal elements mu: how close is H, and what does the
witness structure (B = S cap D1, E = S \\ D1, A = D1 \\ S) look like?
Also tests candidate-term window claims used by the H-route."""
import sys
from math import gcd
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
    window_bad = []      # window [a1*p, mu/p) contains no term
    least_bad = []       # least term >= a1*p is not < mu/p
    for a1 in range(lo, hi + 1):
        B = int(Bmul * a1)
        seq, M = run(a1, B)
        terms = seq
        for mu in M:
            if mu > B or mu < a1:
                continue
            S = fac(mu)
            D1 = fac(a1)
            A = sorted(set(D1) - set(S))
            Bs = sorted(set(D1) & set(S))
            E = sorted(set(S) - set(D1))
            pmax = max(S)
            X = 1
            for p in E:
                X *= p
            c = a1 // (1 if not Bs else __import__('math').prod(Bs))
            rows.append(dict(a1=a1, mu=mu, s=len(S), S=S, A=A, B=Bs, E=E, X=X, c=c,
                             pmax=pmax, rH=mu / (a1 * pmax), rmu=mu / a1,
                             cpo=c * pmax, ratioX=X / (c * pmax),
                             mu_mod_a1X=(a1 * X) % mu, div=(a1 * X) // mu if (a1 * X) % mu == 0 else None))
            # window tests
            for p in S:
                lo_w, hi_w = a1 * p, mu // p if mu % p else mu // p
                # least term >= a1*p
                idx = None
                for t, v in enumerate(terms):
                    if v >= a1 * p:
                        idx = t
                        break
                lt = terms[idx] if idx is not None else None
                if lt is not None and not (lt < mu / p):
                    least_bad.append((a1, mu, p, lt))
                w = [v for v in terms if lo_w <= v < mu / p]
                if not w:
                    window_bad.append((a1, mu, p, lo_w, mu / p))
    print(f"rows={len(rows)}  a1 in [{lo},{hi}]")
    print("violations of mu | a1*X :", [r for r in rows if r['div'] is None][:10])
    print("violations of X >= c*pmax (i.e. H holds):", [ (r['a1'], r['mu'], r['X'], r['c'], r['pmax']) for r in rows if r['ratioX'] >= 1][:10])
    print(f"least term >= a1*p is >= mu/p  count={len(least_bad)}; first:", least_bad[:8])
    print(f"empty window [a1*p, mu/p) count={len(window_bad)}; first:", window_bad[:8])
    print("\n--- top 18 by mu/a1 (structure) ---")
    for r in sorted(rows, key=lambda r: -r['rmu'])[:18]:
        print(f"a1={r['a1']} mu={r['mu']} mu/a1={r['rmu']:.4f} s={r['s']} S={r['S']} D1={sorted(set(r['A'])|set(r['B']))} A={r['A']} B={r['B']} E={r['E']} X={r['X']} c={r['c']} pmax={r['pmax']} rH={r['rH']:.4f} X/(c*pmax)={r['ratioX']:.4f}")
    print("\n--- top 12 by X/(c*pmax)  (closest to H) ---")
    for r in sorted(rows, key=lambda r: -r['ratioX'])[:12]:
        print(f"a1={r['a1']} mu={r['mu']} s={r['s']} S={r['S']} A={r['A']} B={r['B']} E={r['E']} X={r['X']} c={r['c']} pmax={r['pmax']} rH={r['rH']:.4f} X/(c*pmax)={r['ratioX']:.4f} mu/a1={r['rmu']:.3f}")
    print("\ns distribution:", Counter(r['s'] for r in rows))
    print("(mu-a1)/rad(a1) max:", max(((r['mu'] - r['a1']) / rad(r['a1']), r['a1'], r['mu']) for r in rows))
    print("mu/(a1+rad(a1)) max:", max((r['mu'] / (r['a1'] + rad(r['a1'])), r['a1'], r['mu']) for r in rows))

main()
