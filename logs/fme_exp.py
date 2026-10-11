"""FME 定位实验：序列、A_n 极小元（增量 + Berge 暴力对照）、极小横截集。
只做定位，不参与证明。"""
import sys
from math import gcd

def factor(n):
    f = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            f[d] = f.get(d, 0) + 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def min_elems(ints):
    """ints: iterable of squarefree ints >=2; return minimal ones under divisibility"""
    out = []
    for x in sorted(set(ints)):
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def minimalize_sets(sets):
    ss = sorted(sets, key=lambda s: (len(s), sorted(s)))
    out = []
    for s in ss:
        if not any(t <= s for t in out):
            out.append(s)
    return out

def min_transversals(family):
    MT = [frozenset()]
    for F in family:
        new = []
        for S in MT:
            if S & F:
                new.append(S)
            else:
                for x in F:
                    new.append(S | {x})
        MT = minimalize_sets(new)
    return MT

def build(a1, nmax, verify_every=0):
    seq = [a1]
    sup = [frozenset(factor(a1).keys())]
    Z = {}
    for q in sup[0]:
        Z[q] = 0
    n = 0
    # incremental minimal elements of A_n (squarefree ints).  A_1 = {k: gcd(k,a1)>1}
    M = [q for q in sorted(sup[0])]
    hist = [(1, list(M))]
    births = []      # (step index 1-based n+1, child, parent, p)
    deaths = []
    while n < nmax:
        mask_n = (1 << n) - 1
        k = seq[-1] + 1
        while True:
            f = factor(k)
            ok = False
            if any(q in Z for q in f):
                m = mask_n
                for q in f:
                    if q in Z:
                        m &= Z[q]
                        if m == 0:
                            break
                ok = (m == 0)
            if ok:
                break
            k += 1
        an = k
        f = factor(an)
        D = frozenset(f.keys())
        # --- incremental minimal elements of A_{n+1} ---
        dead = [b for b in M if gcd(b, an) == 1]
        surv = [b for b in M if gcd(b, an) > 1]
        cand = list(surv)
        for b in dead:
            for p in D:
                cand.append(b * p)
        Mn = min_elems(cand)
        for b in dead:
            for p in D:
                if b * p in Mn:
                    births.append((n + 2, b * p, b, p))
        for b in dead:
            deaths.append((n + 2, b))
        M = Mn
        seq.append(an)
        sup.append(D)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        hist.append((n + 1, list(M)))
        if verify_every and (n % verify_every == 0 or n < 5):
            mt = min_transversals(sup)
            mtp = [1]
            for s in mt:
                pr = 1
                for q in s:
                    pr *= q
                mtp.append(pr)
            mtp = min_elems([x for x in mtp if x >= 2])
            if mtp != sorted(M):
                return dict(seq=seq, hist=hist, births=births, deaths=deaths,
                            mismatch=(n, sorted(mtp), sorted(M)))
    return dict(seq=seq, hist=hist, births=births, deaths=deaths, mismatch=None)

def main():
    samples = [int(x) for x in (sys.argv[1:] or ["2", "15", "35", "187", "385", "15015"])]
    for a1 in samples:
        r = build(a1, 400, verify_every=20)
        seq, hist, births, deaths = r["seq"], r["hist"], r["births"], r["deaths"]
        print("=" * 70)
        print(f"a1={a1}  len={len(seq)}  tail={seq[-6:]}")
        print("mismatch:", r["mismatch"])
        maxM = max((max(m) if m else 0) for _, m in hist)
        maxlen = max(len(m) for _, m in hist)
        print(f"max|M_n| = {maxlen}, max element of M_n = {maxM}")
        print("births (step, child, parent, p):")
        for x in births[:40]:
            print("   ", x)
        # 3-prime elements ever?
        threep = sorted({c for _, c, _, _ in births if len(factor(c)) >= 3})
        print("births with >=3 prime factors:", threep[:20], "count", len(threep))
        allM = sorted({x for _, m in hist for x in m})
        print("all elements ever in M_n:", allM[:40])
        print("all elements ever in M_n with >=3 primes:",
              [x for x in allM if len(factor(x)) >= 3][:20])
        print("deaths count:", len(deaths), " first:", deaths[:10])
        # final stabilised?
        print("M_n at end:", hist[-1][1])

main()
