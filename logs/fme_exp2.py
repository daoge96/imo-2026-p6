"""FME 精确定位：正确的序列 + A_n 极小元(反链)演化 + 持久极小元(= A_inf 极小元的候选)。
sanity: 用 Berge 极小横截集暴力独立复核 A_n 极小元。"""
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

def build(a1, nmax, verify_at=()):
    """returns seq, hist (step -> list of minimal elements of A_n), parent map, deaths, births"""
    seq = [a1]
    Z = {q: 0 for q in factor(a1)}          # Z[q] bit i = 1 <=> q does not divide a_i
    M = sorted(factor(a1))                  # minimal elements of A_1 = primes of a1
    hist = {1: list(M)}
    parent = {}                             # value -> (parent value, birth step)
    births, deaths = [], []
    n = 1                                   # number of terms currently in seq
    while n < nmax:
        # compute a_{n+1} : least k > a_n in A_n
        k = seq[-1] + 1
        while True:
            f = factor(k)
            if any(q in Z for q in f):
                m = (1 << n) - 1
                for q in f:
                    if q in Z:
                        m &= Z[q]
                        if m == 0:
                            break
                if m == 0:
                    break
            k += 1
        an = k
        D = set(factor(an))
        step = n + 1
        dead = [b for b in M if gcd(b, an) == 1]
        surv = [b for b in M if gcd(b, an) > 1]
        cand = list(surv)
        for b in dead:
            for p in D:
                cand.append(b * p)
        Mn = min_elems(cand)
        for b in dead:
            deaths.append((step, b))
            for p in D:
                if b * p in Mn and b * p not in parent:
                    parent[b * p] = (b, step)
        for x in Mn:
            if x not in M and x not in parent:
                parent[x] = (None, step)
        births.extend((step, b * p, b, p) for b in dead for p in D if b * p in Mn)
        M = Mn
        seq.append(an)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        hist[n] = list(M)
        if n in verify_at:
            mt = min_transversals([frozenset(factor(a)) for a in seq])
            mtp = min_elems([eval('*'.join(map(str, s))) if s else 1 for s in mt] or [1])
            if mtp != sorted(M):
                return dict(seq=seq, hist=hist, parent=parent, births=births,
                            deaths=deaths, mismatch=(n, sorted(mtp), sorted(M)))
    return dict(seq=seq, hist=hist, parent=parent, births=births, deaths=deaths, mismatch=None)

def persistent(a1, nmax):
    r = build(a1, nmax, verify_at=(10, 50, 200))
    if r["mismatch"]:
        print("MISMATCH", a1, r["mismatch"][:2])
    snap = nmax // 2
    Ms = set(r["hist"][snap])
    Mf = set(r["hist"][nmax])
    pers = sorted(Ms & Mf)
    newpers = sorted(Mf - Ms)
    return r, pers, newpers

def ancestry(parent, x):
    chain = []
    while x in parent and parent[x][0] is not None:
        p, st = parent[x]
        chain.append((x, st, p))
        x = p
    chain.append((x, parent.get(x, (None, '?')), None))
    return chain

def main():
    mode = sys.argv[1] if len(sys.argv) > 1 else "detail"
    if mode == "scan":
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        worst = []
        for a1 in range(lo, hi + 1):
            r, pers, newpers = persistent(a1, 700)
            mx = max(pers) if pers else 0
            worst.append((mx / a1, a1, mx, len(pers), sorted(factor(a1)), r["seq"][:4]))
        worst.sort(reverse=True)
        for ratio, a1, mx, lp, D1, head in worst[:25]:
            print(f"a1={a1:6d} D1={D1} maxpers={mx:10d} ratio={ratio:8.3f} |pers|={lp} head={head}")
        print("max ratio:", worst[0][:3])
        bad = [w for w in worst if w[2] > w[1] * max(w[4]) + 5]
        print("violating maxpers <= a1*maxD1:", bad[:10], "count", len(bad))
    else:
        for a1 in [int(x) for x in (sys.argv[2:] or ["15", "35", "187", "385", "15015", "15016"])]:
            r, pers, newpers = persistent(a1, 1500)
            print("=" * 72)
            print(f"a1={a1}  D1={sorted(factor(a1))}  seq head={r['seq'][:8]}")
            print("persistent (= A_inf 极小元候选):", pers)
            for b in pers:
                print(f"   b={b} supp={sorted(factor(b))}")
            print("born late (also persistent):", newpers)
            for b in pers[:6]:
                print("  ancestry of", b, ":", ancestry(r["parent"], b))
            print("total deaths", len(r["deaths"]), "last death", r["deaths"][-3:])
            print("births count", len(r["births"]), "last births", r["births"][-3:])

main()
