"""快速版：筛素数表 + 增量反链。用于大 a1 / 原始积探测。"""
import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")

def sieve(limit):
    bs = bytearray([1]) * (limit + 1)
    bs[0] = bs[1] = 0
    for i in range(2, int(limit ** 0.5) + 1):
        if bs[i]:
            bs[i * i::i] = bytearray(len(bs[i * i::i]))
    return [i for i in range(limit + 1) if bs[i]]

PRIMES = sieve(200000)

def factor(n):
    f = {}
    for p in PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            e = 0
            while n % p == 0:
                n //= p
                e += 1
            f[p] = e
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def min_elems(ints):
    out = []
    for x in sorted(set(ints)):
        if not any(x % y == 0 for y in out):
            out.append(x)
    return out

def run(a1, nmax):
    from math import gcd
    seq = [a1]
    Z = {q: 0 for q in factor(a1)}
    M = sorted(factor(a1))
    hist = [list(M)]
    birth = {}
    for q in M:
        birth[q] = 1
    n = 1
    deaths = []
    while n < nmax:
        k = seq[-1] + 1
        while True:
            f = factor(k)
            ok = False
            if any(q in Z for q in f):
                m = (1 << n) - 1
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
        D = set(factor(an))
        dead = [b for b in M if gcd(b, an) == 1]
        surv = [b for b in M if gcd(b, an) > 1]
        cand = list(surv)
        for b in dead:
            for p in D:
                cand.append(b * p)
        Mn = min_elems(cand)
        for b in dead:
            deaths.append((n + 1, b))
        for x in Mn:
            if x not in birth:
                birth[x] = n + 1
        M = Mn
        seq.append(an)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        hist.append(list(M))
    return seq, hist, birth, deaths

def main():
    a1s = [int(x) for x in (sys.argv[1:] or ["2310", "30030", "46410", "510510"])]
    for a1 in a1s:
        nmax = 400 if a1 > 100000 else 900
        seq, hist, birth, deaths = run(a1, nmax)
        pers = sorted(set(hist[nmax // 2]) & set(hist[-1]))
        D1 = sorted(factor(a1))
        print("=" * 70)
        print(f"a1={a1} D1={D1} |D1|={len(D1)} Pi={max(D1)}")
        print(f"  seq[0:6]={seq[:6]}")
        print(f"  immortal candidates (survived last half): {pers}")
        print(f"  their birth steps: {[(b, birth[b]) for b in pers]}")
        print(f"  their supports: {[(b, sorted(factor(b))) for b in pers]}")
        print(f"  max pers = {max(pers) if pers else 0}, a1*Pi = {a1*max(D1)}")
        print(f"  deaths: {len(deaths)}, last few: {deaths[-2:]}")
        print(f"  |M_n| max = {max(len(h) for h in hist)}")

main()
