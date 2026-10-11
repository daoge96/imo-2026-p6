"""How many |B|=2 (and |B|>=2) cases fall OUTSIDE the newly closed sub-case
min B <= 2 a1 / prod_C p  (系 5.6)?  Also report the ratio minB/(2a1/Pi)."""
import sys
from math import gcd, prod

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
    outside = []
    n2 = 0
    for a1 in range(lo, hi + 1):
        B = int(Bmul * a1)
        seq, M = run(a1, B)
        for mu in M:
            if mu > B or mu < 2:
                continue
            S = fac(mu)
            D1 = fac(a1)
            Bset = sorted(set(S) - set(D1))
            if len(Bset) != 2:
                continue
            n2 += 1
            Pi = prod(sorted(set(S) & set(D1)))
            thr = 2 * a1 / Pi
            r = Bset[0] / thr
            if r > 1:
                outside.append((r, a1, mu, Bset, Pi, thr))
    print(f"a1 in [{lo},{hi}]: |B|=2 cases = {n2}; outside min B <= 2a1/Pi : {len(outside)}")
    print("max ratio minB/(2a1/Pi) overall:", max((o[0] for o in outside), default=0))
    for o in sorted(outside, reverse=True)[:12]:
        print(f"   ratio={o[0]:.3f} a1={o[1]} mu={o[2]} B={o[3]} Pi={o[4]} thr={o[5]:.1f}")

main()
