"""Do H-cases exist with large mu?  Candidate family a1=2c, S={u,v,c} (c=a1/2 prime).
H: mu/x >= a1 for all x in S  <=>  uv >= a1.  Scan a1=2c for c prime, big B."""
import sys
from math import gcd, prod

def sieve(n):
    spf = list(range(n + 1)); i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j: spf[j] = i
        i += 1
    return spf
LIM = 1 << 22
spf = sieve(LIM)

def fac(n):
    s = []
    while n > 1:
        p = spf[n]
        s.append(p)
        while n % p == 0: n //= p
    return s

def minimize(lst):
    out = []
    for x in sorted(set(lst)):
        if not any(x % y == 0 for y in out): out.append(x)
    return out

def run(a1, B):
    seq = [a1]; Z = {q: 0 for q in fac(a1)}; M = minimize(fac(a1)); n = 1
    while seq[-1] <= B and len(seq) < 400000:
        k = seq[-1] + 1
        while True:
            comp = (1 << n) - 1
            for q in fac(k):
                z = Z.get(q)
                if z is not None:
                    comp &= z
                    if comp == 0: break
            if comp == 0: break
            k += 1
        an = k; D = fac(an)
        cand = [b for b in M if gcd(b, an) > 1]
        for b in M:
            if gcd(b, an) == 1:
                for p in D: cand.append(b * p)
        M = minimize(cand); seq.append(an)
        for q in list(Z):
            if q not in D: Z[q] |= (1 << n)
        for q in D:
            if q not in Z: Z[q] = (1 << n) - 1
        n += 1
    return seq, M

def report(a1, B):
    seq, M = run(a1, B)
    D1 = set(fac(a1))
    res = []
    for mu in M:
        if mu < a1 or mu > B: continue
        S = sorted(fac(mu)); m = max(S)
        rH = mu / (a1 * m)
        if rH >= 1:
            C = sorted(set(S) & D1); Bs = sorted(set(S) - D1); A = sorted(D1 - set(S))
            res.append((a1, mu, S, A, Bs, C, prod(Bs) if Bs else 1,
                        mu / a1, mu / (2 * a1 * a1), rH))
    return seq, M, res

if __name__ == "__main__":
    lo, hi, mult = int(sys.argv[1]), int(sys.argv[2]), float(sys.argv[3])
    for a1 in range(lo, hi + 1):
        B = int(mult * a1)
        seq, M, res = report(a1, B)
        if res:
            print(f"a1={a1} B={B} #terms={len(seq)} #M={len(M)}")
            for r in res:
                print("   H-CASE mu=%d S=%s A=%s B=%s C=%s X=%d mu/a1=%.4f mu/(2a1^2)=%.4f rH=%.4f"
                      % (r[1], r[2], r[3], r[4], r[5], r[6], r[7], r[8], r[9]))
