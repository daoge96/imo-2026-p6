"""Independent scan for H:  exists mu in Min(A_inf) with  for all p | mu : mu/p >= a1 ?

Two modes:
  brute  : literally replay the greedy definition (slow, small a1) + direct A_N membership.
  fast   : incremental min(A_n) update (prover-mu style) for wide ranges.

In both modes the exactness justification is:
  if a_N > B  then  {mu in Min(A_inf) : mu <= B, mu >= a1} = {mu in Min(A_N): mu <= B}
  (position lemma: k >= a1 in A_N with kill(k)=j<inf  =>  a_j < k <= B < a_N  => j < N  => k !in A_N .)
Elements mu < a1 are reported separately (they can only satisfy H if mu >= 2a1, so they never do).
"""
import sys
from math import gcd

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

def run_brute(a1, B):
    """plain greedy replay; returns (seq, Min(A_N)) with a_N > B (or N cap)."""
    seq = [a1]
    M = minimize(fac(a1))           # min A_1
    while seq[-1] <= B and len(seq) < 200000:
        k = seq[-1] + 1
        while True:
            ok = True
            for a in seq:
                if gcd(k, a) == 1:
                    ok = False
                    break
            if ok:
                break
            k += 1
        D = fac(k)
        surv = [b for b in M if gcd(b, k) > 1]
        cand = list(surv)
        for b in M:
            if gcd(b, k) == 1:
                for p in D:
                    cand.append(b * p)
        M = minimize(cand)
        seq.append(k)
    return seq, M

def run_fast(a1, B):
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

def Htest(mu, a1):
    S = fac(mu)
    return all(mu // p >= a1 for p in S), S

def main():
    mode = sys.argv[1]
    lo, hi, Bmul = int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4])
    runner = run_brute if mode == 'brute' else run_fast
    worst = []          # by mu/(a1*pmax)  -- H iff >= 1
    worst2 = []         # by mu/(a1*pmin)
    hits = []
    maxmu = []          # mu/(2a1)  (check lemma 5.2 numerically)
    badmu = 0
    for a1 in range(lo, hi + 1):
        B = int(Bmul * a1)
        seq, M = runner(a1, B)
        for mu in M:
            if mu > B:
                continue
            if mu < a1:
                continue          # H would need mu >= 2a1 > a1
            ok, S = Htest(mu, a1)
            pmax, pmin = max(S), min(S)
            worst.append((mu / (a1 * pmax), a1, mu, len(S), pmax, pmin, seq.index(mu) + 1 if mu in seq else -1))
            worst2.append((mu / (a1 * pmin), a1, mu, len(S), pmax, pmin))
            maxmu.append((mu / (2 * a1), a1, mu, len(S), pmax))
            if mu > 2 * a1:
                badmu += 1
            if ok:
                hits.append((a1, mu, S))
    print(f"mode={mode} a1 in [{lo},{hi}], B={Bmul}*a1, pairs seen={len(worst)}")
    print(f"H hits: {len(hits)}  (mu>2a1 violations of lemma 5.2: {badmu})")
    for h in hits[:20]:
        print("   HIT", h)
    print("top 20 by mu/(a1*pmax)   [H iff >=1]:")
    for w in sorted(worst, reverse=True)[:20]:
        print(f"   ratio={w[0]:.4f} a1={w[1]} mu={w[2]} |S|={w[3]} pmax={w[4]} pmin={w[5]} idx={w[6]}")
    print("top 12 by mu/(a1*pmin):")
    for w in sorted(worst2, reverse=True)[:12]:
        print(f"   ratio={w[0]:.4f} a1={w[1]} mu={w[2]} |S|={w[3]} pmax={w[4]} pmin={w[5]}")
    print("top 12 by mu/(2a1):")
    for w in sorted(maxmu, reverse=True)[:12]:
        print(f"   ratio={w[0]:.4f} a1={w[1]} mu={w[2]} |S|={w[3]} pmax={w[4]}")
    # distribution of |S| among worst-by-pmax
    from collections import Counter
    print("|S| distribution over top 200 by pmax-ratio:", Counter(w[3] for w in sorted(worst, reverse=True)[:200]))
    print("|S| distribution overall:", Counter(w[3] for w in worst))

main()
