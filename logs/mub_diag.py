"""Diagnostics on extremal cases: dump sequence, minimal elements, private indices, cross primes.

Also tests candidate lemmas over a range of a1:
 (C1) mu <= 2*a1                      (T1)
 (C2) mu <= 2*rad(a1)                 (T2)
 (C3) mu <= a1 + rad(a1)              (T3a)
 (C4) mu / pmax <= a1                 (T3b)
 (C5) any two elements of M are non-coprime
 (C6) |supp(mu)| <= omega(a1) (or +1)
 (C7) mu <= a1 * pmax
 (C8) for each p in supp(mu): a_{i_p} <= a1 * something
"""
import sys
from math import gcd

LIM = 3_000_000
spf = list(range(LIM + 1))
i = 2
while i * i <= LIM:
    if spf[i] == i:
        for j in range(i * i, LIM + 1, i):
            if spf[j] == j:
                spf[j] = i
    i += 1

def fac(n):
    s = []
    while n > 1:
        p = spf[n]
        s.append(p)
        while n % p == 0:
            n //= p
    return s

def rad_of(n):
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

def run(a1, B, keep_seq=False):
    seq = [a1]
    Z = {q: 0 for q in fac(a1)}
    M = minimize(fac(a1))
    n = 1
    while seq[-1] <= B:
        k = seq[-1] + 1
        while True:
            comp = (1 << n) - 1
            for q in fac(k):
                if q in Z:
                    comp &= Z[q]
                    if comp == 0:
                        break
            if comp == 0:
                break
            k += 1
        an = k
        D = fac(an)
        dead = [b for b in M if gcd(b, an) == 1]
        cand = [b for b in M if gcd(b, an) > 1]
        for b in dead:
            for p in D:
                cand.append(b * p)
        M = minimize(cand)
        seq.append(an)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
    return M, seq, Z

def cross_report(a1, B=6):
    M, seq, Z = run(a1, B * a1, True)
    Ml = [m for m in M if m <= B * a1]
    print("=" * 78)
    print(f"a1={a1} rad={rad_of(a1)} D1={fac(a1)} 2a1={2*a1}")
    print(f"seq[:20]={seq[:20]}")
    print(f"M (<=B) = {Ml}")
    for mu in Ml:
        S = fac(mu)
        info = []
        for p in S:
            kp = mu // p
            # kill index
            i = None
            for idx, a in enumerate(seq, 1):
                if gcd(kp, a) == 1:
                    i = idx
                    break
            ai = seq[i - 1] if i else None
            info.append((p, kp, i, ai, fac(ai) if ai else None))
        print(f"  mu={mu} S={S} |S|={len(S)} mu/a1={mu/a1:.4f}")
        for p, kp, i, ai, fai in info:
            print(f"     p={p}: mu/p={kp} (mu/p)/a1={kp/a1:.3f} kill={i} a_kill={ai} supp={fai}")
        # cross primes
    cop = [(x, y) for i1, x in enumerate(Ml) for y in Ml[i1 + 1:] if gcd(x, y) == 1]
    print(f"  coprime pairs in M: {cop[:5]}{' ...' if len(cop)>5 else ''} (count {len(cop)})")
    return Ml

def main():
    if len(sys.argv) > 1 and sys.argv[1] == "cases":
        for a1 in [int(x) for x in sys.argv[2:]]:
            cross_report(a1)
        return
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    B = 8
    viol = {k: [] for k in ["C1", "C2", "C3", "C4", "C5", "C7"]}
    worst = []
    for a1 in range(lo, hi + 1):
        M, seq, Z = run(a1, B * a1)
        Ml = [m for m in M if m <= B * a1]
        r = rad_of(a1)
        for mu in Ml:
            if mu > 2 * a1:
                viol["C1"].append((a1, mu))
            if mu > 2 * r:
                viol["C2"].append((a1, mu))
            if mu > a1 + r:
                viol["C3"].append((a1, mu))
            pmax = max(fac(mu))
            if mu > a1 * pmax:
                viol["C4"].append((a1, mu, pmax))
            if mu > a1 * pmax:
                pass
            if mu > a1 * max(fac(a1)):
                viol["C7"].append((a1, mu))
        for x in Ml:
            for y in Ml:
                if x < y and gcd(x, y) == 1:
                    viol["C5"].append((a1, x, y))
        if Ml:
            worst.append((max(Ml) / a1, a1, max(Ml)))
    worst.sort(reverse=True)
    print(f"range [{lo},{hi}]  (B={B}*a1)")
    for kk in viol:
        lst = viol[kk]
        print(f"  {kk}: violations={len(lst)} first={lst[:4]}")
    print("worst mu/a1:", [(f"{w[0]:.4f}", w[1], w[2]) for w in worst[:10]])

main()
