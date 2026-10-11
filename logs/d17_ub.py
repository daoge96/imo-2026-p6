"""d17_ub: 测量缺口所需的 a_{i_q} 上界（在 mu/q < a1 的regime）。

对每个 a1<=HI、每个 mu in M、每个 r | mu 且 mu/r < a1（并 mu/r >= 2）：
  i_r := kill(mu/r), 记录 ai := a_{i_r}；
  检验候选上界：ai <= 2a1, ai <= a1 + r, ai <= a1 + pmin(mu), ai <= a1 + mu/r, ai <= a1*r,
并给出 max ai/a1 与其 argmax（Lead 报 a1<=400 时 max ratio=4/3）。
用法: python d17_ub.py HI [mult]
"""
import sys, time
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

LIM = 4_000_000
SPF = sieve(LIM)

def fac(n):
    s = []
    while n > 1:
        p = SPF[n] if n <= LIM else None
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
    full = 1
    while seq[-1] <= B:
        k = seq[-1] + 1
        while True:
            comp = full
            x = k
            while x > 1:
                q = SPF[x]
                if q in Z:
                    comp &= Z[q]
                    if comp == 0:
                        break
                while x % q == 0:
                    x //= q
            if comp == 0:
                break
            k += 1
        D = fac(k)
        dead = [b for b in M if gcd(b, k) == 1]
        cand = [b for b in M if gcd(b, k) > 1]
        for b in dead:
            for p in D:
                cand.append(b * p)
        M = minimize(cand)
        seq.append(k)
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        full = (full << 1) | 1
    return [m for m in M if m <= B], seq

def kill(k, seq):
    for i, a in enumerate(seq, 1):
        if gcd(k, a) == 1:
            return i, a
    return None, None

def main():
    HI = int(sys.argv[1]) if len(sys.argv) > 1 else 1500
    mult = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    t0 = time.time()
    ncase = 0
    viol = {"2a1": 0, "a1+r": 0, "a1+pmin": 0, "a1+mu/r": 0, "a1*r": 0,
            "a1*(mu/r)/r": 0, "2a1*(mu/r)/r": 0, "a1+(mu/r)^2": 0}
    firstviol = {k: [] for k in viol}
    worst = (0.0, 0, 0, 0, 0)
    for a1 in range(2, HI + 1):
        B = int(mult * a1) + 8
        M, seq = run(a1, B)
        for mu in M:
            fs = fac(mu)
            pm = min(fs)
            for r in fs:
                if mu // r < 2 or mu // r >= a1:
                    continue
                i, ai = kill(mu // r, seq)
                if ai is None:
                    continue
                ncase += 1
                if ai / a1 > worst[0]:
                    worst = (ai / a1, a1, mu, r, ai)
                tests = {"2a1": ai <= 2 * a1, "a1+r": ai <= a1 + r,
                         "a1+pmin": ai <= a1 + pm, "a1+mu/r": ai <= a1 + mu // r,
                         "a1*r": ai <= a1 * r,
                         "a1*(mu/r)/r": ai * r <= a1 * (mu // r),
                         "2a1*(mu/r)/r": ai * r <= 2 * a1 * (mu // r),
                         "a1+(mu/r)^2": ai <= a1 + (mu // r) ** 2}
                for key, okv in tests.items():
                    if not okv:
                        viol[key] += 1
                        if len(firstviol[key]) < 5:
                            firstviol[key].append((a1, mu, r, ai))
    print(f"[ub] a1<= {HI} cases(mu/r<a1,mu/r>=2)={ncase} elapsed={time.time()-t0:.1f}s")
    print(f"[ub] max a_(i_r)/a1 = {worst[0]:.4f} at a1={worst[1]} mu={worst[2]} r={worst[3]} a_i={worst[4]}")
    for key in viol:
        print(f"[ub] violations of a_(i_r) <= {key}: {viol[key]}  {firstviol[key]}")

main()
