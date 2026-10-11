"""d17_repair: 失效项迭代替换的终止性与幅度（§8.3.2 缺口）。

对每个 a1<=HI、mu in M、r | mu：
  t := mu/r; A' := supp(t) ∩ D1; T := (D1 \\ A') ∪ {r}（T ∩ supp(t) = ∅ ✓）
  重复: 取最小的 s 使 D_s ∩ T = ∅；取 rho := min(D_s \\ (D1 ∪ supp t))（由 §8.3.2(2) 非空）；T |= {rho}
  直到 T 横截。
统计: 步数分布 max、max |T|、max prod(T)/a1、prod(T) < a1 的例数（需要 boost 的）、
      以及最小失效下标是否严格递增的自检（理论终止性）。
用法: python d17_repair.py HI [mult]
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

def main():
    HI = int(sys.argv[1]) if len(sys.argv) > 1 else 800
    mult = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    t0 = time.time()
    Dsup = None
    maxsteps = (0, 0, 0, 0)     # steps, a1, mu, r
    maxprod = (0.0, 0, 0, 0)
    below = 0; total = 0; mono_bad = 0
    step_hist = {}
    for a1 in range(2, HI + 1):
        B = int(mult * a1) + 8
        M, seq = run(a1, B)
        D1 = set(fac(a1))
        Dsup = [set(fac(a)) for a in seq]
        for mu in M:
            for r in fac(mu):
                t = mu // r
                if t < 2:
                    continue
                total += 1
                st = set(fac(t))
                T = (D1 - st) | {r}
                steps = 0
                last_s = 0
                ok = True
                while True:
                    s = None
                    for idx, D in enumerate(Dsup, 1):
                        if not (D & T):
                            s = idx; Ds = D; break
                    if s is None:
                        break
                    if s <= last_s:
                        mono_bad += 1
                    last_s = s
                    rho = min(Ds - D1 - st)
                    T |= {rho}
                    steps += 1
                    if steps > 500:
                        break
                step_hist[steps] = step_hist.get(steps, 0) + 1
                prod = 1
                for p in T:
                    prod *= p
                if prod < a1:
                    below += 1
                if steps > maxsteps[0]:
                    maxsteps = (steps, a1, mu, r)
                if prod / a1 > maxprod[0]:
                    maxprod = (prod / a1, a1, mu, r)
    print(f"[repair] a1<= {HI} cases={total} elapsed={time.time()-t0:.1f}s")
    print(f"[repair] max steps={maxsteps[0]} at a1={maxsteps[1]} mu={maxsteps[2]} r={maxsteps[3]}")
    print(f"[repair] step histogram: {dict(sorted(step_hist.items()))}")
    print(f"[repair] max prod(T)/a1 = {maxprod[0]:.4f} at a1={maxprod[1]} mu={maxprod[2]} r={maxprod[3]}")
    print(f"[repair] prod(T) < a1 (need boost): {below}/{total}")
    print(f"[repair] 最小失效下标非严格递增的违例: {mono_bad}")

main()
