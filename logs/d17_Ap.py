"""d17_Ap: 校验 prover-descent 的 T0/W0 路线（引理 25.1-25.4）。

对每个 a1<=HI、mu in M、r | mu（mu/r>=2）：
  A' := supp(mu/r) ∩ D1; prod := prod_{p in A'} p (空=1); W0 := a1*r/prod
  统计: prod < r/2 的例数（=> W0 > 2a1，T0 幅度不够）;  prod > r 的例数（=> W0 < a1，T0 太短）
  T0 := (D1 \\ A') ∪ {r}; 检查 T0 是否横截（对全部已生成项 D_t）; 若不横截，记录失效 s 的形状。
用法: python d17_Ap.py HI [mult]
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
    HI = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    mult = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    t0 = time.time()
    ncase = 0; lo_bad = 0; hi_bad = 0
    lo_ex = []; hi_ex = []; nonT = 0; nonT_ex = []
    for a1 in range(2, HI + 1):
        B = int(mult * a1) + 8
        M, seq = run(a1, B)
        D1 = set(fac(a1))
        for mu in M:
            for r in fac(mu):
                if mu // r < 2:
                    continue
                ncase += 1
                Ap = set(fac(mu // r)) & D1
                prod = 1
                for p in Ap:
                    prod *= p
                if prod * 2 < r:
                    lo_bad += 1
                    if len(lo_ex) < 6:
                        lo_ex.append((a1, mu, r, sorted(Ap), prod))
                if prod > r:
                    hi_bad += 1
                    if len(hi_ex) < 6:
                        hi_ex.append((a1, mu, r, sorted(Ap), prod))
                T0 = (D1 - Ap) | {r}
                okv = all(T0 & set(fac(a)) != set() for a in seq)
                if not okv:
                    nonT += 1
                    if len(nonT_ex) < 6:
                        bad_s = [s for s, a in enumerate(seq, 1)
                                 if (set(fac(a)) & D1) <= Ap and a % r != 0]
                        nonT_ex.append((a1, mu, r, bad_s[:2]))
    print(f"[Ap] a1<= {HI} cases(mu,r)={ncase} elapsed={time.time()-t0:.1f}s")
    print(f"[Ap] prod(A') < r/2 (=> W0>2a1, T0 不够长): {lo_bad}  {lo_ex}")
    print(f"[Ap] prod(A') > r   (=> W0<a1, T0 太短)  : {hi_bad}  {hi_ex}")
    print(f"[Ap] T0 非横截: {nonT}  {nonT_ex}")

main()
