"""d17_Lcheck: 独立复核 Lead 的 (L) 线索。

对每个 a1<=HI 与每个使 E_p != empty 的素数 p（p 遍历窗口内所有 mu in M 的素因子）：
  sigma = nu_p := min{mu in M : p | mu},  tau := sigma/p,
  Q := {q prime : q | tau, q | a1},
  ratio := min_{q in Q} a1*q/sigma        # (L) 等价于 ratio >= 1
报告：实例数、|Q|=0 的实例数、|Q|!=0 的实例数、最紧 ratio（含 argmin）、反例（ratio<1）。
另核对 Lead 的等价改写：(L) <=> p*(tau/q) <= a1（对 q in Q）。
用法: python d17_Lcheck.py HI [mult]
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
    seq_last = a1
    fs1 = fac(a1)
    Z = {q: 0 for q in fs1}
    M = minimize(fs1)
    n = 1
    full = 1
    while seq_last <= B:
        k = seq_last + 1
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
        seq_last = k
        for q in list(Z.keys()):
            if q not in D:
                Z[q] |= (1 << n)
        for q in D:
            if q not in Z:
                Z[q] = (1 << n) - 1
        n += 1
        full = (full << 1) | 1
    return [m for m in M if m <= B]

def main():
    HI = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    mult = float(sys.argv[2]) if len(sys.argv) > 2 else 6.0
    t0 = time.time()
    nQ0 = nQpos = ntot = 0
    worst = None          # 最紧 ratio
    bad = []              # ratio < 1
    Q0_notPdiv = []       # |Q|=0 但 p 不整除 a1（Lead 说应为空）
    for a1 in range(2, HI + 1):
        B = int(mult * a1) + 8
        M = run(a1, B)
        D1 = set(fac(a1))
        nu = {}
        for mu in M:
            for p in fac(mu):
                if p not in nu or mu < nu[p]:
                    nu[p] = mu
        for p, sigma in nu.items():
            ntot += 1
            tau = sigma // p
            Q = [q for q in fac(tau) if q in D1]
            if not Q:
                nQ0 += 1
                if p not in D1:
                    Q0_notPdiv.append((a1, p, sigma, tau))
                continue
            nQpos += 1
            best = None
            for q in Q:
                r = a1 * q / sigma
                if best is None or r < best[0]:
                    best = (r, q)
            if worst is None or best[0] < worst[0]:
                worst = (best[0], a1, p, sigma, tau, best[1])
            if best[0] < 1.0:
                bad.append((a1, p, sigma, tau, best[1], best[0]))
    print(f"[L] a1<= {HI} mult={mult} elapsed={time.time()-t0:.1f}s")
    print(f"[L] instances (a1,p) with E_p!=empty: {ntot}")
    print(f"[L] |Q|=0: {nQ0}  (其中 p 不整除 a1 的: {len(Q0_notPdiv)} {Q0_notPdiv[:8]})")
    print(f"[L] |Q|>0: {nQpos}")
    print(f"[L] tightest min_q a1*q/sigma = {worst[0]:.6f}  argmin: a1={worst[1]} p={worst[2]} sigma={worst[3]} tau={worst[4]} q={worst[5]}")
    print(f"[L] counterexamples (ratio<1): {len(bad)} {bad[:10]}")

main()
