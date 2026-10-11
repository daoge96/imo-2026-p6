"""d17_bpp: 独立大范围扫描 (b'') / (b) 与 Q_p 结构。

对每个 a1<=HI、每个使 E_p!=empty 的素数 p（p 遍历窗口内所有 mu in M 的素因子）：
  sigma := nu_p = min{mu in M : p | mu};  tau := sigma/p;  Q := {q prime: q | tau, q | a1}
统计：
  (i)  max p/a1 与 argmax;  count(p>a1);  count(p>2a1)                [=(b) 与更强形式]
  (ii) max nu_p/(2a1) 与 argmax;  count(nu_p>2a1);  count(nu_p>a1)     [=(b'') 与 (L) 的分母]
  (iii) Q=0 <=> p|a1 的列联表：c00(Q=0,p|a1), c01(Q=0,p∤a1), c10(Q≠0,p|a1), c11(Q≠0,p∤a1)
  (iv) max p/a1 限制在 Q!=∅ 的实例;  max sigma/(a1*q) 等 (L) 余量表
  (v) "硬情形"形状计数：a1=p*q（p,q 素）、sigma=a1、tau=q
速度: 用增量 min A_n + 位掩码; B=mult*a1, mult>=3 以保证窗口内 M 完整（观测 max mu/(2a1)=0.724）。
用法: python d17_bpp.py HI [mult] [--step=k]
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
    HI = int(sys.argv[1]) if len(sys.argv) > 1 else 3000
    mult = float(sys.argv[2]) if len(sys.argv) > 2 else 3.0
    step = 1
    for a in sys.argv[1:]:
        if a.startswith("--step="):
            step = int(a.split("=")[1])
    t0 = time.time()
    ntot = 0
    maxPa = (0.0, 0, 0, 0)        # max p/a1
    maxS2 = (0.0, 0, 0, 0)        # max sigma/(2a1)
    np_gt_a = 0; np_gt_2a = 0; ns_gt_a = 0; ns_gt_2a = 0
    c00 = c01 = c10 = c11 = 0     # Q=0 & p|a1 ; Q=0 & p∤a1 ; Q≠0 & p|a1 ; Q≠0 & p∤a1
    maxPaQ = (0.0, 0, 0, 0)       # max p/a1 among Q≠∅
    minRatio = (1e18, 0, 0, 0, 0) # min a1*q/sigma among Q≠∅
    hard = 0; hardlist = []
    for a1 in range(2, HI + 1, step):
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
            rp = p / a1
            if rp > maxPa[0]:
                maxPa = (rp, a1, p, sigma)
            rs2 = sigma / (2 * a1)
            if rs2 > maxS2[0]:
                maxS2 = (rs2, a1, p, sigma)
            if p > a1: np_gt_a += 1
            if p > 2 * a1: np_gt_2a += 1
            if sigma > a1: ns_gt_a += 1
            if sigma > 2 * a1: ns_gt_2a += 1
            tau = sigma // p
            Q = [q for q in fac(tau) if q in D1]
            pdiv = (p in D1)
            if not Q:
                if pdiv: c00 += 1
                else: c01 += 1
            else:
                if pdiv: c10 += 1
                else: c11 += 1
                if rp > maxPaQ[0]:
                    maxPaQ = (rp, a1, p, sigma)
                for q in Q:
                    rr = a1 * q / sigma
                    if rr < minRatio[0]:
                        minRatio = (rr, a1, p, sigma, q)
                if len(fac(a1)) == 2 and p in fac(a1) and sigma == a1 and tau > 1 and len(fac(tau)) == 1:
                    hard += 1
                    if len(hardlist) < 8:
                        hardlist.append((a1, p, sigma, tau))
    print(f"[bpp] a1<= {HI} step={step} mult={mult} instances={ntot} elapsed={time.time()-t0:.1f}s")
    print(f"[bpp] (i)  max p/a1 = {maxPa[0]:.6f} at a1={maxPa[1]} p={maxPa[2]} sigma={maxPa[3]};  #p>a1={np_gt_a};  #p>2a1={np_gt_2a}")
    print(f"[bpp] (ii) max sigma/(2a1) = {maxS2[0]:.6f} at a1={maxS2[1]} p={maxS2[2]} sigma={maxS2[3]};  #sigma>a1={ns_gt_a};  #sigma>2a1={ns_gt_2a}")
    print(f"[bpp] (iii) c(Q=0,p|a1)={c00}  c(Q=0,p!|a1)={c01}  c(Q!=0,p|a1)={c10}  c(Q!=0,p!|a1)={c11}")
    print(f"[bpp] (iv) max p/a1 among Q!=0 = {maxPaQ[0]:.6f} at a1={maxPaQ[1]} p={maxPaQ[2]} sigma={maxPaQ[3]}")
    print(f"[bpp] (iv') min a1*q/sigma among Q!=0 = {minRatio[0]:.6f} at a1={minRatio[1]} p={minRatio[2]} sigma={minRatio[3]} q={minRatio[4]}")
    print(f"[bpp] (v) hard-shape count(a1=pq, sigma=a1, tau=q) = {hard} {hardlist}")

main()
