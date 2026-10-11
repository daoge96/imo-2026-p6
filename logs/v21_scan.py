"""v21 独立扫描：a_1<=500 全扫（用自己的 verify.py 实现，不照抄 d16_*/d17_*/claimB_scan）。

指标：
  max mu/(2a1)、max p/a1、R 实例、E_p 非空对数、max nu_p/(a1 p)、B∈{3a1,6a1} 稳定性。
另：对若干 a_1 直接检验 16.8（R ⇒ v2 引理 5.1 假）与 16.9 的等价形式。
"""
import json
import sys
import time
from math import gcd

sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

MAXA = 500
out = []
t0 = time.time()
worst_mu = (0.0, None)
worst_p = (0.0, None)
worst_nup = (0.0, None)
R_instances = []
npairs = 0
stab3 = stab6 = 0
maxmu = 0
for a1 in range(2, MAXA + 1):
    g = V.fast_gen(a1, 60000, stable_S=400)
    M = g["M"]
    KB = max(4000, 4 * a1)
    B = V.minimal_elements(M, a1, KB)          # 整除极小元（= 16/17 文的 M）
    two = 2 * a1
    for mu in B:
        maxmu = max(maxmu, mu)
        if mu / two > worst_mu[0]:
            worst_mu = (mu / two, (a1, mu, V.factorize(mu)))
        for p in V.factorize(mu):
            if p / a1 > worst_p[0]:
                worst_p = (p / a1, (a1, p, mu))
            if p > 2 * a1 and two < mu <= a1 * p:
                R_instances.append((a1, p, mu))
    primes = sorted({p for mu in B for p in V.factorize(mu)})
    for p in primes:
        sub = [mu for mu in B if mu % p == 0]
        npairs += 1
        nu_p = min(sub)
        if nu_p / (a1 * p) > worst_nup[0]:
            worst_nup = (nu_p / (a1 * p), (a1, p, nu_p))
        # R': E_p != empty, p>2a1, nu_p>2a1
    # 稳定性：B 的上界是否随扫描界 B 变大而变（用 3a1 / 6a1 判据）
    if maxmu > 3 * a1:
        stab3 += 1
    if maxmu > 6 * a1:
        stab6 += 1
    if g["stable"] and not B:
        out.append((a1, "empty-B"))
print("cases=%d  time=%.1fs" % (MAXA - 1, time.time() - t0))
print("max mu/(2a1) = %.4f at %s" % (worst_mu[0], worst_mu[1]))
print("max p/a1     = %.4f at %s" % (worst_p[0], worst_p[1]))
print("R instances  = %d  %s" % (len(R_instances), R_instances[:10]))
print("E_p pairs    = %d" % npairs)
print("max nu_p/(a1 p) = %.4f at %s" % (worst_nup[0], worst_nup[1]))
print("max mu/a1    = %.4f" % (maxmu / max(2, 2)))
print("a1 with maxmu>3a1: %d ; >6a1: %d" % (stab3, stab6))
json.dump(dict(cases=MAXA - 1, worst_mu=worst_mu, worst_p=worst_p,
               R_instances=R_instances, npairs=npairs, worst_nup=worst_nup,
               stab3=stab3, stab6=stab6, empty_B=out, seconds=time.time() - t0),
          open(r"D:\OneDrive\Desktop\dsh\imo-p6\logs\v21_scan.json", "w", encoding="utf-8"),
          ensure_ascii=False, indent=1, default=str)
