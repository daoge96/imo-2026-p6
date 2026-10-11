"""leadH12.py -- H_{1/2}, s=3 残余的约束可满足性扫描.
对 a1 <= HI: c | a1, c <= a1/2; p1 prime > max(2a1/c, 2*sqrt(a1)); p2 prime;
筛选: cp1 > a1^1.5 (残余), 2p2 < cp1, H_{1/2}: c*p2 > a1/2, c*p1 > a1/2, p1*p2*c > a1*p2 ...
报告: 是否存在同时满足 目标 p2 <= 2a1^2/(cp1) 的样本; 以及"最接近违反"的样本.
用法: python leadH12.py LO HI [TOPN]
"""
import sys, math

def spf_sieve(n):
    spf = list(range(n + 1))
    i = 2
    while i * i <= n:
        if spf[i] == i:
            for j in range(i * i, n + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1
    return spf

def primes_upto(n, spf):
    return [p for p in range(2, n + 1) if spf[p] == p]

def divisors(x, spf):
    out = [1]
    while x > 1:
        p = spf[x]; e = 0
        while x % p == 0:
            x //= p; e += 1
        out = [d * p**k for d in out for k in range(e + 1)]
    return out

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    topn = int(sys.argv[3]) if len(sys.argv) > 3 else 8
    spf = spf_sieve(200000)
    bad = []          # 满足残余全部必要约束但目标失败的样本
    surv = 0          # 满足残余约束的样本数
    worst = []
    for a1 in range(lo, hi + 1):
        r = math.isqrt(a1)
        for c in divisors(a1, spf):
            if c < 2 or 2 * c > a1:
                continue
            p1min = max(2 * a1 // c + 1, 2 * r + 1)
            for p1 in primes_upto(min(200000, 40 * a1), spf):
                if p1 < p1min:
                    continue
                if c * p1 <= a1 ** 1.5:
                    continue
                for p2 in primes_upto(min(200000, 2 * a1), spf):
                    if not (2 * p2 < c * p1):
                        continue
                    if not (c * p2 > a1 / 2):
                        continue           # H_{1/2} at p2
                    if not (c * p1 > a1 / 2):
                        continue           # H_{1/2} at p1
                    if not (p1 * p2 > a1 / 2):
                        continue           # H_{1/2} at c
                    surv += 1
                    tgt = 2 * a1 * a1 / (c * p1)
                    if p2 > tgt:
                        bad.append((a1, c, p1, p2, p2 / tgt))
                    worst.append((p2 / tgt, a1, c, p1, p2))
    worst.sort(reverse=True)
    print("survivors (all necessary constraints of the core):", surv)
    print("violating the goal p2 <= 2a1^2/(c p1):", len(bad), bad[:5])
    print("closest to violating (ratio p2/target):")
    seen = set()
    for w in worst:
        key = (w[1], w[2])
        if key in seen:
            continue
        seen.add(key)
        print("  ratio=%.4f a1=%d c=%d p1=%d p2=%d" % w)
        if len(seen) >= topn:
            break

main()
