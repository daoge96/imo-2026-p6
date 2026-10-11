"""leadH12b.py -- 只扫"硬区"：cp1 > a1*2^{omega(a1)/2}（44.2 的自动门槛之外）.
条件: c 素, c | a1, c <= a1/2; p1,p2 素, ∉{c}; cp1 > a1*2^(w/2); 2p2<cp1;
      H_{1/2}: c*p1>a1/2, c*p2>a1/2, p1*p2>a1/2;  目标 p2 <= 2a1^2/(c p1)?
报告幸存数与违反数(附样本). 只限制 p1,p2 <= PMUL*a1.
用法: python leadH12b.py LO HI [PMUL]
"""
import sys, math

def sieve(n):
    isp = bytearray([1]) * (n + 1)
    isp[0] = isp[1] = 0
    i = 2
    while i * i <= n:
        if isp[i]:
            for j in range(i * i, n + 1, i):
                isp[j] = 0
        i += 1
    return isp

def prime_divs(x, isp):
    out = []
    d = 2
    while d * d <= x:
        if x % d == 0 and isp[d]:
            out.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        out.append(x)
    return out

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    pmul = int(sys.argv[3]) if len(sys.argv) > 3 else 10
    N = pmul * hi + 10
    isp = sieve(N)
    primes = [p for p in range(2, N + 1) if isp[p]]
    surv = 0
    bad = []
    for a1 in range(lo, hi + 1):
        D1 = prime_divs(a1, isp)
        w = len(D1)
        thresh = a1 * (2 ** (w / 2.0))
        for c in D1:
            if 2 * c > a1:
                continue
            for p1 in primes:
                if p1 > pmul * a1:
                    break
                cp1 = c * p1
                if cp1 <= thresh:
                    continue
                if not (2 * cp1 > a1):
                    continue
                for p2 in primes:
                    if p2 > 2 * a1:
                        break
                    if p2 == c or p2 == p1:
                        continue
                    if not (2 * p2 < cp1):
                        continue
                    if not (c * p2 > a1 / 2 and p1 * p2 > a1 / 2):
                        continue
                    surv += 1
                    tgt = 2 * a1 * a1 / cp1
                    if p2 > tgt:
                        bad.append((a1, c, p1, p2, round(p2 / tgt, 3)))
    print("hard-region survivors:", surv)
    print("goal violations:", len(bad))
    for b in bad[:12]:
        print("   a1=%d c=%d p1=%d p2=%d ratio=%.3f" % b)

main()
