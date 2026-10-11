"""lead_Hnear2.py -- 快速版 H-接近度扫描（带进度输出）.
对每个 a1<=HI: 建 A_∞ 窗口、取极小元 M，报告 max_mu min_{p|mu} mu/(p*a1) 与 H 实例数.
优化: sieve 只建一次; 用候选表候替代 O(B) 全扫.
用法: python lead_Hnear2.py LO HI [STEP_PRINT]
"""
import sys

def main():
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    step = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    Bmax = 3 * hi + 60
    spf = list(range(Bmax + 1))
    i = 2
    while i * i <= Bmax:
        if spf[i] == i:
            for j in range(i * i, Bmax + 1, i):
                if spf[j] == j:
                    spf[j] = i
        i += 1

    def supp(x):
        out = []
        while x > 1:
            p = spf[x]
            out.append(p)
            while x % p == 0:
                x //= p
        return out

    worst = (0.0,)
    nH = 0
    tot = 0
    for a1 in range(lo, hi + 1):
        B = 3 * a1 + 60
        alive = bytearray([1]) * (B + 1)
        alive[0] = alive[1] = 0
        cand = list(range(a1, B + 1))          # 候选（只保留 >= a1）
        terms = [a1]
        # 初始：加 a1
        for q in supp(a1):
            for j in range(a1, B + 1, q):
                alive[j] = 0
        alive[a1] = 1
        alive2 = bytearray([1]) * (B + 1)
        alive2[0] = alive2[1] = 0
        marks = bytearray([0]) * (B + 1)
        for q in supp(a1):
            for j in range(q, B + 1, q):
                marks[j] = 1
        alive2[a1] = 1
        alive2[1] = 0
        cur = a1
        while True:
            nxt = None
            k = cur + 1
            while k <= B:
                if alive2[k] and marks[k]:
                    nxt = k
                    break
                if alive2[k] and not marks[k]:
                    # 不相容 → 死
                    alive2[k] = 0
                k += 1
            if nxt is None:
                break
            terms.append(nxt)
            for q in supp(nxt):
                for j in range(q, B + 1, q):
                    marks[j] = 1
            for j in range(2, B + 1):
                pass
            # 重新计算 alive2: 与全部已加素数命中
            alive2 = bytearray([1]) * (B + 1)
            alive2[0] = alive2[1] = 0
            hit = bytearray([0]) * (B + 1)
            for tm in terms:
                for q in supp(tm):
                    for j in range(q, B + 1, q):
                        hit[j] = 1
            for j in range(2, B + 1):
                if not hit[j]:
                    alive2[j] = 0
            cur = nxt
        M = []
        for k in range(2, B + 1):
            if alive2[k] and not any(k % m == 0 for m in M):
                M.append(k)
        D1 = set(supp(a1))
        for mu in M:
            S = supp(mu)
            r = min(mu / (p * a1) for p in S)
            if r > 1:
                nH += 1
            tot += 1
            if r > worst[0]:
                worst = (r, a1, mu, sorted(S), len(S))
        if a1 % step == 0:
            print("a1=%d done | mu_seen=%d H=%d worst=%.4f %s" % (a1, tot, nH, worst[0], worst[1:]), flush=True)
    print("FINAL: mu=%d H=%d max_ratio=%.6f argmax=%s" % (tot, nH, worst[0], worst[1:]), flush=True)

main()
