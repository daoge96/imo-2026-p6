"""检查两个猜想：
(C1) 持久极小元 b 的出生步 s 很小(有界)；
(C2) 存在素因子 q|b 使 b/q <= a1 (即 b <= a1*q, q<=max D1)。
"""
import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")
from fme_exp2 import build, factor, persistent

def main():
    lo, hi, nmax = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    worst_s, worst_q, bad = [], [], []
    for a1 in range(lo, hi + 1):
        r, pers, newpers = persistent(a1, nmax)
        Pi = max(factor(a1))
        for b in pers:
            st = r["parent"].get(b, (None, 1))[1]
            worst_s.append((st, a1, b))
            best_q = min((b // q, q) for q in factor(b))
            worst_q.append((best_q[0] / a1, a1, b, best_q[1]))
            if best_q[0] > a1:
                bad.append((a1, b, best_q))
    worst_s.sort(reverse=True)
    print("largest birth steps of persistent elements:")
    for st, a1, b in worst_s[:12]:
        print(f"   step={st}  a1={a1} b={b}")
    print("(C2) largest ratio (b/q)/a1 :")
    worst_q.sort(reverse=True)
    for rt, a1, b, q in worst_q[:12]:
        print(f"   ratio={rt:.3f} a1={a1} b={b} q={q}")
    print("violations of C2:", len(bad), bad[:10])

main()
