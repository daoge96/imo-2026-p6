import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

g = V.fast_gen(18, 40, stable_S=10 ** 9)
M = [frozenset(V.factorize(18))]
for step, t in enumerate(g["terms"][1:], 2):
    D = frozenset(V.factorize(t))
    ident = not any(S <= D for S in M)
    if ident:
        k = None
        for kk in range(2, 300001):
            if V.in_M(M, kk) and not any(kk % q == 0 for q in D):
                k = kk
                break
        if step <= 8 or t == 32:
            print("step=%d term=%d D=%s 恒等式说=击杀 最小被杀k=%s (k<=3000? %s)"
                  % (step, t, sorted(D), k, (k is not None and k <= 3000)))
    M = V.minimal_sets(M + [D])
