import sys, time
from math import gcd
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

a1 = 30030
M = [frozenset(V.factorize(a1))]
Ls = V._prune(V._lcms_of(M))
print("start |Ls|", len(Ls), flush=True)
terms = [a1]
t0 = time.time()
for step in range(1, 3001):
    t = terms[-1]
    nxt = min(((t // L) + 1) * L for L in Ls)
    terms.append(nxt)
    D = frozenset(V.factorize(nxt))
    kill = any(not any(L % q == 0 for q in D) for L in Ls)
    M = V.minimal_sets(M + [D])
    ta = time.time()
    Ls = V._prune(V._lcms_of(M))
    if step % 50 == 0 or step < 5:
        print("step=%-5d |M|=%-4d |Ls|=%-7d kill=%-5s %.2fs (prune %.3fs)" %
              (step, len(M), len(Ls), kill, time.time() - t0, time.time() - ta), flush=True)
    if kill:
        pass
    if len(Ls) > 300000:
        print("BLOWUP at step", step, len(Ls))
        break
