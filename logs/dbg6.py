import sys, time
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

for a1, n in [(2, 60), (15, 60), (2310, 60), (999983, 60), (3**12, 60)]:
    t0 = time.time()
    g = V.choice_gen(a1, n, stable_S=400)
    print("choice_gen a1=%d n=%d -> terms=%d |Ls|=%d kill=%d %.3fs" %
          (a1, n, len(g["terms"]), len(g["Ls"]), g["nkill"], time.time() - t0), flush=True)

t0 = time.time()
for a1 in list(range(2, 31)) + [35, 105, 2310]:
    naive = V.naive_gen(a1, 60)
    cg = V.choice_gen(a1, 60, stable_S=10**9)["terms"]
    wg = V.window_gen(a1, 4096, 60, stable_S=10**9, W_cap=1 << 22)["terms"]
    assert naive == cg, (a1, "naive/choice mismatch")
print("warm ok %.3fs" % (time.time() - t0), flush=True)
