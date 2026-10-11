import sys, time
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")
import probe

print("import ok", flush=True)
for (a1, W, Nmax, S) in [(2, 1024, 6, 3), (2, 1024, 20, 5), (2, 1024, 60, 20)]:
    t0 = time.time()
    r = probe.gen(a1, W, Nmax, S)
    print("gen", a1, W, Nmax, S, "->", len(r[0]), r[3], r[4], r[5], "%.3fs" % (time.time() - t0), flush=True)
t0 = time.time()
terms, alive, W, lk, nk, ext = probe.gen(2, 1024, 4000, 300)
print("big gen", len(terms), lk, nk, ext, "%.3fs" % (time.time() - t0), flush=True)
s = probe.mask_to_bits(alive, W)
print("bits", len(s), flush=True)
p = probe.min_period(s)
print("p", p, flush=True)
