import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6\logs")
import probe

m = probe.mult_mask(2, 2, 16)
print("m(2,lo=2,16) =", bin(m))
m3 = probe.mult_mask(3, 2, 16)
print("m(3,lo=2,16) =", bin(m3), "expect bits 1,4,7,10,13")
print("pattern(2,0)", probe._pattern(2, 0).hex())
print("pattern(3,1)", probe._pattern(3, 1).hex())

# simulate a1=2 by hand, W=32
W = 32
lo = 2
alive = (1 << W) - 1
for p in probe.factorize(2):
    alive &= probe.mult_mask(p, lo, W)
print("alive after step1 =", bin(alive))
for k in (4, 6, 8, 10, 12):
    D = probe.factorize(k)
    before = alive
    for p in D:
        alive &= probe.mult_mask(p, lo, W)
    print("k=", k, "D=", D, "changed=", alive != before, "alive=", bin(alive))
