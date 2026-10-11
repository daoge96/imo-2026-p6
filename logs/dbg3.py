import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

print("min_period(b'0101...')", V.min_period(bytes([1,0,1,0,1,0,1,0])))
a1 = 15
res = V.stabilize(a1, 1024, nterms_cap=4000, stable_S=300)
print("terms", len(res["terms"]), "N0", res["last_kill"], "stable", res["stable"])
B = V.minimal_elements(a1, res["terms"], 20000)
print("B", B)
L, T = V.period_from_B(B)
print("L,T", L, T)
base = res["terms"][-1]
print("base", base, "base%30", base % 30)
Wk = 3 * L + 8
bits = bytearray(Wk)
for b in B:
    start = ((base // b) + 1) * b
    bits[start - base::b] = b"\x01" * len(range(start, base + Wk, b))
s = bytes(bits)
print("period 30 ok?", all(s[q] == s[q + 30] for q in range(len(s) - 30)))
print("period 2 ok?", all(s[q] == s[q + 2] for q in range(len(s) - 2)))
print("min_period", V.min_period(s))
# 检查 A_inf 判定与 B
inA = V.in_Ainf_factory(res["terms"])
print("in_Ainf(6,10,15,30,7,4)", [inA(k) for k in (6, 10, 15, 30, 7, 4)])
