import sys
sys.path.insert(0, r"D:\OneDrive\Desktop\dsh\imo-p6")
import verify as V

a1 = 15
res = V.stabilize(a1, 1024, nterms_cap=4000, stable_S=300)
terms = res["terms"]
inA = V.in_Ainf_factory(terms)
base = terms[-1]
Wk = 98
bits = bytearray(Wk)
B = V.minimal_elements(a1, terms, 20000)
for b in B:
    start = ((base // b) + 1) * b
    rhs = b"\x01" * len(range(start, base + Wk, b))
    sl = len(bits[start - base::b])
    print("b=%d start=%d slice_len=%d rhs_len=%d" % (b, start, sl, len(rhs)))
    bits[start - base::b] = rhs
s = bytes(bits)
print("s   :", "".join(str(x) for x in s))
real = bytes(1 if inA(base + q) else 0 for q in range(Wk))
print("real:", "".join(str(x) for x in real))
print("equal:", s == real)
firstbad = next((q for q in range(Wk - 30) if s[q] != s[q + 30]), None)
print("first q with s[q]!=s[q+30]:", firstbad, base + (firstbad or 0))
print("inA(base+q):", inA(base + firstbad), "inA(base+q+30):", inA(base + firstbad + 30))
print("factors:", V.factorize(base + firstbad), V.factorize(base + firstbad + 30))
