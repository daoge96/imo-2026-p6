"""Scratch probe: measure N_0 (last kill step), window period L*, T for various a_1."""
import sys, time
from math import gcd, isqrt


def sieve(n):
    bs = bytearray([1]) * (n + 1)
    bs[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if bs[i]:
            bs[i * i :: i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(2, n + 1) if bs[i]]


PRIMES = sieve(100003)


def factorize(n):
    f = []
    for p in PRIMES:
        if p * p > n:
            break
        if n % p == 0:
            f.append(p)
            while n % p == 0:
                n //= p
    if n > 1:
        f.append(n)
    return f


def rad(n):
    r = 1
    for p in factorize(n):
        r *= p
    return r


_PAT = {}


def _pattern(p, r):
    key = (p, r)
    if key in _PAT:
        return _PAT[key]
    b = bytearray(p)
    for j in range(p):
        i0 = (r - 8 * j) % p
        while i0 < 8:
            b[j] |= 1 << i0
            i0 += p
    out = bytes(b)
    _PAT[key] = out
    return out


def mult_mask(p, lo, n):
    """bit q (0<=q<n) set iff (lo+q) % p == 0."""
    r = (-lo) % p
    nb = (n + 7) // 8
    if p <= 512:
        pat = _pattern(p, r)
        reps = nb // p + 2
        m = int.from_bytes((pat * reps)[:nb], "little")
    else:
        ba = bytearray(nb)
        q = r
        while q < n:
            ba[q >> 3] |= 1 << (q & 7)
            q += p
        m = int.from_bytes(bytes(ba), "little")
    if nb * 8 > n:
        m &= (1 << n) - 1
    return m


def min_period(b):
    n = len(b)
    fail = [0] * n
    k = 0
    for i in range(1, n):
        c = b[i]
        while k and b[k] != c:
            k = fail[k - 1]
        if b[k] == c:
            k += 1
        fail[i] = k
    return n - fail[n - 1]


_EXPAND = [bytes((x >> i) & 1 for i in range(8)) for x in range(256)]


def mask_to_bits(m, n):
    nb = (n + 7) // 8
    raw = m.to_bytes(nb, "little")
    s = b"".join(_EXPAND[x] for x in raw)
    return s[:n]


def union_mask(D, lo, n):
    m = 0
    for p in D:
        m |= mult_mask(p, lo, n)
    return m


def gen(a1, W, Nmax, stable_S=300):
    lo = a1
    alive = (1 << W) - 1
    Dlist = [factorize(a1)]
    alive &= union_mask(Dlist[0], lo, W)
    terms = [a1]
    last_kill = 1
    nkill = 1
    n = 1
    extensions = 0
    while len(terms) < Nmax:
        t = alive >> (terms[-1] - lo + 1)
        if t == 0:
            delta = W
            ext = (1 << delta) - 1
            for D in Dlist:
                ext &= union_mask(D, lo + W, delta)
            alive |= ext << W
            W += delta
            extensions += 1
            continue
        nxt = terms[-1] + 1 + ((t & -t).bit_length() - 1)
        terms.append(nxt)
        n += 1
        D = factorize(nxt)
        Dlist.append(D)
        before = alive
        alive &= union_mask(D, lo, W)
        if alive != before:
            last_kill = n
            nkill += 1
        if n - last_kill >= stable_S:
            break
    return terms, alive, W, last_kill, nkill, extensions


def main():
    cands = [2, 3, 4, 6, 15, 30, 35, 105, 210, 385, 1001, 1155, 2310, 3003, 4096,
             15015, 30030, 59049, 255255, 510510, 999983, 999993, 1048576, 720720,
             333667, 1000003]
    cands = [c for c in cands if c <= 16000000]
    print(f"{'a1':>9} {'rad':>9} {'W':>9} {'Nterm':>6} {'N0':>6} {'nkill':>6} {'p':>9} {'T':>8} {'3p<=W':>6} {'t_s':>7}")
    for a1 in cands:
        R = rad(a1)
        Nmax = 4000
        W0 = max(1024, 4 * R)
        t0 = time.time()
        try:
            terms, alive, W, last_kill, nkill, ext = gen(a1, W0, Nmax, stable_S=300)
            s = mask_to_bits(alive, W)
            p = min_period(s)
            T = bin(alive & ((1 << p) - 1)).count("1")
            dt = time.time() - t0
            print(f"{a1:>9} {R:>9} {W:>9} {len(terms):>6} {last_kill:>6} {nkill:>6} {p:>9} {T:>8} "
                  f"{str(3*p<=W):>6} {dt:>7.2f}  ext={ext}", flush=True)
        except Exception as e:
            print(f"{a1:>9} ERROR {e!r}", flush=True)


if __name__ == "__main__":
    main()
