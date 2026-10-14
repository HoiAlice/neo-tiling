"""np_tiling.py -- explicit tilings of a wire stretch between two cores (closes LOCALITY.md open item 2) + independent verifier.
Stretch: core switch w_0, plain switches w_1..w_r (r >= 2), core switch w_{r+1}; links l_i = (w_i,w_{i+1}), i = 0..r.
Optional single weak link l_j with 2 <= j <= r-2 (j is the index of its left switch).
P2 = {K, K'} + partition of w_1..w_r ;  P1 = {K^+ ∋ w_1, K'^+ ∋ w_r} + blocks on w_2..w_{r-1}.
Required: every strong link inside a block of P1 or P2 (l_0 in K^+, l_r in K'^+ count), weak link inside a block of both, all plain blocks of size <= 4."""
def split(n):
    """partition n >= 2 consecutive switches into blocks of size 2 (and one 3 if n odd); n == 0 -> []"""
    if n == 0: return []
    assert n >= 2
    return [2] * (n // 2 - 1) + [2 + n % 2 + 0] if n % 2 == 0 else [2] * ((n - 3) // 2) + [3]
def construct(r, j=None):
    """returns (P2 blocks, P1 plain blocks) as lists of (first,last) switch indices"""
    if j is None:
        sizes = split(r)
    else:
        a, b = j - 1, r - j - 1           # switches left of the weak pair, right of it
        mid = [2]
        if a == 1 and b == 1: mid = [4]; a = b = 0   # r = 4, j = 2: one block {w_1..w_4}
        elif a == 1: mid = [3]; a = 0       # absorb w_1 : block {w_1,w_2,w_3}  (j == 2)
        elif b == 1: mid = [3]; b = 0       # block {w_{r-2}, w_{r-1}, w_r}
        sizes = split(a) + mid + split(b)
        if a == 0 and mid == [3] and j == 2: pass
    blocks = []; p = 1
    for k in sizes: blocks.append((p, p + k - 1)); p += k
    assert p == r + 1, (r, j, sizes)
    # P1: bridging pairs over every boundary link + weak pair, merged where overlapping
    links = set()
    for (a_, b_), (c_, d_) in zip(blocks, blocks[1:]): links.add(b_)        # boundary link l_{b_} = (w_{b_}, w_{b_+1})
    if j is not None: links.add(j)
    comps = []; cur = None
    for i in sorted(links):
        if cur and i == cur[1]: cur = (cur[0], i + 1)
        else:
            if cur: comps.append(cur)
            cur = (i, i + 1)
    if cur: comps.append(cur)
    return blocks, comps
def verify(r, j=None, smax=4):
    P2, P1 = construct(r, j)
    # partition checks
    assert sorted(i for a, b in P2 for i in range(a, b + 1)) == list(range(1, r + 1))
    P1all = [(1, 1)] + [c for c in P1] + [(r, r)]      # K^+ contributes w_1 and w_r (as 'cores' here)
    used = [i for a, b in P1all for i in range(a, b + 1)]
    assert len(used) == len(set(used)), "P1 blocks overlap"
    assert all(2 <= a and b <= r - 1 for a, b in P1), "P1 plain block touches w_1 or w_r"
    assert all(b - a + 1 <= smax for a, b in P1 + P2)
    for i in range(1, r):                                  # links l_1..l_{r-1}
        in2 = any(a <= i and i + 1 <= b for a, b in P2); in1 = any(a <= i and i + 1 <= b for a, b in P1)
        if i == j: assert in1 and in2, ("weak", r, j)
        else: assert in1 or in2, ("link", r, j, i)
    return P2, P1
if __name__ == "__main__":
    cnt = 0
    for r in range(2, 61):
        verify(r, None); cnt += 1
        for j in range(2, r - 1):
            verify(r, j); cnt += 1
    print("verified", cnt, "(r, weak-position) cases, r <= 60")
    for r, j in [(2, None), (3, None), (5, None), (6, None), (8, 4), (9, 4), (7, 2), (7, 5), (11, 5)]:
        print("r", r, "weak", j, verify(r, j))
