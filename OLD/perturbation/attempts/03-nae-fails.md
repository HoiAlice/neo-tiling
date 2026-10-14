# Attempt 3: NAE-3SAT via forced triangles — does not work out of the box

Idea suggested in `scratchpad/REDUCTION-SOURCES.md`: encode NAE-3SAT via "forced
triangles" from `y`-chains `t > s > u`, hoping that the cost of "all three conflicts
on the same coordinate" is strictly larger than the mixed configurations. If true,
each clause becomes a chain and the "all three same" penalty forces NAE.

## What was tested

Explicit `d = 2`, `T = 3`, `P = ((1, 1), (2, 2), (3, 3))`, `y = (1, 2, 3)`. All three
conflicts `(1, 0), (2, 0), (2, 1)` are strict dominance obstructions. For each
`σ ∈ {0, 1}^3`:

| σ        | coord 0 cost | coord 1 cost | total   |
|----------|--------------|--------------|---------|
| (0,0,0)  | 1.499        | 0            | **1.499** |
| (1,1,1)  | 0            | 1.499        | **1.499** |
| (0,0,1)  | 1.499        | 0.449        | 1.948   |
| (0,1,0)  | 1.499        | 0.449        | 1.948   |
| (1,0,0)  | 1.499        | 0.449        | 1.948   |
| (0,1,1)  | 0.449        | 1.499        | 1.948   |
| (1,0,1)  | 0.449        | 1.499        | 1.948   |
| (1,1,0)  | 0.449        | 1.499        | 1.948   |

(Numbers from the `iso_scipy.py` tool. The coord 0 pool with `(0, 0, 1)` happens to
cost the same `1.499` as the chain pool `(0, 0, 0)` because the "V" and the chain
both pin two points to the top of the chain.)

**All-same is CHEAPER than any mixed configuration.** The chain is "ferromagnetic",
not antiferromagnetic. The forced-triangle NAE encoding does not work.

## Why the intuition went wrong

The chain `p_t = (c_t, c_t)` with `c_1 < c_2 < c_3` has both coordinates equally
"compressible". Pooling all three to a common value `c` on one coord costs the
same as the two-point pool on that coord (because the chain-pool constraint is
automatically satisfied by two pools) and leaves the other coord free. Splitting
across coordinates duplicates the pool cost on each coord separately.

## What this suggests for the direction of the proof

* To force "NAE" (all-same > mixed), clause gadgets must couple two coords
  **non-chain-like**: some conflicts must prefer one coord, others the other,
  with the NAE pattern breaking a cheaper joint configuration. A pure `y`-chain
  gadget does not achieve this.
* Candidate: a clause gadget where the three conflicts have cost profiles that
  make exactly one coord cheap per conflict, so "all-same" wastes two expensive
  moves. Requires designing `p_t` positions where cost `π` is highly anisotropic.

## Next step (not yet done)

Design an explicit three-conflict gadget with anisotropic costs and verify
numerically that all-same is more expensive than mixed by a margin of `Ω(1)`.
If such a gadget exists, scale it to the full NAE-3SAT reduction.
