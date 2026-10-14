# Attempt 4: assignment gadgets vs NAE gadgets

## Experimental finding

Random search over `T = 3` configurations (200 trials, `scratchpad/search_nae.py`)
produced several gadgets where the minimum-cost `σ` is strictly non-constant and
the margin to the cheapest constant `σ` exceeds 0.5. Example (`y = (3, 2, 1)`,
conflicts `(0, 1), (0, 2), (1, 2)`):

```
P = [[2.4, 9.61], [4.03, 1.83], [1.87, 8.63]]
sigma=(0,0,0)  cost 0.936   SAME
sigma=(0,0,1)  cost 0.266   NAE
sigma=(0,1,0)  cost 1.047   NAE
sigma=(0,1,1)  cost 0.111   NAE
sigma=(1,0,0)  cost 3.519   NAE
sigma=(1,0,1)  cost 2.849   NAE
sigma=(1,1,0)  cost 3.519   NAE
sigma=(1,1,1)  cost 2.583   SAME
```

The minimum is `(0, 1, 1)` at 0.111; the two SAME patterns cost 0.936 and 2.583.
So the SAME patterns are NOT symmetric and the gadget does NOT behave as a "NAE
gadget" (where SAME patterns are expensive and NAE patterns are uniformly cheap).

**What the gadget does encode: an ASSIGNMENT.** It forces `σ` to a specific pattern
(here `(0, 1, 1)`), with large margins to all other patterns.

## Why assignment gadgets alone do not give NP-hardness

Each gadget pins its own `σ` conflicts to a specific pattern. If we combine
several gadgets sharing conflicts, consistency is a classical CSP: "assign Boolean
values to shared variables so that each gadget's forced values agree with its
neighbours". Such a CSP, where each constraint uniquely determines all its
variables, is solved in polynomial time by unit propagation. No NP-hardness
transfer.

## Chain is ferromagnetic

The pure `y`-chain `t > s > u` (so conflicts `(t, s), (t, u), (s, u)`) is
**ferromagnetic**: `σ = (0, 0, 0)` or `(1, 1, 1)` is strictly cheapest. The
intuition: the chain constraints are transitively closed, so pooling all three
points on one coordinate costs the same as a pair pool. Splitting across
coordinates duplicates the pool cost. Thus chain gadgets cannot encode NAE.

## What a NAE gadget would need

For an NAE encoding we need a gadget on three conflicts with cost function
`f(σ) ≈ M · 𝟙[σ constant]`, i.e. BOTH all-zeros and all-ones strictly expensive,
all six non-constant patterns cheap and roughly equal. In our ρ_dom structure:

* `g_0(all 3 conflicts) ≫ g_0(≤ 2 conflicts)` AND
* `g_1(all 3 conflicts) ≫ g_1(≤ 2 conflicts)`.

With the chain structure of a `y`-chain this cannot happen: 2 of 3 chain
constraints already imply the third. So the gadget must use **non-chain conflict
sets**: three conflicts whose edge set in the conflict tournament is NOT a
transitive triangle.

In a tournament, three edges form a non-transitive triangle only if their y-ranks
are arranged with a tie. Example: `y = (3, 1, 1)` has only two conflicts
`(0, 1), (0, 2)`; no three. To get three independent conflicts we need more
points. A "star" gadget with one `y`-maximum and multiple `y`-minima gives
multiple conflicts from the same vertex but no inter-conflict constraints among
them. This can be a NAE-style target.

## Next step not yet done

Build a star gadget: one centre with `y` large, three leaves with equal `y`.
Three conflicts `(centre, leaf_i)` share only the centre. The three constraints
`q_c^i ≤ q_leaf_i^i` on coord 0 (if all `σ = 0`) interact through `q_c^0`. The
all-same cost: lower `q_c^0` below all three leaves, expensive. Splitting:
lower `q_c^0` below two leaves, lower `q_c^1` below one leaf (or vice versa);
cheaper if the leaves are placed anisotropically.

This is the most concrete remaining angle for a NAE/forbid gadget. It is not
yet tested.
