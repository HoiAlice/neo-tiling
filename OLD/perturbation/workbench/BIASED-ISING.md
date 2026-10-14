# Biased switches (planar Ising with field?) -- results

Scripts (all in gad/): bias.py (table + Ising fit helpers), b2.py (pairs), b3.py (chains), b4.py/b5.py/b6.py/b7.py/b8.py
(rho_dom vs weak solvability), b9.py (triangle). Conventions as GADGET-D2.md: eps=0.2 per grid step, cost e^{|dlog|}-1,
rho_dom = exact MILP+polish (core.solve_dom). s_i = 1-2*sigma_i; fits E = E0 + sum h_i s_i + sum J_ij s_i s_j
(J>0 = antiferro, J<0 = ferro). "solvable" = flow_lp weak solvability of the margin-1e-6 optimum Q (=> rho_full = rho_dom there).

## 0. Correction to the premise
Ising with ferromagnetic couplings and fields of any sign is submodular = min-cut = POLYNOMIAL. Likewise AF couplings on a
bipartite graph (gauge s_i -> (-1)^i s_i turns it into ferro + field). Hardness with a field needs FRUSTRATION (odd cycle of AF
edges / mixed-sign J on a cyclic structure), as in Barahona's +-J planar-with-field construction (I recall his couplings are
mixed sign; not re-verified). So "biased switch + ferro" alone is not enough.

## 1. Biased switch: YES, trivially, by asymmetric gap (b)
Switch gap (g0,g1) grid steps, y=(2,1). sigma=0 closes coordinate 0, cost 2(e^{0.2 g0/2}-1); sigma=1 cost 2(e^{0.2 g1/2}-1).
  (4,4): 0.98365 / 0.98365     (4,5): 0.98365 / 1.29744 (h=0.1569)     (4,6): 0.98365 / 1.64424     (5,4): mirrored.
Sign of the field = which gap is longer, magnitude continuous in the gap difference.
(a) y-weights do NOT change the dom costs at all (only the order y_t>y_s enters), so they cannot bias; but see section 3, they matter for rho_full.
(c),(d) anchors/triplets: not needed, not explored.

## 2. Stacking
Antiferro chain, offsets (-3,+3), alternating gaps (4,5),(5,4),(4,5),...:
  n=4: exact NN Ising over all 16 patterns, E0=4.86418 h=(-.1569,+.1569,-.1569,+.1569) J=(.0984,.1052,.0984) max resid 1.3e-10; min at 0101 = 3.93460.
  n=5: same with J=(.0984,.1052,.0984,.1052), resid 1.9e-8; min 01010 = 4.91825.
  (this is the gauge image of ferro + uniform field, so it is only the polynomial case.)
Uniform gaps (4,5) on the chain: NOT Ising (n=5 resid 7.5e-2) -- boundary/context effects; alternation (5,4) is what makes it clean.
Ferro (NE offsets (1,1),(2,2),(3,3),(5,5)) chains: NOT Ising. NN fit residuals 0.39 (n=3), 0.84 (n=4), 1.43 (n=5) at equal y-levels; with
y levels decreasing along NE (c_i=-0.5 i) still 0.18-0.31 (n=4, all-pairs 0.09-0.17). Every comparable pair interacts. Pairs alone are fine
(e.g. offset (1,1), gaps (4,5),(4,5): T00=1.9972, 01=2.8939, 11=2.6279). The claim "ferro chain fits exact Ising" is NOT confirmed
for NE offsets; ferro must be built as an even AF path (min over the middle spin gives effective ferro, not tested).

## 3. rho_dom vs rho_full -- real obstruction found, cured by y-ratio
AF n=4 alternating-gap chain, 2:1 y-levels: dom-optimal Q (rho_dom=3.93460) is NOT weakly solvable (even at margins up to 3e-2);
8 of 16 switch patterns fail. So rho_full > rho_dom for biased chains at y=(2,1)! (Symmetric gaps and n<=3 are fine.)
Cure: y_top/y_bot closer to 1. Same Q, y=(r,1): solvable for r=1.01,1.2,1.5; fails r>=1.9.
Full tables of 2^n dom-optimal patterns checked solvable: n=4 alt: 16/16 at r=1.1,1.2,1.5; n=5 alt: 32/32 at r=1.1,1.2 (26/32 at 1.5);
n=5 uniform (4,5): 32/32 at 1.1,1.2 (21/32 at 1.5). So with y_top=1.2,y_bot=1 rho_full=rho_dom on everything tested (upper bound via solvable Q).
Single biased switch and biased AF pair at y=(2,1): solvable.

## 4. Frustration + bias (planar triangle)
Switches at (0,0),(-2,3),(-5,5) (all pairwise AF, planar triangle, no crossing):
  gaps all (6,6): exact pairwise Ising (3-body resid 2.7e-12), E0=5.3785, J01=.1631 J02=.1708 J12=.1631, h~(-.028,0,.028); table 000=111=5.8755, rest 5.15-5.26 (frustrated, NAE-like).
  gaps all (6,7): h~-0.2, but 3-body resid 3.5e-2.  (6,7),(7,6),(6,7): resid 2.95e-2.  one biased (third (6,7)): h3=-.1733, resid 8.5e-4.
So bias is compatible with frustrated triangle only approximately: a 3-body term ~1-3e-2 (vs J~0.17, h~0.2) appears; for one small bias it is 8.5e-4.
Not done: embed C4/triangulated lattice with fields and compare with Ising ground state; no exact planar-with-field reduction constructed.

## Verdict
Biased switch exists (asymmetric gap, continuous field of either sign). Clean stacking shown for AF chains with alternating gaps (resid<=2e-8),
frustrated triangles with symmetric gaps (resid 3e-12). Not established: (i) ferro couplers as exact Ising (NE offsets are not; use AF 2-paths),
(ii) pairwise exactness for biased frustrated structures (3-body 1e-3..3e-2), (iii) a planar reduction proper (needs triangulated AF lattice + fields,
where every edge strength must be exactly controlled), (iv) rho_full=rho_dom must be re-checked per instance (fails at y=(2,1), holds at y_top~1.2).

## Follow-up (ferro/AF mixing; scripts gad/c1.py, gad/c2.py)
1. Ferro, symmetric gaps (6,6), NE triples: exact pairwise (resid <=1.2e-14). Steps (1,1): J=(-.3571,-.2959,-.3571); (2,2): (-.4111,-.3006,-.4111);
   (4,4) and (7,7): all three J=-.4111 (saturated, NOT decaying with distance: every comparable pair at equal y interacts).
   With biased gaps ferro is not exact (see section 2). AF 2-path (0,0),(-3,3),(-6,6) gap 6: exact, J=(.2575,.0923,.2575) -> effective ferro after eliminating middle.
2. Mixed triple S0(0,0),S1(2,2),S2(5,-3), gaps (6,6): exact (resid 7.3e-11), J01=-.381 (ferro), J02=J12=+.1749 (AF), h~(-.034,+.034,0). Not frustrated
   (ferro+AF+AF, sign product +). Other mixed placements ((2,2),(-3,3) ; (4,4),(-3,3)) are NOT pairwise (resid 1.6e-2, 1.8e-2).
   Ferro-ferro-AF triangle is impossible (comparability transitive); frustration needs an all-AF triangle.
3. 4th switch scan next to the exact mixed triple, all integer offsets in [-8,8]^2 (263 positions): only 2 exact fits, (-8,8) and (-7,8), and there the new switch
   has all J=0 (isolated), i.e. trivial. Any 4th switch that actually interacts breaks pairwise Ising (resid >1e-7). AF triangle + pendant (12 variants, with/without
   bias): resid 0.04-0.09. So NO exact pairwise mixed-sign frustrated 4-switch configuration found; step 3 fails, no Barahona reduction.
   Rho_dom=rho_full not re-checked for these (not needed since they fail).
Reason: couplings are geometric and all-to-all among switches within range / comparable, with 3-body corrections as soon as a switch interacts with >=3 others.
