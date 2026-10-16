import Lake
open Lake DSL

/-- Lean 4 + Mathlib formalization accompanying the paper (`paper/tex`).
Submodules: `Core` (solvability and weak solvability criteria), `Planar` (d = 2, chain graph and
flow LP), `Hardness` (d = 3, Karp reduction from 3-colouring), `Perturbation` (box theorem, least
radius, breakpoints, weighted metric), `Lp` (reduction of the least l_p price perturbation to the
box oracle, certificate cuts). -/
package neotiling

@[default_target]
lean_lib NeoTiling where
  globs := #[.andSubmodules `NeoTiling]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"
