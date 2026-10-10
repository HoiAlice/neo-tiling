import Lake
open Lake DSL

package neotiling

@[default_target]
lean_lib NeoTiling where
  globs := #[.andSubmodules `NeoTiling]

-- Algorithms for the minimal perturbation problem (covering cuts, set-cover hardness).
-- Not a default target: build with `lake build Algorithms`.
lean_lib Algorithms where
  globs := #[.submodules `Algorithms]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"
