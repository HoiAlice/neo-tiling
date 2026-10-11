import Lake
open Lake DSL

package neotiling

@[default_target]
lean_lib NeoTiling where
  globs := #[.andSubmodules `NeoTiling]

-- Polynomial-time (weak) solvability in the plane (`poly-hardness/`).
-- Not a default target: build with `lake build PolyHardness`.
lean_lib PolyHardness where
  srcDir := "poly-hardness/lean"
  globs := #[.andSubmodules `PolyHardness]

-- NP-hardness (Karp) of (weak) solvability in dimension 3, from graph 3-colouring
-- (`np-hardness/`). Not a default target: build with `lake build NPHardness`.
lean_lib NPHardness where
  srcDir := "np-hardness/lean"
  globs := #[.andSubmodules `NPHardness]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"
