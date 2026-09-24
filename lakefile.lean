import Lake
open Lake DSL

package neotiling

@[default_target]
lean_lib NeoTiling where
  globs := #[.andSubmodules `NeoTiling]

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.28.0-rc1"
