import Lake
open Lake DSL

package «reflexive-architecture» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

require nems_lean from git
  "https://github.com/novaspivack/nems-lean.git" @ "d1379b2d6d01b1c652ae65b65e1fab97b9b6b6b3"

require infinity_compression from git
  "https://github.com/novaspivack/infinity-compression-lean.git" @ "3623c6bff15741ef3796d3901b378dabed18194e"

@[default_target]
lean_lib «ReflexiveArchitecture» where
  roots := #[`ReflexiveArchitecture]
