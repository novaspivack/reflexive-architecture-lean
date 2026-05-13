import Lake
open Lake DSL

package «reflexive-architecture» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require nems_lean from git
  "https://github.com/novaspivack/nems-lean.git" @ "main"

require infinity_compression from git
  "https://github.com/novaspivack/infinity-compression-lean.git" @ "main"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

@[default_target]
lean_lib «ReflexiveArchitecture» where
  roots := #[`ReflexiveArchitecture]
