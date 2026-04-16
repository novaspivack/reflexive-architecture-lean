import Lake
open Lake DSL

package «reflexive-architecture» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

require nems_lean from git
  "https://github.com/novaspivack/nems-lean.git" @ "d1379b2d6d01b1c652ae65b65e1fab97b9b6b6b3"

require infinity_compression from git
  "https://github.com/novaspivack/infinity-compression-lean.git" @ "ffa29759ea36169b07a9a5a9d43433df47440258"

@[default_target]
lean_lib «ReflexiveArchitecture» where
  roots := #[`ReflexiveArchitecture]
