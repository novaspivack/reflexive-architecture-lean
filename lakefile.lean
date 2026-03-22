import Lake
open Lake DSL

package «reflexive-architecture» where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

require nems_lean from "../../nems-lean"
require infinity_compression from "../../infinity-compression/infinity-compression-lean"

@[default_target]
lean_lib «ReflexiveArchitecture» where
  roots := #[`ReflexiveArchitecture]
