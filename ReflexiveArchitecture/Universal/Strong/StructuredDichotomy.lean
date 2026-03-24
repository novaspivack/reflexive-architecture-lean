/-
  EPIC_020 — Classical dichotomy **specialized** to `StructuredReflectiveCertificationSystem`.

  Same logical content as EPIC_019 U4 on `S.toRCS`, but typed in the stronger class.
-/

import ReflexiveArchitecture.Universal.Dichotomy
import ReflexiveArchitecture.Universal.Strong.StructuredRCS

universe u

namespace ReflexiveArchitecture.Universal.Strong

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

theorem structured_minimal_or_nonExhaustive [Nontrivial Bare] [Nontrivial Realized]
    (S : StructuredReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S.toRCS ∨ NonExhaustive S.toRCS :=
  minimal_exhaustive_or_nonExhaustive_classical S.toRCS

end ReflexiveArchitecture.Universal.Strong
