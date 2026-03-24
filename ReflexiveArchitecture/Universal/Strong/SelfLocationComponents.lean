/-
  EPIC_020 — Decompose `SelfLocationGap` into (i) a **section law** for some `s` and
  (ii) an **off-section witness**. Relate global sections to `StrongExhaustive`.
-/

import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.Forcing.SelfLocationForcing

universe u

namespace ReflexiveArchitecture.Universal.Strong

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Forcing

variable {Bare Realized : Type u}

/-- Some `s` is a global **section** of `compare` (equivalently: `StrongExhaustive`). -/
def HasGlobalSection (S : ReflectiveCertificationSystem Bare Realized) : Prop :=
  ∃ s : Bare → Realized, ∀ b : Bare, S.compare (s b) = b

theorem strongExhaustive_iff_hasGlobalSection (S : ReflectiveCertificationSystem Bare Realized) :
    StrongExhaustive S ↔ HasGlobalSection S := by
  simp [StrongExhaustive, HasGlobalSection, Function.LeftInverse]

/-- For a fixed candidate section `s`: section law + off-section witness. -/
def HasOffSectionWitness (S : ReflectiveCertificationSystem Bare Realized) (s : Bare → Realized) :
    Prop :=
  (∀ b : Bare, S.compare (s b) = b) ∧ ∃ x : Realized, x ≠ s (S.compare x)

theorem selfLocationGap_iff_exists_offWitness (S : ReflectiveCertificationSystem Bare Realized) :
    SelfLocationGap S ↔ ∃ s : Bare → Realized, HasOffSectionWitness S s :=
  Iff.rfl

end ReflexiveArchitecture.Universal.Strong
