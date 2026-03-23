/-
  EPIC_019 — Theorem U4 (classical): minimal exhaustion (injective `compare`) or
  non-exhaustion (nontrivial fiber). This is the abstract “collapse-or-fiber” law at
  the level of **comparison alone**, assuming classical logic for the proposition
  `Function.Injective S.compare`.
-/

import Mathlib.Logic.Basic
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem
import ReflexiveArchitecture.Universal.ExhaustionDefinitions

universe u

namespace ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-- **U4 (classical).** Either `compare` is injective (no upstairs multiplicity over bare)
or there exist distinct realizations with the same bare image. -/
theorem minimal_exhaustive_or_nonExhaustive_classical :
    MinimalExhaustive S ∨ NonExhaustive S := by
  rcases Classical.em (MinimalExhaustive S) with h | h
  · exact Or.inl h
  · exact Or.inr ((nonExhaustive_iff_not_minimal S).2 h)

end ReflexiveArchitecture.Universal
