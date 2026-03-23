/-
  EPIC_019 Phase I — minimal vs strong exhaustion, non-exhaustion, canonical region.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem
import ReflexiveArchitecture.Universal.FiberBasics

universe u

namespace ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-- Region of bare objects marked canonical (intended “bare certificate” locus). -/
def CanonicalRegion : Set Bare :=
  { b | S.Canonical b }

@[simp]
theorem mem_canonicalRegion_iff {b : Bare} : b ∈ CanonicalRegion S ↔ S.Canonical b :=
  Iff.rfl

/-- Minimal exhaustion: comparison does not identify distinct realizations. -/
def MinimalExhaustive : Prop :=
  Function.Injective S.compare

/-- Strong exhaustion: a global section `s` with `compare ∘ s = id` (every bare
certificate is realized; `compare` is surjective). -/
def StrongExhaustive : Prop :=
  ∃ s : Bare → Realized, Function.LeftInverse S.compare s

/-- Non-exhaustion: distinct realizations share a certified image (nontrivial fiber). -/
def NonExhaustive : Prop :=
  ∃ x y : Realized, x ≠ y ∧ S.compare x = S.compare y

theorem nonExhaustive_iff_not_minimal : NonExhaustive S ↔ ¬MinimalExhaustive S := by
  simp [NonExhaustive, MinimalExhaustive]
  exact (not_injective_iff_exists_ne S).symm

theorem strong_exhaustive_implies_surjective (h : StrongExhaustive S) :
    Function.Surjective S.compare := by
  rcases h with ⟨s, hs⟩
  exact hs.surjective

/-- On the canonical region, “locally strong” exhaustion: section only on canonical bare
objects and reconstruction for realizations whose certificate is canonical. -/
structure LocalStrongExhaustiveOnCanonical where
  sectionOf : Bare → Realized
  section_right_on : ∀ ⦃b⦄, S.Canonical b → S.compare (sectionOf b) = b
  reconstruct_on :
    ∀ ⦃x : Realized⦄, S.Canonical (S.compare x) → sectionOf (S.compare x) = x

end ReflexiveArchitecture.Universal
