/-
  EPIC_031 — **Fundamental equivalence theorem** (the Gödel-scale closure).

  Five equivalent characterizations of non-exhaustion. The key new direction:
  non-exhaustion implies existence of a non-trivial compare-preserving endomorphism
  (fiber automorphism), constructed classically via a swap on any nontrivial fiber.

  The all-or-nothing theorem: either ALL five conditions hold, or NONE do.
-/

import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.Summit.Adequacy
import ReflexiveArchitecture.Universal.Summit.SelfGeneration
import ReflexiveArchitecture.Universal.Residual.ResidualKernel
import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem

universe u

namespace ReflexiveArchitecture.Universal.Summit

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Residual

variable {Bare Realized : Type u}

/-! ### Non-exhaustion implies fiber automorphism (the Gödel direction) -/

/-- **1→3:** Non-exhaustion implies a non-trivial compare-preserving endomorphism exists.
The construction: given `x ≠ y` with `compare x = compare y`, define a swap
`z ↦ if z = x then y, if z = y then x, else z`. This preserves `compare` and is ≠ id. -/
theorem nonExhaustive_implies_fiberAutomorphism (S : ReflectiveCertificationSystem Bare Realized)
    (h : NonExhaustive S) :
    ∃ (twist : Realized → Realized),
      (∀ z, S.compare (twist z) = S.compare z) ∧ twist ≠ id := by
  obtain ⟨x, y, hne, heq⟩ := h
  classical
  let swap : Realized → Realized := fun z => if z = x then y else if z = y then x else z
  refine ⟨swap, fun z => ?_, fun hid => ?_⟩
  · simp only [swap]
    split_ifs with h1 h2
    · rw [h1, heq]
    · rw [h2, ← heq]
    · rfl
  · have : swap x = id x := congr_fun hid x
    simp [swap] at this
    exact hne this.symm

/-- **3→1:** Fiber automorphism implies non-exhaustion. -/
theorem fiberAutomorphism_implies_nonExhaustive (S : ReflectiveCertificationSystem Bare Realized)
    (twist : Realized → Realized)
    (hpres : ∀ z, S.compare (twist z) = S.compare z)
    (hne : twist ≠ id) :
    NonExhaustive S := by
  have ⟨x, hx⟩ : ∃ x, twist x ≠ x := by
    by_contra h; push_neg at h; exact hne (funext h)
  exact ⟨twist x, x, hx, hpres x⟩

/-! ### The five-way equivalence -/

theorem equiv_1_iff_2 (S : ReflectiveCertificationSystem Bare Realized) :
    NonExhaustive S ↔ ¬MinimalExhaustive S :=
  nonExhaustive_iff_not_minimal S

theorem equiv_1_iff_3 (S : ReflectiveCertificationSystem Bare Realized) :
    NonExhaustive S ↔
      ∃ (twist : Realized → Realized),
        (∀ z, S.compare (twist z) = S.compare z) ∧ twist ≠ id :=
  ⟨nonExhaustive_implies_fiberAutomorphism S,
   fun ⟨twist, hpres, hne⟩ => fiberAutomorphism_implies_nonExhaustive S twist hpres hne⟩

theorem equiv_1_iff_4 (S : ReflectiveCertificationSystem Bare Realized) :
    NonExhaustive S ↔
      ∃ (w₁ w₂ : Realized), w₁ ≠ w₂ ∧ S.compare w₁ = S.compare w₂ :=
  Iff.rfl

theorem equiv_1_iff_5 (S : ReflectiveCertificationSystem Bare Realized) :
    NonExhaustive S ↔ (∃ p, p ∈ ResidualKernel S) :=
  (residualKernel_nonempty_iff S).symm

/-! ### The all-or-nothing theorem -/

/-- **All-or-nothing (Gödel-scale closure):** either ALL five conditions hold
simultaneously, or NONE do. -/
theorem all_or_nothing (S : ReflectiveCertificationSystem Bare Realized) :
    (NonExhaustive S ∧
      ¬MinimalExhaustive S ∧
      (∃ twist : Realized → Realized, (∀ z, S.compare (twist z) = S.compare z) ∧ twist ≠ id) ∧
      (∃ p, p ∈ ResidualKernel S))
    ∨
    (¬NonExhaustive S ∧
      MinimalExhaustive S ∧
      (∀ twist : Realized → Realized, (∀ z, S.compare (twist z) = S.compare z) → twist = id) ∧
      ResidualKernel S = ∅) := by
  rcases Classical.em (NonExhaustive S) with h | h
  · left
    exact ⟨h,
      (equiv_1_iff_2 S).1 h,
      (equiv_1_iff_3 S).1 h,
      (equiv_1_iff_5 S).1 h⟩
  · right
    have hinj : MinimalExhaustive S := by
      rwa [← not_not (a := MinimalExhaustive S), ← equiv_1_iff_2]
    refine ⟨h, hinj, ?_, ?_⟩
    · intro twist hpres
      by_contra hne
      exact h (fiberAutomorphism_implies_nonExhaustive S twist hpres hne)
    · exact (Residual.exhaustive_iff_kernel_empty S).1 hinj

/-! ### Bundled package -/

/-- The five-way equivalence + dichotomy, packaged. -/
structure FiveWayEquivalence (S : ReflectiveCertificationSystem Bare Realized) where
  iff_not_injective : NonExhaustive S ↔ ¬MinimalExhaustive S
  iff_fiber_automorphism : NonExhaustive S ↔
    ∃ (twist : Realized → Realized), (∀ z, S.compare (twist z) = S.compare z) ∧ twist ≠ id
  iff_witness_diversity : NonExhaustive S ↔
    ∃ (w₁ w₂ : Realized), w₁ ≠ w₂ ∧ S.compare w₁ = S.compare w₂
  iff_nontrivial_kernel : NonExhaustive S ↔ (∃ p, p ∈ ResidualKernel S)

/-- The five-way equivalence exists unconditionally for every RCS. -/
def fiveWayEquivalence (S : ReflectiveCertificationSystem Bare Realized) :
    FiveWayEquivalence S where
  iff_not_injective := equiv_1_iff_2 S
  iff_fiber_automorphism := equiv_1_iff_3 S
  iff_witness_diversity := equiv_1_iff_4 S
  iff_nontrivial_kernel := equiv_1_iff_5 S

/-- The five-way equivalence + all-or-nothing dichotomy exist for every RCS. -/
theorem fiveWayEquivalence_exists (S : ReflectiveCertificationSystem Bare Realized) :
    Nonempty (FiveWayEquivalence S) :=
  ⟨fiveWayEquivalence S⟩

end ReflexiveArchitecture.Universal.Summit
