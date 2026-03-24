/-
  EPIC_022 — **Residual / fiber geometry** at the abstract universal layer.

  Once `compare` is not injective, fibers over bare certificates carry nontrivial
  structure. This module proves **laws of observables**: any quantity factoring through
  `compare` is **blind** to fiber-internal variation — the first “radar” constraint on
  what can be recovered from bare data alone.

  No `sorry`. This does **not** reprove non-exhaustion; it analyzes consequences given
  the fiber partition.
-/

import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.FiberBasics
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-- Two realizations are fiber-equivalent iff they share a bare certificate — the
equivalence relation whose classes are fibers `Fiber S b`. -/
def FiberEquiv (x y : Realized) : Prop :=
  S.compare x = S.compare y

theorem fiberEquiv_equivalence : Equivalence (FiberEquiv S) where
  refl _ := rfl
  symm hxy := hxy.symm
  trans hxy hyz := hxy.trans hyz

theorem fiberEquiv_iff_mem_same_fiber (x y : Realized) :
    FiberEquiv S x y ↔ ∃ b : Bare, x ∈ Fiber S b ∧ y ∈ Fiber S b := by
  constructor
  · intro h; refine ⟨S.compare x, ?_, ?_⟩
    · simp [Fiber]
    · simp [Fiber, h.symm]
  · rintro ⟨b, hx, hy⟩; rw [mem_fiber_iff] at hx hy; exact hx.trans hy.symm

theorem mem_fiber_compare (x : Realized) : x ∈ Fiber S (S.compare x) := by simp [Fiber]

/-- **Observable law (RFG):** any map factoring through `compare` is constant on each
fiber — certified data alone cannot distinguish points in the same fiber. -/
theorem fiber_blind_of_factors_compare {α : Type u} (f : Realized → α) (g : Bare → α)
    (hf : f = g ∘ S.compare) (b : Bare) ⦃x y : Realized⦄ (hx : x ∈ Fiber S b)
    (hy : y ∈ Fiber S b) : f x = f y := by
  rcases hf with rfl
  rw [mem_fiber_iff] at hx hy
  simp [hx, hy]

/-- `compare` is constant on `Fiber S b` (the canonical “grading” to `Bare`). -/
theorem compare_constant_on_fiber (b : Bare) ⦃x y : Realized⦄ (hx : x ∈ Fiber S b)
    (hy : y ∈ Fiber S b) : S.compare x = S.compare y := by
  rw [mem_fiber_iff] at hx hy
  exact hx.trans hy.symm

/-- `NonExhaustive` packaged as existence of a bare certificate whose fiber contains a
nontrivial pair (the standard residual reading). -/
theorem nonExhaustive_iff_exists_nontrivial_fiber :
    NonExhaustive S ↔
      ∃ b : Bare, ∃ x y : Realized, x ≠ y ∧ x ∈ Fiber S b ∧ y ∈ Fiber S b := by
  simp [NonExhaustive, Fiber]
  constructor
  · rintro ⟨x, y, hne, heq⟩
    refine ⟨S.compare x, x, y, hne, ?_, ?_⟩
    · rfl
    · simpa [Fiber] using heq.symm
  · rintro ⟨b, x, y, hne, hx, hy⟩
    exact ⟨x, y, hne, hx.trans hy.symm⟩

/-- From global non-injectivity, some fiber carries two distinct points. -/
theorem exists_fiber_pair_of_not_injective (h : ¬Function.Injective S.compare) :
    ∃ b : Bare, ∃ x y : Realized, x ≠ y ∧ x ∈ Fiber S b ∧ y ∈ Fiber S b :=
  (nonExhaustive_iff_exists_nontrivial_fiber S).1 ((not_injective_iff_exists_ne S).1 h)

end ReflexiveArchitecture.Universal.Residual
