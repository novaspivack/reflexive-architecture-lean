/-
  EPIC_019 Phase I — Theorem U1 (fiber basics): fibers of `compare`, injectivity,
  and existence of distinct witnesses in a fiber.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-- Fiber above `b` in the abstract sense: all realizations that certify to `b`. -/
def Fiber (b : Bare) : Set Realized :=
  { x | S.compare x = b }

@[simp]
theorem mem_fiber_iff {b : Bare} {x : Realized} : x ∈ Fiber S b ↔ S.compare x = b :=
  Iff.rfl

/-- Pointwise “subsingleton fiber” predicate (no `Set.Subsingleton` dependency). -/
def FiberIsSubsingleton (b : Bare) : Prop :=
  ∀ ⦃x y : Realized⦄, x ∈ Fiber S b → y ∈ Fiber S b → x = y

theorem injective_iff_forall_fiber_subsingleton :
    Function.Injective S.compare ↔ ∀ b : Bare, FiberIsSubsingleton S b := by
  constructor
  · intro hinj b x y hx hy
    rw [mem_fiber_iff] at hx hy
    exact hinj (hx.trans hy.symm)
  · intro hf x y hxy
    have hx : x ∈ Fiber S (S.compare x) := by simp [Fiber]
    have hy : y ∈ Fiber S (S.compare x) := by simp [Fiber, hxy]
    exact hf (S.compare x) hx hy

theorem not_injective_iff_exists_ne :
    ¬Function.Injective S.compare ↔
      ∃ x y : Realized, x ≠ y ∧ S.compare x = S.compare y := by
  rw [Function.not_injective_iff]
  constructor
  · rintro ⟨x, y, hcmp, hne⟩
    exact ⟨x, y, hne, hcmp⟩
  · rintro ⟨x, y, hne, hcmp⟩
    exact ⟨x, y, hcmp, hne⟩

theorem exists_ne_in_same_fiber_of_not_injective (h : ¬Function.Injective S.compare) :
    ∃ b : Bare, ∃ x y : Realized, x ≠ y ∧ x ∈ Fiber S b ∧ y ∈ Fiber S b := by
  rcases not_injective_iff_exists_ne S |>.1 h with ⟨x, y, hne, heq⟩
  refine ⟨S.compare x, x, y, hne, ?_, ?_⟩
  · simp [Fiber]
  · simp [Fiber, heq]

theorem fiber_nontrivial_of_not_injective (h : ¬Function.Injective S.compare) :
    ∃ b : Bare, ∃ x y : Realized, x ≠ y ∧ x ∈ Fiber S b ∧ y ∈ Fiber S b :=
  exists_ne_in_same_fiber_of_not_injective S h

end ReflexiveArchitecture.Universal
