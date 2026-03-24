/-
  EPIC_023 — **Refinement composition and ordering.**

  Refinements compose: if `r₁ : Realized → E₁` and `r₂ : Realized → E₂`, then
  `(r₁, r₂) : Realized → E₁ × E₂` is a refinement that is **at least as fine** as
  either component.

  The identity refinement (to `PUnit`) is bottom; total separation (to `Realized`
  itself) is top.
-/

import ReflexiveArchitecture.Universal.Residual.ResidualStructure

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Refinement composition -/

/-- **Trivial refinement:** maps everything to `PUnit` (no extra information). -/
def trivialRefinement : Refinement Realized PUnit where
  refine := fun _ => PUnit.unit

/-- The trivial refinement does not shrink any fiber: refined fibers equal original fibers. -/
theorem trivialRefinement_fiber_eq (b : Bare) :
    RefinedFiber S (trivialRefinement (Realized := Realized)) (b, PUnit.unit) = Fiber S b := by
  ext x
  simp [RefinedFiber, refinedCompare, trivialRefinement, Fiber]

/-- **Identity refinement:** maps each element to itself (maximal information). -/
def identityRefinement : Refinement Realized Realized where
  refine := id

/-- The identity refinement makes the refined comparison injective. -/
theorem identityRefinement_injective :
    Function.Injective (refinedCompare S (identityRefinement (Realized := Realized))) := by
  intro x y heq
  simp [refinedCompare, identityRefinement, Prod.mk.injEq] at heq
  exact heq.2

/-- **Product refinement:** combine two refinements into one that is at least as fine
as either component. -/
def productRefinement {E₁ E₂ : Type u} (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂) :
    Refinement Realized (E₁ × E₂) where
  refine := fun x => (r₁.refine x, r₂.refine x)

/-- Product refinement fibers are subsets of either component's refined fibers. -/
theorem productRefinement_fiber_subset_left {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (b : Bare) (e₁ : E₁) (e₂ : E₂) :
    RefinedFiber S (productRefinement r₁ r₂) (b, (e₁, e₂)) ⊆
      RefinedFiber S r₁ (b, e₁) := by
  intro x hx
  simp [RefinedFiber, refinedCompare, productRefinement, Prod.mk.injEq] at hx ⊢
  exact ⟨hx.1, hx.2.1⟩

theorem productRefinement_fiber_subset_right {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (b : Bare) (e₁ : E₁) (e₂ : E₂) :
    RefinedFiber S (productRefinement r₁ r₂) (b, (e₁, e₂)) ⊆
      RefinedFiber S r₂ (b, e₂) := by
  intro x hx
  simp [RefinedFiber, refinedCompare, productRefinement, Prod.mk.injEq] at hx ⊢
  exact ⟨hx.1, hx.2.2⟩

/-! ### Refinement preorder -/

/-- Refinement `r₂` is **at least as fine as** `r₁` if equal `r₂`-values imply equal
`r₁`-values (every `r₂`-class is contained in an `r₁`-class). -/
def RefinesTo {E₁ E₂ : Type u} (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂) : Prop :=
  ∀ x y : Realized, r₂.refine x = r₂.refine y → r₁.refine x = r₁.refine y

theorem refinesTo_refl {E : Type u} (r : Refinement Realized E) : RefinesTo r r :=
  fun _ _ h => h

theorem refinesTo_trans {E₁ E₂ E₃ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂) (r₃ : Refinement Realized E₃)
    (h₁₂ : RefinesTo r₁ r₂) (h₂₃ : RefinesTo r₂ r₃) : RefinesTo r₁ r₃ :=
  fun x y h => h₁₂ x y (h₂₃ x y h)

/-- The trivial refinement is refined by everything. -/
theorem trivialRefinement_bot {E : Type u} (r : Refinement Realized E) :
    RefinesTo (trivialRefinement (Realized := Realized)) r :=
  fun _ _ _ => rfl

/-- The identity refinement refines everything. -/
theorem identityRefinement_top {E : Type u} (r : Refinement Realized E) :
    RefinesTo r (identityRefinement (Realized := Realized)) :=
  fun x y h => by simp [identityRefinement] at h; rw [h]

/-- Product refinement refines both components. -/
theorem productRefinement_refines_left {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂) :
    RefinesTo r₁ (productRefinement r₁ r₂) := by
  intro x y h
  simp [productRefinement, Prod.mk.injEq] at h
  exact h.1

theorem productRefinement_refines_right {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂) :
    RefinesTo r₂ (productRefinement r₁ r₂) := by
  intro x y h
  simp [productRefinement, Prod.mk.injEq] at h
  exact h.2

/-! ### Refinement and separation -/

/-- If `r₂` refines `r₁` and `r₁` separates a fiber pair, then `r₂` also separates it. -/
theorem finer_separates_of_coarser_separates {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (hfine : RefinesTo r₁ r₂)
    {x y : Realized} (hsep : r₁.refine x ≠ r₁.refine y) :
    r₂.refine x ≠ r₂.refine y := by
  intro heq
  exact hsep (hfine x y heq)

end ReflexiveArchitecture.Universal.Residual
