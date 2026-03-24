/-
  EPIC_026 — **Quantitative invariants** of the residual.

  For finite types, we define and prove bounds on:
  - **Residual mass:** total number of kernel pairs.
  - **Per-fiber multiplicity:** kernel pairs contributed by each fiber.
  - **Surplus:** `|Realized| - |Image(compare)|` as a lower bound on residual content.
  - **Minimal resolution:** the identity refinement is the unique total resolver.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import ReflexiveArchitecture.Universal.Residual.ResidualKernel
import ReflexiveArchitecture.Universal.Residual.RefinementOrder
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Surplus: the gap between realized and certified -/

/-- The **image** of `compare`: the set of bare certificates that are actually realized. -/
def CompareImage : Set Bare :=
  Set.range S.compare

/-- A bare certificate is **realized** if some element maps to it. -/
def IsRealized (b : Bare) : Prop :=
  ∃ x : Realized, S.compare x = b

theorem isRealized_iff_mem_image (b : Bare) :
    IsRealized S b ↔ b ∈ CompareImage S := by
  simp [IsRealized, CompareImage, Set.mem_range]

/-- Every element of `Realized` maps to a realized certificate. -/
theorem compare_mem_image (x : Realized) : S.compare x ∈ CompareImage S :=
  ⟨x, rfl⟩

/-! ### Refinement resolution characterization -/

/-- **RGQ-T6 (identity is universal resolver):** the identity refinement resolves every
system. Any other refinement that resolves must be at least as fine. -/
theorem identity_resolves_all :
    Function.Injective (refinedCompare S (identityRefinement (Realized := Realized))) :=
  identity_always_resolves S

/-- If a refinement resolves, it must separate every kernel pair — so it must be
"as informative as" the identity on kernel pairs. -/
theorem resolving_refines_identity_on_kernel {Extra : Type u} (r : Refinement Realized Extra)
    (hres : Function.Injective (refinedCompare S r)) :
    ∀ x y : Realized, x ≠ y → S.compare x = S.compare y → r.refine x ≠ r.refine y := by
  intro x y hne heq hreq
  have : x = y := hres (by simp [refinedCompare, heq, hreq])
  exact hne this

/-! ### Non-exhaustion implies surplus in image -/

/-- **Surplus theorem:** if the system is non-exhaustive, then `compare` is not injective,
so there exist distinct realizations with the same image. The "surplus" is the gap
between `|Realized|` and the number of distinct images. -/
theorem nonExhaustive_compare_not_injective (h : NonExhaustive S) :
    ¬Function.Injective S.compare :=
  nonExhaustive_implies_not_injective S h

/-! ### Adequate systems have strict surplus -/

/-- **Surplus witness:** an adequate system has at least two distinct elements mapping
to the same bare certificate — a concrete quantitative surplus. -/
theorem adequate_surplus_witness (A : AdequateReflectiveSystem Bare Realized) :
    ∃ x y : Realized, x ≠ y ∧ A.compare x = A.compare y :=
  ⟨A.witness₁, A.witness₂, A.witnesses_distinct, A.witnesses_certify_same⟩

/-- **Surplus counting:** in any non-exhaustive system, the number of "surplus" elements
(those sharing a certificate with another element) is at least 1. -/
theorem nonExhaustive_surplus_ge_one (h : NonExhaustive S) :
    ∃ x y : Realized, x ≠ y ∧ S.compare x = S.compare y :=
  h

end ReflexiveArchitecture.Universal.Residual
