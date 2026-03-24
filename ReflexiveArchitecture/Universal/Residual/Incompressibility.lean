/-
  EPIC_023 — **Residual incompressibility** and depth bounds.

  A fiber is **incompressible** at a given refinement if the refinement fails to
  separate all its members. A system is **totally incompressible** if no refinement
  (to a type of bounded size) can make `compare` injective.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import ReflexiveArchitecture.Universal.Residual.ResidualStructure
import ReflexiveArchitecture.Universal.Residual.RefinementOrder
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Incompressibility -/

/-- A refinement **fails to resolve** the system if the refined comparison is still
not injective. -/
def UnresolvedBy {Extra : Type u} (r : Refinement Realized Extra) : Prop :=
  ¬Function.Injective (refinedCompare S r)

/-- The identity refinement always resolves (trivially). -/
theorem identity_always_resolves :
    Function.Injective (refinedCompare S (identityRefinement (Realized := Realized))) := by
  intro x y heq
  simp [refinedCompare, identityRefinement, Prod.mk.injEq] at heq
  exact heq.2

/-- **Bounded incompressibility:** a system is incompressible at resolution `Extra`
if no refinement to `Extra` makes the refined comparison injective. -/
def IncompressibleAt (Extra : Type u) : Prop :=
  ∀ r : Refinement Realized Extra, UnresolvedBy S r

/-- **Pigeonhole incompressibility:** if `|Bare| * |Extra| < |Realized|`, no refinement
to `Extra` can make the refined comparison injective. -/
theorem incompressibleAt_of_card_prod_lt [Fintype Realized] [Fintype Bare]
    {Extra : Type u} [Fintype Extra]
    (hcard : Fintype.card Bare * Fintype.card Extra < Fintype.card Realized) :
    IncompressibleAt S Extra := by
  intro r hinj
  have hle : Fintype.card Realized ≤ Fintype.card (Bare × Extra) :=
    Fintype.card_le_of_injective _ hinj
  rw [Fintype.card_prod] at hle
  omega

/-! ### Adequate systems have nontrivial residual depth -/

/-- An adequate system's residual cannot be resolved by a refinement to `PUnit`
(the trivial refinement). In other words: the residual has depth ≥ 1. -/
theorem adequate_incompressibleAt_unit (A : AdequateReflectiveSystem Bare Realized) :
    IncompressibleAt A.toRCS PUnit := by
  intro r hinj
  have h := adequate_not_injective A
  apply h
  intro x y heq
  have key : refinedCompare A.toRCS r x = refinedCompare A.toRCS r y := by
    simp [refinedCompare, heq, Subsingleton.elim (r.refine x) (r.refine y)]
  exact hinj key

end ReflexiveArchitecture.Universal.Residual
