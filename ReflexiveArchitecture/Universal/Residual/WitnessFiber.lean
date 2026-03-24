/-
  EPIC_023 — **Witness-fiber connection** and fiber invariance.

  The two witnesses of an `AdequateReflectiveSystem` live in the **same** fiber.
  Fiber nontriviality is a property of `compare` alone, independent of which
  witnesses are chosen.
-/

import ReflexiveArchitecture.Universal.FiberBasics
import ReflexiveArchitecture.Universal.Summit.Adequacy
import ReflexiveArchitecture.Universal.Residual.FiberResidual
import ReflexiveArchitecture.Universal.Residual.ResidualStructure

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u}

/-- The two adequate witnesses live in the **same** fiber. -/
theorem adequate_witnesses_same_fiber (A : AdequateReflectiveSystem Bare Realized) :
    A.witness₁ ∈ Fiber A.toRCS (A.compare A.witness₁) ∧
    A.witness₂ ∈ Fiber A.toRCS (A.compare A.witness₁) := by
  constructor
  · simp [Fiber]
  · simp [Fiber, A.witnesses_certify_same.symm]

/-- The canonical nontrivial fiber of an adequate system: the fiber over the shared
bare certificate of the two witnesses. -/
def canonicalNontrivialFiber (A : AdequateReflectiveSystem Bare Realized) : Bare :=
  A.compare A.witness₁

/-- The canonical fiber is nontrivial. -/
theorem canonicalFiber_nontrivial (A : AdequateReflectiveSystem Bare Realized) :
    ∃ x y : Realized, x ≠ y ∧
      x ∈ Fiber A.toRCS (canonicalNontrivialFiber A) ∧
      y ∈ Fiber A.toRCS (canonicalNontrivialFiber A) :=
  ⟨A.witness₁, A.witness₂, A.witnesses_distinct,
    (adequate_witnesses_same_fiber A).1, (adequate_witnesses_same_fiber A).2⟩

/-- There exists a non-bare-determined predicate on any adequate system. -/
theorem adequate_has_non_bareDetermined (A : AdequateReflectiveSystem Bare Realized) :
    ∃ P : Realized → Prop, ¬BareDetermined A.toRCS P :=
  exists_non_bareDetermined_of_nonExhaustive A.toRCS (adequate_nonExhaustive A)

/-- **Fiber nontriviality is independent of witness choice:** it depends only on
`compare`, not on which specific `w₁, w₂` are provided. Any two adequate systems
with the **same** `compare` have the same `NonExhaustive` status. -/
theorem nonExhaustive_depends_only_on_compare
    (A₁ A₂ : AdequateReflectiveSystem Bare Realized)
    (hcmp : A₁.compare = A₂.compare) :
    NonExhaustive A₁.toRCS ↔ NonExhaustive A₂.toRCS := by
  simp [NonExhaustive, hcmp]

/-- Two adequate systems with the same `compare` have the same fiber partition. -/
theorem fiber_eq_of_compare_eq
    (A₁ A₂ : AdequateReflectiveSystem Bare Realized)
    (hcmp : A₁.compare = A₂.compare) (b : Bare) :
    Fiber A₁.toRCS b = Fiber A₂.toRCS b := by
  ext x
  simp [Fiber, hcmp]

/-- **Residual structure is compare-intrinsic:** `BareDetermined` depends only on `compare`. -/
theorem bareDetermined_depends_only_on_compare
    (A₁ A₂ : AdequateReflectiveSystem Bare Realized)
    (hcmp : A₁.compare = A₂.compare) (P : Realized → Prop) :
    BareDetermined A₁.toRCS P ↔ BareDetermined A₂.toRCS P := by
  simp [BareDetermined, hcmp]

end ReflexiveArchitecture.Universal.Residual
