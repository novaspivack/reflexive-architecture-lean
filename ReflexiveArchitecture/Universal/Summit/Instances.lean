/-
  EPIC_021 — **Toy instances** of `AdequateReflectiveSystem` and counterexample
  verification that identity-style collapse cannot inhabit the class.
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Summit

open ReflexiveArchitecture.Universal

instance : Nontrivial (Bool × Bool) :=
  ⟨⟨(true, false), (true, true), by simp [Ne]⟩⟩

/-- Toy adequate system: `compare = Prod.fst` on `Bool × Bool → Bool`.
Witnesses: `(true, false)` and `(true, true)` — distinct, same first component. -/
def toyAdequateSystem : AdequateReflectiveSystem Bool (Bool × Bool) where
  compare := Prod.fst
  Canonical := fun _ => True
  Sound := True
  witness₁ := (true, false)
  witness₂ := (true, true)
  witnesses_distinct := by simp
  witnesses_certify_same := rfl

theorem toyAdequate_nonExhaustive : NonExhaustive toyAdequateSystem.toRCS :=
  adequate_nonExhaustive toyAdequateSystem

theorem toyAdequate_not_injective : ¬Function.Injective toyAdequateSystem.compare :=
  adequate_not_injective toyAdequateSystem

/-- **Counterexample verification:** any attempt to build an adequate system with
`compare = id` on `Bool` leads to contradiction. -/
example : ¬∃ (A : AdequateReflectiveSystem Bool Bool), A.compare = id := by
  rintro ⟨A, hid⟩
  exact identityCompare_not_adequate A hid

/-- **Counterexample verification (general):** any adequate system on equal carriers
with `compare = id` is impossible. -/
theorem no_adequate_with_identity {α : Type u} :
    ∀ (A : AdequateReflectiveSystem α α), A.compare = id → False :=
  fun A hid => by
    have := A.witnesses_certify_same
    rw [hid] at this
    exact A.witnesses_distinct this

/-- **Counterexample verification (equiv):** any adequate system with injective
`compare` is impossible. -/
theorem no_adequate_with_injective {Bare Realized : Type u}
    (A : AdequateReflectiveSystem Bare Realized) (hinj : Function.Injective A.compare) : False :=
  adequate_not_injective A hinj

end ReflexiveArchitecture.Universal.Summit
