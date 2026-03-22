/-
  Outer layer — abstract NEMS-style semantic self-theory interface.
-/

import Mathlib.Tactic

universe u

namespace ReflexiveArchitecture.Outer

/-- Minimal data for the semantic-remainder master pattern
`SemRem(T) ∨ ¬ TotalOn(T)` under a barrier hypothesis. -/
class ReflexiveLayer (S : Type u) where
  Theory : Type u
  InternalTheory : Theory → Prop
  TotalOn : Theory → Prop
  SemanticRemainder : Theory → Prop
  FinalSelfTheory : Theory → Prop
  /-- Hypothesis packaging diagonal / closure-compatible barrier assumptions. -/
  BarrierHyp : Prop

  no_final_self_theory :
    BarrierHyp → ∀ T, InternalTheory T → ¬ FinalSelfTheory T

  no_remainder_and_total_implies_final :
    ∀ T, InternalTheory T → TotalOn T → ¬ SemanticRemainder T → FinalSelfTheory T

end ReflexiveArchitecture.Outer
