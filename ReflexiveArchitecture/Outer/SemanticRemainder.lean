/-
  Derived outer theorem: semantic remainder or failure of totality.
-/

import ReflexiveArchitecture.Outer.Interface

universe u

namespace ReflexiveArchitecture.Outer

open Classical in
theorem semantic_remainder_or_nontotality {S : Type u} [L : ReflexiveLayer S]
    (hB : L.BarrierHyp) :
    ∀ T, L.InternalTheory T → L.SemanticRemainder T ∨ ¬ L.TotalOn T := by
  intro T hT
  by_cases hTot : L.TotalOn T
  · by_cases hRem : L.SemanticRemainder T
    · exact Or.inl hRem
    · exfalso
      exact (L.no_final_self_theory hB T hT)
        (L.no_remainder_and_total_implies_final T hT hTot hRem)
  · exact Or.inr hTot

end ReflexiveArchitecture.Outer
