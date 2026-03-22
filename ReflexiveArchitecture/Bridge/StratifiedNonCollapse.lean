/-
  Stratified non-collapse: from the layered theorem + collapse predicates.
-/

import ReflexiveArchitecture.Bridge.LayeredTheorem
import ReflexiveArchitecture.Bridge.CollapsePredicates

universe u

namespace ReflexiveArchitecture.Bridge

theorem stratified_noncollapse {A : Type u} [R : Architecture A] [C : CollapsePredicates A]
    (hBarrier : R.BarrierHyp)
    (hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r) :
    ¬ C.SemanticCollapse ∧ ¬ C.RealizationFlattening ∧ ¬ C.CertificationCollapse := by
  have hMain := layered_architecture_theorem hBarrier hTrack hCanon hAdeq
  rcases hMain with ⟨hOuter, hComp, hInner⟩
  rcases hInner with ⟨hSplit, _hNec, hRef, _hFib⟩
  refine ⟨?_, ?_, ?_⟩
  · exact C.semantic_collapse_defeated hOuter
  · exact C.realization_flattening_defeated hComp
  · exact C.certification_collapse_defeated ⟨hSplit, hRef⟩

end ReflexiveArchitecture.Bridge
