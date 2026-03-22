/-
  Bundled inner conclusions from adequacy + canonical bare certification.
-/

import ReflexiveArchitecture.Inner.Interface

universe u

namespace ReflexiveArchitecture.Inner

theorem inner_residue_package {S : Type u} [I : CertificationLayer S]
    (hCanon : I.CanonicalBareCertificate)
    (hAdeq : ∃ r, I.AdequateRoute r) :
    I.ReflectiveSplit ∧ I.UniversalRouteNecessity ∧ I.StrictRefinement ∧ I.FiberNontriviality := by
  have hSplit : I.ReflectiveSplit := I.canonical_implies_split hCanon
  have hNec : I.UniversalRouteNecessity := I.adequate_implies_route_necessity hAdeq
  have hRef : I.StrictRefinement := I.route_necessity_implies_strict_refinement hNec
  have hFib : I.FiberNontriviality := I.split_implies_fiber_nontriviality hSplit
  exact ⟨hSplit, hNec, hRef, hFib⟩

end ReflexiveArchitecture.Inner
