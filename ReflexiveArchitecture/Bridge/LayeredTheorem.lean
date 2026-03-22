/-
  Integrated Layered Architecture Theorem (bridge conjunction of the three projections).
-/

import ReflexiveArchitecture.Bridge.Architecture
import ReflexiveArchitecture.Outer.SemanticRemainder
import ReflexiveArchitecture.Middle.CompositionExactness
import ReflexiveArchitecture.Inner.ResiduePackage

universe u

namespace ReflexiveArchitecture.Bridge

open Outer Middle Inner

theorem layered_architecture_theorem {A : Type u} [R : Architecture A]
    (hBarrier : R.BarrierHyp)
    (hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r) :
    (∀ T, R.InternalTheory T → R.SemanticRemainder T ∨ ¬ R.TotalOn T) ∧
      R.ICompIdx ∧
        (R.ReflectiveSplit ∧ R.UniversalRouteNecessity ∧ R.StrictRefinement ∧
          R.FiberNontriviality) :=
  ⟨fun T hT => Outer.semantic_remainder_or_nontotality (L := R.toReflexiveLayer) hBarrier T hT,
    Middle.composition_from_tracking_and_gluing (M := R.toRealizationLayer) hTrack,
    Inner.inner_residue_package (I := R.toCertificationLayer) hCanon hAdeq⟩

end ReflexiveArchitecture.Bridge
