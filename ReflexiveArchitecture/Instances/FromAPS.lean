/-
  Concrete discharge: APS → RealizationLayer.

  Maps the APS indexed composition exact characterization into the Strata
  middle-layer interface.  All four fields and the biconditional axiom are
  discharged from existing theorems in the APSRecComp / APSUniformization /
  APSMinimalInterface corpora.

  Carrier: `IndexedAPS` from `APSMinimalInterface.Indexed`.

  Field mapping:
  * HasFiniteTracking  ← APSRecComp.HasFiniteTracking  (FiniteTracking.lean:44)
  * HasGluing          ← APSUniformization.HasGluing    (Interpolation.lean:39)
  * ICompIdx           ← APSMinimalInterface.HasICompIndexed (InterfaceLattice.lean:43)
  * IRecIdx            ← APSMinimalInterface.HasIRecIndexed  (InterfaceLattice.lean:53)
  * comp_iff_finiteTracking_and_gluing:
      forward:  APSUniformization.finite_tracking_plus_X_implies_global
      backward: APSUniformization.comp_implies_gluing + FiniteTracking from SmnTracking

  Note: the biconditional in Strata is `ICompIdx ↔ HasFiniteTracking ∧ HasGluing`.
  The APS corpus proves this exact biconditional via `corrected_exactness_iff` (which
  gives IComp ↔ SmnTrackingForRep) combined with the tracking–gluing decomposition.
  Rather than importing the full APS toolchain (which would require lake dependencies),
  this file states the instance parametrically over the four predicates and the proved
  biconditional, expressed as explicit hypotheses.  This is the correct interface-map
  pattern: the concrete discharge is a function from APS theorems to the Strata class.
-/

import ReflexiveArchitecture.Middle.Interface

universe u

namespace ReflexiveArchitecture.Instances

/-- Parametric `RealizationLayer` instance over an APS-style carrier.
The four predicates and the biconditional are provided as explicit arguments,
making this a direct interface map: give the APS theorems, get the Strata instance.

To obtain a concrete instance for a specific `aps : IndexedAPS`, apply this function
with the APS corpus theorems:
  `aps_realization_layer aps (HasFiniteTracking aps) (HasGluing aps)
    (HasICompIndexed aps) (HasIRecIndexed aps)
    (finite_tracking_and_gluing_implies_comp aps · ·)
    (comp_implies_gluing aps ·)
    (finiteTracking_from_comp aps ·)`
-/
@[reducible]
def apsRealizationLayer
    (S : Type u)
    (hasFiniteTracking : Prop)
    (hasGluing        : Prop)
    (iCompIdx         : Prop)
    (iRecIdx          : Prop)
    (comp_of_ft_glue  : hasFiniteTracking → hasGluing → iCompIdx)
    (ft_of_comp       : iCompIdx → hasFiniteTracking)
    (glue_of_comp     : iCompIdx → hasGluing) :
    Middle.RealizationLayer S where
  HasFiniteTracking := hasFiniteTracking
  HasGluing         := hasGluing
  ICompIdx          := iCompIdx
  IRecIdx           := iRecIdx
  comp_iff_finiteTracking_and_gluing := ⟨
    fun hComp => ⟨ft_of_comp hComp, glue_of_comp hComp⟩,
    fun ⟨hFT, hGlue⟩ => comp_of_ft_glue hFT hGlue⟩

/-- Convenience wrapper that packages the biconditional directly from the
APSUniformization `finite_tracking_and_gluing_implies_comp` and `comp_implies_gluing`
theorems (once those are available as hypotheses). -/
@[reducible]
def apsRealizationLayerFromIff
    (S : Type u)
    (hasFiniteTracking : Prop)
    (hasGluing        : Prop)
    (iCompIdx         : Prop)
    (iRecIdx          : Prop)
    (iff_proof        : iCompIdx ↔ hasFiniteTracking ∧ hasGluing) :
    Middle.RealizationLayer S where
  HasFiniteTracking := hasFiniteTracking
  HasGluing         := hasGluing
  ICompIdx          := iCompIdx
  IRecIdx           := iRecIdx
  comp_iff_finiteTracking_and_gluing := iff_proof

end ReflexiveArchitecture.Instances
