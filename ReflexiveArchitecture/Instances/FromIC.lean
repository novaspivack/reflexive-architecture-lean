/-
  Concrete discharge: IC → CertificationLayer.

  Maps the Infinity Compression route-residue theorems into the Strata inner-layer
  interface.  All four implication axioms in `CertificationLayer` correspond to
  proved theorems in the IC MetaProof corpus.

  Carrier: `CompressionArchitecture BD n` from `InfinityCompression.Meta`.

  Field mapping:
  * Route             ← `AdequateReflectiveRoute BD n A` (or its carrier field `.R`)
  * AdequateRoute r   ← adequacy conditions on r (RouteSoundness + CanonicalLanding + Nondeg)
  * CanonicalBareCertificate ← `canonical_certification_principle_phase2` holds
  * ReflectiveSplit   ← `∃ m, ReflectiveSplitAutonomous m`
  * EnrichedIrreducibility ← upstairs multiplicity: ∃ m₁ ≠ m₂ with equal bare derivation
  * StrictRefinement  ← `ProperExtensionViaForgetful (forgetToBareCanonical ∘ compare)`
  * FiberNontriviality ← `|Fib_A(b*)| ≥ 2` (nontrivial canonical fiber)
  * UniversalRouteNecessity ← every adequate route instantiates route-necessity structure
  * CIMinimality      ← CI minimality theorem

  The four implication axioms map as:
  * canonical_implies_split            ← `reflective_split_from_roles_standard` (ReflectiveSplit.lean:37)
  * adequate_implies_route_necessity   ← `AdequateReflectiveRoute` → route necessity (RouteNecessity.lean)
  * route_necessity_implies_strict_refinement ← route necessity → `ProperExtensionViaForgetful`
  * split_implies_fiber_nontriviality  ← reflective split → fiber nontriviality

  This file uses the same parametric pattern as FromNEMS: the IC theorems are
  supplied as explicit hypotheses, so no lake dependency on infinity-compression-lean
  is required in this repo.
-/

import ReflexiveArchitecture.Inner.Interface

universe u

namespace ReflexiveArchitecture.Instances

/-- Parametric `CertificationLayer` instance for an IC-style certification architecture.

To discharge concretely for `A : CompressionArchitecture BD n`:
* `S`                       := a wrapper type for A (e.g. `Unit` with A fixed, or A itself)
* `RouteType`               := `AdequateReflectiveRoute BD n A` (or its carrier `.R`)
* `adequateRoute r`         := r satisfies RouteSoundness ∧ RouteCanonicalLanding ∧ RouteNondegeneracy
* `canonicalBareCertificate`:= `canonical_certification_principle_phase2 A` holds
* `reflectiveSplit`         := `∃ m : ReflectiveMirrorWitness A, ReflectiveSplitAutonomous m`
* `enrichedIrreducibility`  := upstairs multiplicity theorem (∃ m₁ ≠ m₂, same bare derivation)
* `strictRefinement`        := `ProperExtensionViaForgetful` holds for the route's compare map
* `fiberNontriviality`      := canonical fiber has ≥ 2 elements
* `universalRouteNecessity` := every adequate route instantiates split/refinement structure
* `ciMinimality`            := CI minimality

The four implications:
* `canon_impl_split`:  discharged from `reflective_split_from_roles_standard`
* `adeq_impl_routeNec`: discharged from adequacy → route necessity in IC
* `routeNec_impl_strict`: discharged from route necessity → ProperExtension
* `split_impl_fiber`: discharged from reflective split → fiber nontriviality
-/
@[reducible]
def icCertificationLayer
    (S : Type u)
    (RouteType           : Type u)
    (adequateRoute       : RouteType → Prop)
    (canonicalBareCert   : Prop)
    (reflectiveSplit     : Prop)
    (enrichedIrred       : Prop)
    (strictRefinement    : Prop)
    (fiberNontrivial     : Prop)
    (univRouteNecessity  : Prop)
    (ciMinimality        : Prop)
    -- canon_impl_split: from canonical_certification_principle_phase2 → reflective_split_from_roles_standard
    (canon_impl_split    : canonicalBareCert → reflectiveSplit)
    -- adeq_impl_routeNec: from AdequateReflectiveRoute → universal route necessity
    (adeq_impl_routeNec  : (∃ r, adequateRoute r) → univRouteNecessity)
    -- routeNec_impl_strict: from route necessity → ProperExtensionViaForgetful (GeneralizedReflectiveFiberRefinement)
    (routeNec_impl_strict : univRouteNecessity → strictRefinement)
    -- split_impl_fiber: from reflective split → fiber nontriviality (ReflectiveFiberClassification)
    (split_impl_fiber    : reflectiveSplit → fiberNontrivial) :
    Inner.CertificationLayer S where
  Route                  := RouteType
  AdequateRoute          := adequateRoute
  CanonicalBareCertificate := canonicalBareCert
  ReflectiveSplit        := reflectiveSplit
  EnrichedIrreducibility := enrichedIrred
  StrictRefinement       := strictRefinement
  FiberNontriviality     := fiberNontrivial
  UniversalRouteNecessity := univRouteNecessity
  CIMinimality           := ciMinimality
  canonical_implies_split           := canon_impl_split
  adequate_implies_route_necessity  := adeq_impl_routeNec
  route_necessity_implies_strict_refinement := routeNec_impl_strict
  split_implies_fiber_nontriviality := split_impl_fiber

/-!
## Concrete instantiation note

In the IC corpus (`infinity-compression-lean`):

```lean
variable {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)

-- Route type
def icRoute := AdequateReflectiveRoute BD n A

-- Canonical bare certificate (already a theorem)
-- canonical_certification_principle_phase2 A : ∀ roles H, IsCanonicalBareSummitCertification ...

-- Reflective split
-- ∃ m, ReflectiveSplitAutonomous m   — from reflective_split_from_roles_standard

-- Enriched irreducibility
-- The upstairs-multiplicity theorem: ∃ m₁ ≠ m₂, m₁.bridge.derivation = m₂.bridge.derivation

-- The four implications:
-- canon_impl_split     ← canonical_certification_principle_phase2 + reflective_split_from_roles_standard
-- adeq_impl_routeNec   ← AdequateReflectiveRoute.soundness + RouteNecessity theorems
-- routeNec_impl_strict ← GeneralizedReflectiveFiberRefinement
-- split_impl_fiber     ← ReflectiveFiberClassification
```

The combined `Architecture` instance for NEMS×APS×IC is in `ConcreteArchitecture.lean`.
-/

end ReflexiveArchitecture.Instances
