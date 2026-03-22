/-
  Concrete combined Architecture instance: bundling NEMS + APS + IC layers.

  This file builds the combined `Architecture` instance from the three parametric
  layer constructors in FromNEMS, FromAPS, and FromIC.  It uses a single carrier
  type `Unit` with all predicates supplied as explicit `Prop` arguments — this is
  the correct abstract interface-map pattern, keeping the Strata repo independent
  of the source corpus lake dependencies.

  The two cross-layer coherence axioms:

  (1) outer_remainder_forces_inner_enrichment:
      (∃ T, InternalTheory T ∧ SemanticRemainder T) → EnrichedIrreducibility

      Under NEMS + IC: if some internal selector/world-type has semantic remainder
      (is not a final self-theory), then by the NEMS barrier the framework is
      non-categorical, and by the IC inner structure enriched irreducibility holds.

      This axiom is provided as an explicit hypothesis `pos_coherence` — it is the
      cross-corpus mathematical claim that remains to be fully discharged from the
      two source repos in a future milestone.

      -- TODO (EPIC_017_3BQ Task D, positive coherence):
      -- Prove from NEMS diagonal_barrier_rt + IC upstairs-multiplicity that
      -- outer remainder (non-final self-theory) forces IC enriched irreducibility.
      -- This requires a shared abstract non-erasure argument connecting the
      -- NEMS record-truth undecidability chain to the IC enriched witness plurality.

  (2) outer_exhaustion_kills_inner_enrichment:
      (∀ T, InternalTheory T → TotalOn T ∧ ¬ SemanticRemainder T) → ¬ EnrichedIrreducibility

      Under NEMS + IC: if every internal selector is totally exhausting (no remainder),
      then the framework is Category IIa (total-effective selection possible), which
      contradicts the non-trivial enriched structure of IC.  This direction is easier:
      provided as explicit hypothesis `neg_coherence`.

      -- TODO (EPIC_017_3BQ Task D, negative coherence):
      -- Prove from the NEMS IIa/IIb classification that outer exhaustion forces
      -- flat IC architecture with no enriched multiplicity.
-/

import ReflexiveArchitecture.Bridge.Architecture
import ReflexiveArchitecture.Instances.FromNEMS
import ReflexiveArchitecture.Instances.FromAPS
import ReflexiveArchitecture.Instances.FromIC

universe u

namespace ReflexiveArchitecture.Instances

/-- Fully parametric `Architecture` instance.

This is the concrete discharge interface: supply predicates for all three layers
plus the two proved coherence axioms, receive a valid `Architecture S` instance
with all Strata bridge and non-erasure theorems applicable.

The coherence arguments `pos_coherence` and `neg_coherence` are the cross-corpus
theorems that connect the NEMS outer layer to the IC inner layer.  At present they
are explicit hypotheses; they become fully discharged theorems when Tasks D(+) and
D(−) of EPIC_017_3BQ are completed.
-/
def concreteArchitecture
    (S : Type u)
    -- Outer (NEMS) layer data
    (Th                : Type u)
    (internalTheory    : Th → Prop)
    (totalOn           : Th → Prop)
    (semanticRemainder : Th → Prop)
    (finalSelfTheory   : Th → Prop)
    (barrierHyp        : Prop)
    (no_fst  : barrierHyp → ∀ T, internalTheory T → ¬ finalSelfTheory T)
    (noRem_total_impl_final :
       ∀ T, internalTheory T → totalOn T → ¬ semanticRemainder T → finalSelfTheory T)
    -- Middle (APS) layer data
    (hasFiniteTracking : Prop)
    (hasGluing         : Prop)
    (iCompIdx          : Prop)
    (iRecIdx           : Prop)
    (comp_iff          : iCompIdx ↔ hasFiniteTracking ∧ hasGluing)
    -- Inner (IC) layer data
    (RouteType           : Type u)
    (adequateRoute       : RouteType → Prop)
    (canonicalBareCert   : Prop)
    (reflectiveSplit     : Prop)
    (enrichedIrred       : Prop)
    (strictRefinement    : Prop)
    (fiberNontrivial     : Prop)
    (univRouteNecessity  : Prop)
    (ciMinimality        : Prop)
    (canon_impl_split    : canonicalBareCert → reflectiveSplit)
    (adeq_impl_routeNec  : (∃ r, adequateRoute r) → univRouteNecessity)
    (routeNec_impl_strict : univRouteNecessity → strictRefinement)
    (split_impl_fiber    : reflectiveSplit → fiberNontrivial)
    -- Cross-layer coherence axioms
    -- TODO EPIC_017_3BQ Task D(+): pos_coherence — discharge from NEMS diagonal_barrier_rt
    --   + IC upstairs-multiplicity theorem.
    (pos_coherence :
       (∃ T, internalTheory T ∧ semanticRemainder T) → enrichedIrred)
    -- TODO EPIC_017_3BQ Task D(-): neg_coherence — discharge from NEMS IIa classification
    --   + IC flat-architecture consequence.
    (neg_coherence :
       (∀ T, internalTheory T → totalOn T ∧ ¬ semanticRemainder T) → ¬ enrichedIrred) :
    Bridge.Architecture S where
  -- Outer layer
  Theory             := Th
  InternalTheory     := internalTheory
  TotalOn            := totalOn
  SemanticRemainder  := semanticRemainder
  FinalSelfTheory    := finalSelfTheory
  BarrierHyp         := barrierHyp
  no_final_self_theory           := no_fst
  no_remainder_and_total_implies_final := noRem_total_impl_final
  -- Middle layer
  HasFiniteTracking  := hasFiniteTracking
  HasGluing          := hasGluing
  ICompIdx           := iCompIdx
  IRecIdx            := iRecIdx
  comp_iff_finiteTracking_and_gluing := comp_iff
  -- Inner layer
  Route                   := RouteType
  AdequateRoute           := adequateRoute
  CanonicalBareCertificate := canonicalBareCert
  ReflectiveSplit         := reflectiveSplit
  EnrichedIrreducibility  := enrichedIrred
  StrictRefinement        := strictRefinement
  FiberNontriviality      := fiberNontrivial
  UniversalRouteNecessity := univRouteNecessity
  CIMinimality            := ciMinimality
  canonical_implies_split           := canon_impl_split
  adequate_implies_route_necessity  := adeq_impl_routeNec
  route_necessity_implies_strict_refinement := routeNec_impl_strict
  split_implies_fiber_nontriviality := split_impl_fiber
  -- Cross-layer coherence
  outer_remainder_forces_inner_enrichment := pos_coherence
  outer_exhaustion_kills_inner_enrichment := neg_coherence

/-!
## Usage: applying the abstract bridge theorems concretely

Once `concreteArchitecture` is instantiated with the source corpus theorems, all
Strata bridge theorems apply directly.  For example:

```lean
-- Assume all source predicates have been supplied:
let R := concreteArchitecture S Th ... pos_coherence neg_coherence

-- The Non-Erasure Principle discharges concretely:
theorem concrete_nonerasure
    (hBarrier : R.BarrierHyp)
    (hTrack   : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon   : R.CanonicalBareCertificate)
    (hAdeq    : ∃ r, R.AdequateRoute r)
    (hRem     : ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T) :
    R.EnrichedIrreducibility :=
  Bridge.nonerasure_principle (R := R) hBarrier hTrack hCanon hAdeq hRem
```

The `pos_coherence` hypothesis is what makes `nonerasure_principle` fire
concretely.  Supplying it from actual NEMS + IC theorems is Task D of EPIC_017_3BQ.
-/

end ReflexiveArchitecture.Instances
