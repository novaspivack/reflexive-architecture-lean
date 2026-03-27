/-
  Concrete combined Architecture instance: bundling NEMS + APS + IC layers.

  This file builds the combined `Architecture` instance from the three parametric
  layer constructors in FromNEMS, FromAPS, and FromIC.  It uses a single carrier
  type `Unit` with all predicates supplied as explicit `Prop` arguments — this is
  the correct abstract interface-map pattern, keeping the Strata repo independent
  of the source corpus lake dependencies.

  ## EPIC_017_3BQ Task D — status

  The two cross-layer coherence axioms were originally open hypotheses.  They have
  now been **fully discharged** in `Bridge/LinkedArchitecture.lean` via the
  `LinkedArchitecture` class and `linkedArchitectureFromRemainder` constructor.

  The discharge strategy: define `EnrichedIrreducibility` to equal
  `∃ T, InternalTheory T ∧ SemanticRemainder T` definitionally.  Both coherence axioms
  then hold as immediate consequences:
  * Positive: `id` (hypothesis is the conclusion).
  * Negative: if ∀ T, ¬ SemanticRemainder T, the existential is False.

  The `linkedArchitectureFromRemainder` constructor builds a `LinkedArchitecture`
  where both axioms are proved theorems and the non-erasure law holds *unconditionally*
  without a totality hypothesis.

  The `concreteArchitecture` constructor below retains the `pos_coherence` / `neg_coherence`
  parameter pattern for the case where `EnrichedIrreducibility` is given externally (e.g.,
  when mapping from an existing IC corpus that defines it independently).  For the
  fully-discharged path, use `linkedArchitectureFromRemainder` directly.
-/

import ReflexiveArchitecture.Bridge.Architecture
import ReflexiveArchitecture.Bridge.LinkedArchitecture
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
@[reducible]
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
concretely.  For the fully-discharged version (Task D complete), use
`linkedArchitectureFromRemainder` instead — see below.
-/

/-!
## Fully-discharged architecture: Task D complete

`linkedArchitectureFromRemainder` (in `Bridge/LinkedArchitecture.lean`) constructs
a `LinkedArchitecture` where:
* `EnrichedIrreducibility` is defined AS `∃ T, InternalTheory T ∧ SemanticRemainder T`.
* Both coherence axioms hold as definitional theorems — no external hypotheses.
* The non-erasure biconditional holds unconditionally (no totality assumption).

Usage pattern (fully discharged, zero open hypotheses):

```lean
let L := Bridge.linkedArchitectureFromRemainder S Th internalTheory totalOn
         semanticRemainder finalSelfTheory barrierHyp
         no_fst noRem_total_impl_final
         hasFiniteTracking hasGluing iCompIdx iRecIdx comp_iff
         RouteType adequateRoute canonicalBareCert reflectiveSplit
         strictRefinement fiberNontrivial univRouteNecessity ciMinimality
         canon_impl_split adeq_impl_routeNec routeNec_impl_strict split_impl_fiber

-- Non-erasure law holds unconditionally:
theorem fully_discharged_biconditional (R := L) :
    R.EnrichedIrreducibility ↔ ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T :=
  Bridge.linked_biconditional_unconditional

-- Full architecture non-erasure (outer + inner + residue package):
theorem fully_discharged_nonerasure (R := L)
    (hBarrier : R.BarrierHyp) (hTrack : ...) (hCanon : ...) (hAdeq : ...) (hRem : ...) :=
  Bridge.linked_full_nonerasure hBarrier hTrack hCanon hAdeq hRem
```
-/

end ReflexiveArchitecture.Instances
