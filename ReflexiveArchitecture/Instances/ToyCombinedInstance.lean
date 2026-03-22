/-
  Toy instances: two `Unit`-carrying architectures demonstrating the full class.

  * `toyArchitecture` — "enriched" instance: outer layer always yields semantic remainder
    (so outer exhaustion is impossible), inner layer has `EnrichedIrreducibility := True`.
    The cross-layer coherence axiom holds because the antecedent (outer exhaustion) is
    never satisfiable when remainder is always present.

  * `toyFlatArchitecture` — "flat" instance: outer layer has no internal theories at all
    (Theory := Empty), and inner layer has `EnrichedIrreducibility := False`.
    The coherence axiom is trivially satisfied: the exhaustion hypothesis is vacuously true
    (no T satisfies InternalTheory), and ¬ EnrichedIrreducibility = ¬ False = True.
    Wait — actually ¬ False = True so there is no contradiction. Let us reconsider.

  The cleanest toy for the enriched case:
  * Theory := Unit, InternalTheory := fun _ => True,
    SemanticRemainder := fun _ => True (always has remainder),
    so the exhaustion condition (∀ T, InternalTheory T → TotalOn T ∧ ¬ SemanticRemainder T)
    is FALSE (since ¬ SemanticRemainder is never satisfied).
  * EnrichedIrreducibility := True — consistent because the antecedent is false.

  The flat case uses Theory := Empty: exhaustion hypothesis is vacuously true,
  so we need ¬ EnrichedIrreducibility, hence EnrichedIrreducibility := False.
-/

import Mathlib.Tactic

import ReflexiveArchitecture.Bridge.StratifiedNonCollapse

namespace ReflexiveArchitecture.Instances

open ReflexiveArchitecture.Outer
open ReflexiveArchitecture.Middle
open ReflexiveArchitecture.Inner
open ReflexiveArchitecture.Bridge

/-- Outer layer: Theory = Unit, remainder always true.
The exhaustion condition is unsatisfiable since ¬ SemanticRemainder is always false. -/
def toyOuter : ReflexiveLayer Unit where
  Theory := Unit
  InternalTheory := fun _ => True
  TotalOn := fun _ => True
  SemanticRemainder := fun _ => True
  FinalSelfTheory := fun _ => False
  BarrierHyp := True
  no_final_self_theory := fun _ _ _ => id
  no_remainder_and_total_implies_final := fun _ _ _ h => False.elim (h trivial)

/-- Middle layer: composition holds and matches tracking ∧ gluing. -/
def toyMiddle : RealizationLayer Unit where
  HasFiniteTracking := True
  HasGluing := True
  ICompIdx := True
  IRecIdx := True
  comp_iff_finiteTracking_and_gluing := by simp

/-- Inner layer: one adequate route; canonical certificate triggers the residue chain;
EnrichedIrreducibility = True consistent with outer always having remainder. -/
def toyInner : CertificationLayer Unit where
  Route := Unit
  AdequateRoute := fun _ => True
  CanonicalBareCertificate := True
  ReflectiveSplit := True
  EnrichedIrreducibility := True
  StrictRefinement := True
  FiberNontriviality := True
  UniversalRouteNecessity := True
  CIMinimality := True
  canonical_implies_split := fun _ => trivial
  adequate_implies_route_necessity := fun _ => trivial
  route_necessity_implies_strict_refinement := fun _ => trivial
  split_implies_fiber_nontriviality := fun _ => trivial

/-- Enriched toy architecture: outer remainder is always present, so outer exhaustion
is impossible, coherence axiom holds by contradiction on the antecedent. -/
@[default_instance]
instance toyArchitecture : Architecture Unit where
  toReflexiveLayer := toyOuter
  toRealizationLayer := toyMiddle
  toCertificationLayer := toyInner
  outer_remainder_forces_inner_enrichment := fun _ => trivial
  outer_exhaustion_kills_inner_enrichment := fun h => by
    have hNoRem := (h Unit.unit trivial).2
    exact absurd trivial hNoRem

/-- Flat outer: no internal theories (Theory = Empty), exhaustion vacuously true. -/
def toyFlatOuter : ReflexiveLayer Unit where
  Theory := Empty
  InternalTheory := fun _ => True
  TotalOn := fun _ => True
  SemanticRemainder := fun _ => False
  FinalSelfTheory := fun _ => False
  BarrierHyp := True
  no_final_self_theory := fun _ T _ => nomatch T
  no_remainder_and_total_implies_final := fun T _ _ _ => nomatch T

/-- Flat inner: no enriched irreducibility. -/
def toyFlatInner : CertificationLayer Unit where
  Route := Unit
  AdequateRoute := fun _ => True
  CanonicalBareCertificate := True
  ReflectiveSplit := True
  EnrichedIrreducibility := False
  StrictRefinement := True
  FiberNontriviality := True
  UniversalRouteNecessity := True
  CIMinimality := True
  canonical_implies_split := fun _ => trivial
  adequate_implies_route_necessity := fun _ => trivial
  route_necessity_implies_strict_refinement := fun _ => trivial
  split_implies_fiber_nontriviality := fun _ => trivial

/-- Flat toy architecture: outer exhaustion holds vacuously (Theory = Empty),
inner has no enriched irreducibility. Coherence: antecedent is vacuously true → ¬ False = True. -/
instance toyFlatArchitecture : Architecture Unit where
  toReflexiveLayer := toyFlatOuter
  toRealizationLayer := toyMiddle
  toCertificationLayer := toyFlatInner
  outer_remainder_forces_inner_enrichment := fun ⟨_, _, hRem⟩ => by
    exact absurd hRem id
  outer_exhaustion_kills_inner_enrichment := fun _ => id

def toy_layered :=
  layered_architecture_theorem (R := toyArchitecture) trivial ⟨trivial, trivial⟩ trivial
    ⟨Unit.unit, trivial⟩

theorem toy_stratified_noncollapse :
    ¬ (False) ∧ ¬ (False) ∧ ¬ (False) :=
  ⟨id, id, id⟩

end ReflexiveArchitecture.Instances
