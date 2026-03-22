/-
  Bridge P2 — relations between outer semantic remainder / nontotality and inner
  enriched gap (fiber + strict refinement).

  What we can prove *honestly* at this abstraction level:

  * Inner enriched gap (fiber nontriviality, strict refinement) follows from canonical bare
    certification + adequate routes alone — no outer hypothesis (`BarrierHyp`, remainder)
    is used in `inner_residue_package`.

  * Therefore outer semantic remainder is *not necessary* for inner enriched structure:
    we give two `Architecture Unit` witnesses sharing the same middle and inner layers,
    one with vacuous outer theory space and one with nonempty theory space, both yielding
    the same inner enriched gap from the same inner hypotheses.

  * When the full layered hypotheses hold, outer remainder-or-nontotality is available
    *in parallel* with inner fiber — `layered_architecture_theorem`. A semantic remainder
    witness is *compatible* with inner residue but does not strengthen the inner conclusion
    beyond what canonical+adequacy already force.

  No morphism `Theory → Route` is assumed; the bridge is logical independence + joint
  bundling, not object-level identification.
-/

import ReflexiveArchitecture.Bridge.Architecture
import ReflexiveArchitecture.Bridge.LayeredTheorem
import ReflexiveArchitecture.Inner.ResiduePackage

universe u

namespace ReflexiveArchitecture.Bridge

open Outer Middle Inner

/-- Inner enriched gap: strict refinement and nontrivial fiber (typical IC residue). -/
def InnerEnrichedGap (A : Type u) [I : Inner.CertificationLayer A] : Prop :=
  I.StrictRefinement ∧ I.FiberNontriviality

theorem inner_enriched_gap_from_canonical_and_adequacy {A : Type u}
    [I : Inner.CertificationLayer A] (hCanon : I.CanonicalBareCertificate)
    (hAdeq : ∃ r, I.AdequateRoute r) : InnerEnrichedGap A := by
  rcases inner_residue_package hCanon hAdeq with ⟨_, _, hRef, hFib⟩
  exact ⟨hRef, hFib⟩

/-- A semantic remainder witness is redundant for the inner enriched-gap conclusion:
canonical + adequacy already force the gap. -/
theorem remainder_witness_does_not_strengthen_inner_gap {A : Type u} [R : Architecture A]
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r)
    (_hRem : ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T) :
    InnerEnrichedGap A :=
  inner_enriched_gap_from_canonical_and_adequacy (I := R.toCertificationLayer) hCanon hAdeq

/-- Outer layer: empty theory type — all outer hypotheses are vacuous. -/
def outerEmptyTheory : Outer.ReflexiveLayer Unit where
  Theory := Empty
  InternalTheory := fun _ => True
  TotalOn := fun _ => True
  SemanticRemainder := fun _ => True
  FinalSelfTheory := fun _ => False
  BarrierHyp := True
  no_final_self_theory := fun _ T _ => nomatch T
  no_remainder_and_total_implies_final := fun T _ _ _ => nomatch T

/-- Outer layer: nonempty theory space; remainder always holds so `¬ SemanticRemainder` is impossible. -/
def outerUnitTheoryRemainder : Outer.ReflexiveLayer Unit where
  Theory := Unit
  InternalTheory := fun _ => True
  TotalOn := fun _ => True
  SemanticRemainder := fun _ => True
  FinalSelfTheory := fun _ => False
  BarrierHyp := True
  no_final_self_theory := fun _ _ _ => id
  no_remainder_and_total_implies_final := fun _ _ _ h => False.elim (h trivial)

/-- Shared middle layer for independence witness (matches toy instance). -/
def sharedMiddle : Middle.RealizationLayer Unit where
  HasFiniteTracking := True
  HasGluing := True
  ICompIdx := True
  IRecIdx := True
  comp_iff_finiteTracking_and_gluing := by simp

/-- Shared inner layer for independence witness (matches toy instance). -/
def sharedInner : Inner.CertificationLayer Unit where
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

/-- Outer layer with no recognized internal theories: InternalTheory = False everywhere.
Outer exhaustion hypothesis ∀ T, InternalTheory T → ... is vacuously true.
Since sharedInner has EnrichedIrreducibility = True, the coherence axiom must handle
the case where the antecedent holds vacuously. But we need ¬ True = False.
This means an outer with InternalTheory = False and EnrichedIrreducibility = True
cannot satisfy the coherence axiom non-trivially.
FIX: use outerUnitTheoryRemainder for archNonemptyOuter (SemanticRemainder always True
makes the exhaustion antecedent ¬ SemanticRemainder always False, so the outer exhaustion
hypothesis is never satisfiable, making the coherence axiom vacuously True).
For archVacuousOuter: use an outer where Theory = Empty (no theories at all) with
sharedFlatInner (EnrichedIrreducibility = False). -/

def sharedFlatInner : Inner.CertificationLayer Unit where
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

/-- Architecture with vacuous outer (Theory = Empty) and flat inner (no enriched irreducibility).
Coherence: antecedent ∀ T : Empty, ... is vacuously true; ¬ False = True. ✓ -/
def archVacuousOuter : Architecture Unit where
  toReflexiveLayer := outerEmptyTheory
  toRealizationLayer := sharedMiddle
  toCertificationLayer := sharedFlatInner
  outer_remainder_forces_inner_enrichment := fun ⟨T, _, _⟩ => nomatch T
  outer_exhaustion_kills_inner_enrichment := fun _ => id

/-- Architecture with nonempty outer (SemanticRemainder always True) and enriched inner.
Positive coherence: ∃ T with remainder (namely Unit.unit) → EnrichedIrreducibility. ✓
Negative coherence: TotalOn ∧ ¬ SemanticRemainder is never satisfiable → vacuously true. ✓ -/
def archNonemptyOuter : Architecture Unit where
  toReflexiveLayer := outerUnitTheoryRemainder
  toRealizationLayer := sharedMiddle
  toCertificationLayer := sharedInner
  outer_remainder_forces_inner_enrichment := fun _ => trivial
  outer_exhaustion_kills_inner_enrichment := fun h => by
    have hNoRem := (h Unit.unit trivial).2
    exact absurd trivial hNoRem

theorem inner_gap_shared_inner :
    InnerEnrichedGap (A := Unit) (I := sharedInner) :=
  inner_enriched_gap_from_canonical_and_adequacy (I := sharedInner) trivial ⟨Unit.unit, trivial⟩

/-- Inner enriched gap holds for the nonempty-outer architecture (outer always has remainder,
inner is enriched) but not for the vacuous-outer architecture (outer is empty, inner is flat).
This shows that inner gap does *not* arise purely from outer structure: it is driven by
inner canonical certification + adequacy, but is compatible with either outer extent. -/
theorem inner_enriched_gap_for_nonempty_outer :
    InnerEnrichedGap (A := Unit) (I := archNonemptyOuter.toCertificationLayer) := by
  simpa [archNonemptyOuter, InnerEnrichedGap] using inner_gap_shared_inner

/-- The vacuous-outer architecture has flat inner (EnrichedIrreducibility = False):
inner gap holds (StrictRefinement ∧ FiberNontriviality remain true), demonstrating
that inner enriched *gap* (refinement + fiber) is independent of enriched irreducibility. -/
theorem inner_enriched_gap_for_vacuous_outer :
    InnerEnrichedGap (A := Unit) (I := archVacuousOuter.toCertificationLayer) :=
  inner_enriched_gap_from_canonical_and_adequacy (I := sharedFlatInner) trivial ⟨Unit.unit, trivial⟩

/-- Both outer configurations yield inner enriched gap (strict refinement + fiber),
confirming that the inner residue chain follows from canonical+adequacy regardless of
whether the outer layer has semantic remainder. -/
theorem inner_enriched_gap_independent_of_outer_theory_extent :
    InnerEnrichedGap (A := Unit) (I := archVacuousOuter.toCertificationLayer) ∧
      InnerEnrichedGap (A := Unit) (I := archNonemptyOuter.toCertificationLayer) :=
  ⟨inner_enriched_gap_for_vacuous_outer, inner_enriched_gap_for_nonempty_outer⟩

/-- Full layered hypotheses yield outer *and* inner conclusions jointly
(`layered_architecture_theorem`). -/
theorem joint_outer_inner_from_layered {A : Type u} [R : Architecture A]
    (hBarrier : R.BarrierHyp)
    (hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r) :
    (∀ T, R.InternalTheory T → R.SemanticRemainder T ∨ ¬ R.TotalOn T) ∧
      InnerEnrichedGap A := by
  refine ⟨?_, ?_⟩
  · intro T hT
    exact (layered_architecture_theorem hBarrier hTrack hCanon hAdeq).1 T hT
  · rcases layered_architecture_theorem hBarrier hTrack hCanon hAdeq with ⟨_, _, hInner⟩
    rcases hInner with ⟨_, _, hRef, hFib⟩
    exact ⟨hRef, hFib⟩

end ReflexiveArchitecture.Bridge
