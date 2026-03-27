/-
  Summit bridge theorems: the Non-Erasure Principle.

  This file proves the highest-level results of the Strata program:

  1. **Outer remainder forces inner enrichment**:
     If some internal theory has semantic remainder, enriched irreducibility holds.

  2. **Outer exhaustion kills inner enrichment**:
     If every theory is totally exhausted without remainder, enriched irreducibility fails.

  3. **Non-Erasure Biconditional** (under universal totality):
     enriched irreducibility ↔ ∃ theory with semantic remainder.

  4. **Non-Erasure Principle** (with remainder witness):
     Under the full layered hypotheses and a remainder-bearing internal theory,
     enriched irreducibility holds.

  5. **Full Architecture Non-Erasure** (summit theorem):
     All layered hypotheses + remainder witness → outer non-exhaustion AND enriched
     irreducibility AND full inner residue package.

  6. **Unified Non-Erasure Law** (biconditional, under universal totality):
     Outer semantic remainder ↔ inner enriched irreducibility.
     This is the abstract unifying law behind NEMS remainder and IC enriched residue.

  7. **Non-Erasure from Barrier with Totality**:
     Under barrier + universal totality, inner enriched and outer remainder both follow
     for every internal theory.
-/

import ReflexiveArchitecture.Bridge.Architecture
import ReflexiveArchitecture.Bridge.LayeredTheorem
import ReflexiveArchitecture.Inner.ResiduePackage
import ReflexiveArchitecture.Bridge.BareCanonicityNotReflectiveFinality

universe u

namespace ReflexiveArchitecture.Bridge

open Outer Middle Inner

/-- **Positive non-erasure**: outer semantic remainder forces inner enriched irreducibility.
Direct application of the positive coherence axiom. -/
theorem outer_remainder_forces_enriched_irreducibility {A : Type u} [R : Architecture A]
    (T : R.Theory) (hT : R.InternalTheory T) (hRem : R.SemanticRemainder T) :
    R.EnrichedIrreducibility :=
  R.outer_remainder_forces_inner_enrichment ⟨T, hT, hRem⟩

/-- **Negative non-erasure**: outer total exhaustion forces failure of enriched irreducibility.
Direct application of the negative coherence axiom. -/
theorem outer_exhaustion_kills_enriched_irreducibility {A : Type u} [R : Architecture A]
    (h : ∀ T, R.InternalTheory T → R.TotalOn T ∧ ¬ R.SemanticRemainder T) :
    ¬ R.EnrichedIrreducibility :=
  R.outer_exhaustion_kills_inner_enrichment h

/-- **Non-Erasure Biconditional** under universal totality:
enriched irreducibility ↔ ∃ internal theory with semantic remainder.

Under the assumption that every recognized internal theory is total, the two
coherence axioms together give the full equivalence:
- If enriched: by_contra and exhaustion → contradiction.
- If remainder witness: positive coherence gives enriched directly. -/
theorem enriched_iff_outer_remainder_total {A : Type u} [R : Architecture A]
    (hAllTotal : ∀ T, R.InternalTheory T → R.TotalOn T) :
    R.EnrichedIrreducibility ↔ ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T := by
  constructor
  · intro hEnr
    by_contra hNoExist
    push_neg at hNoExist
    have hexhaust : ∀ T, R.InternalTheory T → R.TotalOn T ∧ ¬ R.SemanticRemainder T :=
      fun T hT => ⟨hAllTotal T hT, hNoExist T hT⟩
    exact R.outer_exhaustion_kills_inner_enrichment hexhaust hEnr
  · intro ⟨T, hT, hRem⟩
    exact R.outer_remainder_forces_inner_enrichment ⟨T, hT, hRem⟩

/-- **Non-Erasure Principle** (summit theorem, with inhabited remainder witness):
Under all layered hypotheses and the existence of an internal theory with semantic
remainder, enriched irreducibility holds.

This is the positive bridging theorem connecting the outer and inner strata:
outer semantic non-exhaustion (realized as remainder) directly entails inner
enriched irreducibility via the coherence axiom. -/
theorem nonerasure_principle {A : Type u} [R : Architecture A]
    (_hBarrier : R.BarrierHyp)
    (_hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (_hCanon : R.CanonicalBareCertificate)
    (_hAdeq : ∃ r, R.AdequateRoute r)
    (hRemWitness : ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T) :
    R.EnrichedIrreducibility :=
  R.outer_remainder_forces_inner_enrichment hRemWitness

/-- **Full Architecture Non-Erasure** (main summit theorem):
Under all layered hypotheses and an inhabited semantic remainder, the architecture
simultaneously exhibits three non-erasure conclusions:
- Outer: every internal theory has semantic remainder or fails totality (NEMS law).
- Inner: enriched irreducibility holds (IC law).
- Inner: full residue package (split, route necessity, strict refinement, fiber). -/
theorem full_architecture_nonerasure {A : Type u} [R : Architecture A]
    (hBarrier : R.BarrierHyp)
    (hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r)
    (hRemWitness : ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T) :
    (∀ T, R.InternalTheory T → R.SemanticRemainder T ∨ ¬ R.TotalOn T) ∧
    R.EnrichedIrreducibility ∧
    (R.ReflectiveSplit ∧ R.UniversalRouteNecessity ∧ R.StrictRefinement ∧ R.FiberNontriviality) :=
  ⟨(layered_architecture_theorem hBarrier hTrack hCanon hAdeq).1,
    nonerasure_principle hBarrier hTrack hCanon hAdeq hRemWitness,
    (layered_architecture_theorem hBarrier hTrack hCanon hAdeq).2.2⟩

/-- **Unified Non-Erasure Law** (summit theorem, biconditional):
Under universal totality, outer semantic remainder ↔ inner enriched irreducibility.
This identifies the abstract common law unifying NEMS and IC:
they are the outer and inner expressions of the same non-erasure constraint. -/
theorem unified_nonerasure_law {A : Type u} [R : Architecture A]
    (hAllTotal : ∀ T, R.InternalTheory T → R.TotalOn T) :
    R.EnrichedIrreducibility ↔ ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T :=
  enriched_iff_outer_remainder_total hAllTotal

/-- **Non-Erasure from Barrier with Totality** (corollary):
Under barrier + universal totality + full layered hypotheses,
every internal theory has semantic remainder AND enriched irreducibility holds.

This is the strongest possible form of the non-erasure principle when TotalOn is
universal: the barrier forces outer remainder for all theories, which forces inner
enriched irreducibility, completing the cross-layer derivation. -/
theorem nonerasure_from_barrier_with_totality {A : Type u} [R : Architecture A]
    (hBarrier : R.BarrierHyp)
    (hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r)
    (hAllTotal : ∀ T, R.InternalTheory T → R.TotalOn T)
    (T : R.Theory) (hT : R.InternalTheory T) :
    R.SemanticRemainder T ∧ R.EnrichedIrreducibility := by
  have hOuter := (layered_architecture_theorem hBarrier hTrack hCanon hAdeq).1 T hT
  have hTot := hAllTotal T hT
  have hRem : R.SemanticRemainder T := by
    cases hOuter with
    | inl h => exact h
    | inr h => exact absurd hTot h
  exact ⟨hRem, R.outer_remainder_forces_inner_enrichment ⟨T, hT, hRem⟩⟩

/-- **Enriched Irreducibility Non-Finality** (summit bridge, unifying Thm 1 with Non-Erasure):
Under barrier + universal totality + full layered hypotheses with remainder witness:
enriched irreducibility holds, hence reflective finality (`¬ EnrichedIrreducibility`) fails.
This directly unites the bare-canonicity / reflective-finality separation (Milestone 2)
with the non-erasure principle: enriched structure is not merely possible but forced. -/
theorem enriched_hence_not_reflexively_final {A : Type u} [R : Architecture A]
    (hBarrier : R.BarrierHyp)
    (hTrack : R.HasFiniteTracking ∧ R.HasGluing)
    (hCanon : R.CanonicalBareCertificate)
    (hAdeq : ∃ r, R.AdequateRoute r)
    (hRemWitness : ∃ T, R.InternalTheory T ∧ R.SemanticRemainder T) :
    ¬ ReflectiveFinality (R.toCertificationLayer) :=
  fun h => h (nonerasure_principle hBarrier hTrack hCanon hAdeq hRemWitness)

end ReflexiveArchitecture.Bridge
