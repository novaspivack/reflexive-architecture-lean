/-
  Necessity Theorem: the Universal Non-Erasure Law collapses to a single hypothesis.

  ## The key insight

  `DiagonalCapable` is always satisfiable by `haltingFramework` with `haltingASR`,
  unconditionally and independently of any IC architecture.  The halting problem is
  undecidable regardless of which IC architecture A one considers.

  Therefore the Universal Non-Erasure Law's two-hypothesis condition
  (`RolePairDiverseCrownEligible A` AND `DiagonalCapable F`)
  collapses to a ONE-hypothesis condition:

    `RolePairDiverseCrownEligible A`  →  biconditional holds (for A vs haltingFramework)

  This is the necessity theorem: for ANY `RolePairDiverseCrownEligible` IC architecture,
  IC enriched irreducibility ↔ NEMS semantic remainder (on the canonical halting framework).

  No separate `DiagonalCapable` hypothesis is needed because the halting framework
  is always diagonally capable, regardless of A.

  ## What this means

  The Universal Non-Erasure Law was already stated for all pairs (A, F) satisfying
  both structural conditions.  The necessity theorem shows that the right-hand side
  (NEMS undecidability) is always available — one does not need to find a special F.
  The halting framework is the canonical diagonal witness.

  ## The single-hypothesis form

  For any `RolePairDiverseCrownEligible A`:

    IC enriched irreducibility on A  ↔  ¬ ComputablePred haltingASR.RT

  The right-hand side is always true (by Mathlib's halting_problem), so this is:

    IC enriched irreducibility on A  ↔  True

  Which is simply: `RolePairDiverseCrownEligible A → IC enriched irreducibility on A`.

  This is T-C+.7 / T-GR.3 directly — `two_distinct_roles_nontrivial_enriched_pair`.

  ## The deeper necessity question (genuinely open)

  The question "do the two structural hypotheses logically imply each other" is answered:
  - `DiagonalCapable` is universally satisfiable (haltingFramework), so it adds no
    constraint beyond what is already there.
  - `RolePairDiverseCrownEligible` is the substantive structural condition.
  - The biconditional holds whenever `RolePairDiverseCrownEligible` holds,
    because both sides then follow (IC from T-C+.7, NEMS from halting_problem).

  The remaining genuine necessity question would be: does `RolePairDiverseCrownEligible`
  ITSELF follow from some even weaker/simpler condition?  That would require understanding
  when polarity plurality is necessary for a compression architecture.

  ## Single-hypothesis universal law

  The strongest clean form:

    single_hypothesis_nonerasure_law:
    ∀ A with RolePairDiverseCrownEligible,
      IC enriched irreducibility on A  ↔  ¬ ComputablePred haltingASR.RT

  This is the universal law with a single structural hypothesis.
-/

import NemS.Diagonal.Instantiation
import NemS.MFRR.DiagonalBarrier

import InfinityCompression.MetaProof.GeneralizedReflectiveFiberRefinement
import InfinityCompression.MetaProof.LocalToGlobalDerivation

import ReflexiveArchitecture.Bridge.UniversalNonErasureLaw

namespace ReflexiveArchitecture.Bridge

open NemS
open NemS.MFRR
open NemS.Diagonal
open InfinityCompression.MetaProof
open InfinityCompression.Meta

/-!
## DiagonalCapable is universally available

The halting framework is always diagonally capable.
This means `DiagonalCapable` is not an additional constraint on any system.
-/

/-- The halting framework is always `DiagonalCapable`.
This is the canonical diagonal witness, available unconditionally. -/
noncomputable instance haltingDC : DiagonalCapable haltingFramework where
  asr := haltingASR

/-- NEMS semantic remainder holds unconditionally on the halting framework. -/
theorem nems_remainder_always : ¬ ComputablePred haltingASR.RT :=
  nems_halting_semantic_remainder

/-!
## The single-hypothesis universal law

For any `RolePairDiverseCrownEligible` IC architecture, the biconditional holds
with the halting framework as the canonical NEMS partner.
No additional `DiagonalCapable` hypothesis is needed.
-/

/-- **Single-Hypothesis Universal Non-Erasure Law.**

For any `RolePairDiverseCrownEligible` IC architecture `A`:

  IC enriched irreducibility on A  ↔  NEMS semantic remainder (on haltingFramework)

The NEMS side holds unconditionally (halting_problem).
The IC side holds from `RolePairDiverseCrownEligible A` via T-C+.7.

This is the universal law with a SINGLE structural hypothesis.
The canonical diagonal witness is always the halting framework. -/
theorem single_hypothesis_nonerasure_law
    {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    (hRPD : RolePairDiverseCrownEligible A)
    (H : SummitComponentExtraction A) :
    (∃ m₁ m₂ : ReflectiveMirrorWitness A,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred haltingASR.RT) :=
  universal_nonerasure_law (F := haltingFramework) hRPD H

/-- Library extraction form: `SummitComponentExtraction` supplied automatically. -/
theorem single_hypothesis_nonerasure_law_library
    {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    (hRPD : RolePairDiverseCrownEligible A) :
    (∃ m₁ m₂ : ReflectiveMirrorWitness A,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred haltingASR.RT) :=
  universal_nonerasure_law_library (F := haltingFramework) hRPD

/-- **Structural necessity (IC side):**
`RolePairDiverseCrownEligible A` → IC enriched irreducibility.
This is the nontrivial direction: structural plurality forces witness plurality. -/
theorem rolePairDiverse_implies_ic_enriched_irred
    {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    (hRPD : RolePairDiverseCrownEligible A)
    (H : SummitComponentExtraction A) :
    ∃ m₁ m₂ : ReflectiveMirrorWitness A,
      ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
        m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂ :=
  (single_hypothesis_nonerasure_law hRPD H).mpr nems_remainder_always

/-- **The biconditional with ONE hypothesis:**
`RolePairDiverseCrownEligible A` is the single condition that makes the full
non-erasure biconditional hold (with the canonical halting framework as NEMS partner).

The NEMS side is always true; the IC side follows from the single hypothesis.
Both sides are therefore equivalent to `RolePairDiverseCrownEligible A` being true. -/
theorem single_hypothesis_is_sufficient
    {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    (hRPD : RolePairDiverseCrownEligible A) :
    -- IC enriched irreducibility holds
    (∃ H : SummitComponentExtraction A,
      ∃ m₁ m₂ : ReflectiveMirrorWitness A,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ∧
    -- NEMS semantic remainder holds (on canonical halting framework)
    (¬ ComputablePred haltingASR.RT) :=
  ⟨⟨librarySummitExtraction A,
    rolePairDiverse_implies_ic_enriched_irred hRPD (librarySummitExtraction A)⟩,
   nems_remainder_always⟩

/-!
## The NEMS spine instantiates single_hypothesis_nonerasure_law
-/

/-- The NEMS spine satisfies `RolePairDiverseCrownEligible` and hence the
single-hypothesis law holds on it, recovering the spine biconditional. -/
theorem nems_spine_single_hypothesis :
    (∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred haltingASR.RT) :=
  single_hypothesis_nonerasure_law_library nems_spine_role_pair_diverse_crown_eligible

end ReflexiveArchitecture.Bridge
