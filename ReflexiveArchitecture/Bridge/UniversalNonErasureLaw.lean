/-
  The Universal Non-Erasure Law.

  ## Statement

  For ANY architecture `A` with `RolePairDiverseCrownEligible A` and `SummitComponentExtraction A`,
  and ANY NEMS framework `F` with `DiagonalCapable F`:

    IC enriched irreducibility on A  ↔  NEMS semantic remainder on F

  This is the universal version of the biconditional: not just the NEMS spine, but any
  jointly crown-eligible/diagonal-capable pair.

  ## Why this is the universal law

  The two hypotheses are:
  - `RolePairDiverseCrownEligible A`: the IC architecture has ≥ 2 distinct role-separated
    skeletons, making enriched irreducibility structurally forced (T-C+.7 / T-GR.3).
  - `DiagonalCapable F`: the NEMS framework carries an ASR structure, making record-truth
    undecidability forced (`diagonal_barrier_rt`).

  Under these hypotheses, BOTH sides are unconditionally true — each from its own source:
  - IC enriched irreducibility follows from `RolePairDiverseCrownEligible` alone (T-C+.7).
  - NEMS semantic remainder follows from `DiagonalCapable` alone (`diagonal_barrier_rt`).

  A biconditional between two true propositions is true. The content is in the two
  nontrivial implications: structural IC plurality forces enriched witnesses (T-C+.7),
  and structural NEMS diagonal capability forces undecidability (`diagonal_barrier_rt`).

  ## What makes this universal

  The NEMS-spine biconditional in `SharedReflexiveArchitecture.lean` was specialized
  to `nemsSpineChain.toArchitecture` and `haltingFramework`. This theorem ranges over
  ALL pairs (A : CompressionArchitecture BD n, F : Framework) satisfying the structural
  hypotheses. It applies to:
  - Any crown-eligible IC architecture with two distinct role skeletons
  - Any NEMS-like framework with a diagonal capability / ASR structure

  The NEMS spine is one instance; any other IC-NEMS joint architecture is another.

  ## Logical structure (honest account)

  The biconditional is universal because BOTH sides follow from their structural
  hypotheses alone, independently of each other. The law says:

    "On any architecture class where IC structural plurality and NEMS diagonal
     capability both hold, the IC and NEMS strata are logically equivalent."

  This is a universal law about the class, not a derivation of one side from the other.
  IC enriched irreducibility and NEMS undecidability are equivalent on this class
  because they are both structurally forced by their respective hypotheses — and
  structural forcing of both true propositions gives a biconditional.
-/

import NemS.MFRR.DiagonalBarrier
import NemS.Diagonal.Instantiation

import InfinityCompression.MetaProof.CanonicalCertificationNontrivialRealization
import InfinityCompression.MetaProof.GeneralizedReflectiveFiberRefinement
import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.MetaProof.LocalToGlobalDerivation

import ReflexiveArchitecture.Bridge.SharedReflexiveArchitecture

namespace ReflexiveArchitecture.Bridge

open NemS
open NemS.Framework
open NemS.MFRR
open NemS.Diagonal
open InfinityCompression.MetaProof
open InfinityCompression.Meta

/-!
## The universal biconditional
-/

/-- **IC enriched irreducibility from `RolePairDiverseCrownEligible`** (general, T-C+.7).

On ANY `RolePairDiverseCrownEligible` architecture with `SummitComponentExtraction`,
two distinct enriched witnesses exist with the same bare derivation. -/
theorem ic_enriched_from_rolePairDiverse {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    (hRPD : RolePairDiverseCrownEligible A)
    (H : SummitComponentExtraction A) :
    ∃ m₁ m₂ : ReflectiveMirrorWitness A,
      ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
        m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂ := by
  obtain ⟨_, r₁, r₂, hne⟩ := hRPD
  exact two_distinct_roles_nontrivial_enriched_pair r₁ r₂ H hne

/-- **NEMS semantic remainder from `DiagonalCapable`** (general, `diagonal_barrier_rt`).

For ANY `DiagonalCapable` framework, record-truth is not computably decidable. -/
theorem nems_remainder_from_diagonalCapable
    {F : Framework} [dc : DiagonalCapable F] :
    ¬ ComputablePred dc.asr.RT :=
  diagonal_barrier_rt F

/-!
## The Universal Non-Erasure Law
-/

/-- **Universal Non-Erasure Law:**

For ANY `RolePairDiverseCrownEligible` IC architecture `A` with `SummitComponentExtraction H`
and ANY `DiagonalCapable` NEMS framework `F`:

  IC enriched irreducibility on A  ↔  NEMS semantic remainder on F

This biconditional holds for ALL pairs (A, F) satisfying the structural hypotheses.
It is the universal version of the NEMS-spine biconditional.

The two nontrivial implications:
- (A, H) → IC witnesses: `two_distinct_roles_nontrivial_enriched_pair` (T-C+.7)
- [dc] → NEMS undecidability: `diagonal_barrier_rt`

Both sides are structurally forced by their hypotheses; the biconditional follows. -/
theorem universal_nonerasure_law
    {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    {F : Framework}
    [dc : DiagonalCapable F]
    (hRPD : RolePairDiverseCrownEligible A)
    (H : SummitComponentExtraction A) :
    (∃ m₁ m₂ : ReflectiveMirrorWitness A,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred dc.asr.RT) :=
  ⟨fun _ => nems_remainder_from_diagonalCapable,
   fun _ => ic_enriched_from_rolePairDiverse hRPD H⟩

/-- **Universal Non-Erasure Law (library extraction form):**

Uses `librarySummitExtraction` so the `SummitComponentExtraction` argument is automatic. -/
theorem universal_nonerasure_law_library
    {BD : Type} {n : Nat}
    {A : CompressionArchitecture BD n}
    {F : Framework}
    [dc : DiagonalCapable F]
    (hRPD : RolePairDiverseCrownEligible A) :
    (∃ m₁ m₂ : ReflectiveMirrorWitness A,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred dc.asr.RT) :=
  universal_nonerasure_law hRPD (librarySummitExtraction A)

/-- **The NEMS spine is an instance of the Universal Law.**

The NEMS-spine biconditional `ic_enriched_iff_nems_remainder_unconditional` is a
corollary of `universal_nonerasure_law` applied to the specific (nemsSpineChain, haltingFramework) pair. -/
theorem nems_spine_from_universal :
    (∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred haltingASR.RT) :=
  universal_nonerasure_law_library (F := haltingFramework)
    nems_spine_role_pair_diverse_crown_eligible

/-- Consistency check: `nems_spine_from_universal` recovers exactly
`ic_enriched_iff_nems_remainder_unconditional`. -/
theorem universal_recovers_spine_biconditional :
    (∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) ↔
    (¬ ComputablePred haltingASR.RT) :=
  nems_spine_from_universal

end ReflexiveArchitecture.Bridge
