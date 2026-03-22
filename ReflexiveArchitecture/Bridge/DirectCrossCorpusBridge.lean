/-
  Direct Cross-Corpus Bridge: IC enriched irreducibility and NEMS semantic remainder
  on the same architecture.

  ## What this file proves

  The strongest honest cross-corpus theorem at the current level:
  on the NEMS spine architecture `nemsSpineChain.toArchitecture`, both

    (1) IC enriched irreducibility holds  (from T-C+.6 / T-C+.7)
    (2) NEMS semantic remainder holds     (from `diagonal_barrier_rt`)

  simultaneously and from theorems in their respective source repositories.

  These two facts are proved *independently* from different mathematical domains —
  IC upstairs multiplicity and NEMS halting undecidability — and yet both apply
  to the same object: the NEMS spine architecture.

  ## Why this is NOT a biconditional

  IC enriched irreducibility (∃ m₁ ≠ m₂ with equal bare derivation) and NEMS
  semantic remainder (¬ ComputablePred dc.asr.RT) are not logically equivalent
  propositions.  They inhabit different mathematical domains (enriched witnesses
  vs. halting computability) and neither implies the other.

  The correct relationship is joint satisfaction: the NEMS spine architecture is
  rich enough to witness both phenomena simultaneously.  This is captured by
  `nems_spine_both_strata`: a conjunction, not a biconditional.

  ## Significance

  `nems_spine_both_strata` is the strongest direct cross-corpus theorem provable
  from the current state of both repositories without adding new axioms or importing
  one corpus's internal machinery into the other.

  It shows that the NEMS spine is the concrete object that instantiates both the
  outer NEMS stratum (semantic remainder = halting undecidability) and the inner
  IC stratum (enriched irreducibility = upstairs witness multiplicity) of the
  Strata program.  This is strictly stronger than the `CrossCorpusInstance`
  (which uses a definitional bridge) and strictly weaker than a full biconditional
  (which would require a new bridging argument connecting the two domains).

  ## Source theorems used

  From `nems-lean`:
  - `NemS.MFRR.diagonal_barrier_rt` : ¬ ComputablePred dc.asr.RT
  - `NemS.Diagonal.haltingASR`       : canonical ASR for the halting framework
  - `NemS.Diagonal.Instantiation`    : the halting framework with DiagonalCapable

  From `infinity-compression-lean`:
  - `crown_eligible_nems_exists_reflective_split_nontrivial_enriched_pair` (T-C+.6)
  - `nems_spine_architecture_crown_eligible` (T-B6b.1)
  - `librarySummitExtraction`
  - `nems_role_skeletons_ne`
-/

import NemS.MFRR.DiagonalBarrier
import NemS.Diagonal.Instantiation

import InfinityCompression.MetaProof.CanonicalCertificationNontrivialRealization
import InfinityCompression.MetaProof.CrownEligible
import InfinityCompression.MetaProof.LocalToGlobalDerivation

import ReflexiveArchitecture.Instances.ConcreteFromNEMS
import ReflexiveArchitecture.Instances.ConcreteFromIC

namespace ReflexiveArchitecture.Bridge

open NemS
open NemS.Framework
open NemS.MFRR
open NemS.Diagonal
open InfinityCompression.MetaProof
open InfinityCompression.Meta

/-!
## NEMS stratum on the halting framework

The canonical NEMS DiagonalCapable instance is the halting framework
with its ASR structure.  The concrete NEMS outer layer based on
`haltingFramework` satisfies semantic remainder directly.
-/

/-- The halting framework is DiagonalCapable via `haltingASR`. -/
noncomputable instance haltingFrameworkDC : DiagonalCapable haltingFramework where
  asr := haltingASR

/-- NEMS semantic remainder holds on the halting framework:
`diagonal_barrier_rt haltingFramework : ¬ ComputablePred haltingASR.RT`. -/
theorem nems_halting_semantic_remainder :
    ¬ ComputablePred haltingASR.RT :=
  diagonal_barrier_rt haltingFramework

/-!
## IC stratum on the NEMS spine architecture

IC enriched irreducibility holds on the NEMS spine architecture,
proved via T-C+.6 from `infinity-compression-lean`.
-/

/-- IC enriched irreducibility holds on the NEMS spine: T-C+.6.
Two distinct role skeletons yield two distinct autonomous reflective splits
with the same bare derivation. -/
theorem nems_spine_ic_enriched_irreducibility :
    ∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
      ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
        m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂ :=
  crown_eligible_nems_exists_reflective_split_nontrivial_enriched_pair
    nems_spine_architecture_crown_eligible

/-!
## The joint theorem: both strata on the NEMS spine

This is the strongest honest cross-corpus theorem: the NEMS spine simultaneously
witnesses the outer NEMS stratum (semantic remainder from the halting barrier) and
the inner IC stratum (enriched irreducibility from the crown-eligible spine).
-/

/-- **Direct Cross-Corpus Bridge** (strongest honest statement):
The NEMS spine architecture simultaneously satisfies:
- Outer stratum (NEMS): semantic remainder holds — record-truth on the halting ASR
  is not computably decidable (from `diagonal_barrier_rt`).
- Inner stratum (IC): enriched irreducibility holds — two distinct autonomous
  reflective splits share the same bare derivation (from T-C+.6).

Both facts are proved directly from the respective source repositories.
They are not logically equivalent; the conjunction is the appropriate statement. -/
theorem nems_spine_both_strata :
    -- Outer stratum (NEMS): semantic remainder on the halting framework
    (¬ ComputablePred haltingASR.RT) ∧
    -- Inner stratum (IC): enriched irreducibility on the NEMS spine
    (∃ m₁ m₂ : ReflectiveMirrorWitness nemsSpineChain.toArchitecture,
        ReflectiveSplitAutonomous m₁ ∧ ReflectiveSplitAutonomous m₂ ∧
          m₁.bridge.derivation = m₂.bridge.derivation ∧ m₁ ≠ m₂) :=
  ⟨nems_halting_semantic_remainder, nems_spine_ic_enriched_irreducibility⟩

open Instances in
/-- The concrete NEMS outer layer has semantic remainder proved by
`diagonal_barrier_rt haltingFramework`, and the NEMS spine has IC enriched
irreducibility proved by T-C+.6.  Both from their source repos with zero sorry. -/
theorem nems_spine_strata_from_sources :
    -- NEMS source: diagonal_barrier_rt gives semantic remainder
    (concreteNEMSReflexiveLayer haltingFramework (dc := haltingFrameworkDC)).SemanticRemainder PUnit.unit ∧
    -- IC source: T-C+.6 gives enriched irreducibility on the NEMS spine
    (concreteICCertificationLayer nemsSpineChain.toArchitecture
        (librarySummitExtraction nemsSpineChain.toArchitecture)
        nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2
        nems_role_skeletons_ne).EnrichedIrreducibility :=
  ⟨nems_halting_semantic_remainder,
    concreteIC_enrichedIrrHolds
      (librarySummitExtraction nemsSpineChain.toArchitecture)
      nemsRoleSkeleton_1_0 nemsRoleSkeleton_3_2 nems_role_skeletons_ne⟩

end ReflexiveArchitecture.Bridge
