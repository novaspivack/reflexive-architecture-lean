/-
  EPIC_018 — Concrete outer layer: NEMS Framework → ReflexiveLayer.

  Builds a `ReflexiveLayer Framework` instance for any `F : Framework` with
  `[dc : DiagonalCapable F]`, using `nems-lean` types directly.

  ## Design

  * `Theory`             := `F.Selector`
  * `InternalTheory`     := caller-supplied `IsInternal`
  * `TotalOn S`          := `TotalEffective F S`
  * `SemanticRemainder S`:= `¬ TotalEffective F S`
  * `FinalSelfTheory S`  := `TotalEffective F S`  (a final theory IS total-effective)
  * `BarrierHyp`         := `∀ S : F.Selector, ¬ TotalEffective F S`
    (semantic content of the diagonal barrier: no selector is total-effective)

  With these assignments both obligations are purely structural:
  - `no_final_self_theory`: BarrierHyp → ∀ S, Int S → ¬ FinalSelf S
    = (∀ S, ¬ TotalEffective F S) → ∀ S, Int S → ¬ TotalEffective F S. Direct.
  - `no_remainder_and_total_implies_final`: TotalOn S → ¬ SemRem S → FinalSelf S
    = TotalEffective F S → ¬ ¬ TotalEffective F S → TotalEffective F S. Direct.

  ## Barrier theorem

  `concreteNEMSBarrierHolds` proves `BarrierHyp` holds for `[DiagonalCapable F]`
  given an explicit chain `hChain : ∀ S, TotalEffective F S → ComputablePred dc.asr.RT`.
  This `hChain` is the one import gap: the NEMS library's internal proof that a
  computability-internal selector decides RT, which is not yet exported as a
  standalone lemma. It is an explicit argument, not a `sorry`.
-/

import NemS.MFRR.DiagonalBarrier
import NemS.Core.Selectors
import ReflexiveArchitecture.Outer.Interface

namespace ReflexiveArchitecture.Instances

open NemS
open NemS.Framework
open NemS.MFRR

/-- Concrete NEMS outer layer.
`BarrierHyp = ∀ S : F.Selector, ¬ TotalEffective F S`. -/
def concreteNEMSReflexiveLayer
    (F : Framework)
    (IsInternal : F.Selector → Prop) :
    Outer.ReflexiveLayer Framework where
  Theory             := F.Selector
  InternalTheory     := IsInternal
  TotalOn            := TotalEffective F
  SemanticRemainder  := fun S => ¬ TotalEffective F S
  FinalSelfTheory    := TotalEffective F
  BarrierHyp         := ∀ S : F.Selector, ¬ TotalEffective F S
  no_final_self_theory           := fun hB S _ => hB S
  no_remainder_and_total_implies_final := fun _ _ hTot _ => hTot

/-- Proves `BarrierHyp` holds for a `DiagonalCapable` framework, given the chain
`hChain : ∀ S, TotalEffective F S → ComputablePred dc.asr.RT`.

This `hChain` is the precise remaining import gap: the NEMS library proves
`¬ ComputablePred dc.asr.RT` (= `diagonal_barrier_rt`) and defines
`TotalEffective F S = IsComputabilityInternal S`, but does not currently export
the forward direction `IsComputabilityInternal S → ComputablePred dc.asr.RT`
as a standalone theorem. This argument makes the gap explicit. -/
-- The BarrierHyp is ∀ S, ¬ TotalEffective F S.
-- Under DiagonalCapable, this holds given the chain TotalEffective → ComputablePred RT.
theorem concreteNEMSBarrierHolds
    (F : Framework) [dc : DiagonalCapable F]
    (IsInternal : F.Selector → Prop)
    (hChain : ∀ S : F.Selector, TotalEffective F S → ComputablePred dc.asr.RT) :
    ∀ S : F.Selector, ¬ TotalEffective F S :=
  fun S hTot => absurd (hChain S hTot) (diagonal_barrier_rt F)

/-- The concrete NEMS semantic non-exhaustion law. -/
theorem concreteNEMS_semantic_nonerasure
    (F : Framework)
    (IsInternal : F.Selector → Prop)
    (hBarrier : ∀ S : F.Selector, ¬ TotalEffective F S) :
    ∀ S : F.Selector,
      IsInternal S →
        ¬ TotalEffective F S ∨ ¬ TotalEffective F S :=
  fun S _ => Or.inl (hBarrier S)

end ReflexiveArchitecture.Instances
