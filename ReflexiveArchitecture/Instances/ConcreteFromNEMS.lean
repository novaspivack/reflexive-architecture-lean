/-
  EPIC_018 — Concrete outer layer: NEMS Framework → ReflexiveLayer.

  Builds `ReflexiveLayer Framework` for `F : Framework` with `[dc : DiagonalCapable F]`.
  Zero open gaps; zero sorry. `diagonal_barrier_rt F` discharges both proof obligations.

  ## Assignment

  The NEMS barrier `diagonal_barrier_rt F : ¬ ComputablePred dc.asr.RT` IS the
  semantic remainder: RT undecidability = outer semantic non-exhaustion.

  * `Theory`            := `PUnit`        (single abstract theory token, universe-polymorphic)
  * `InternalTheory _`  := `True`
  * `TotalOn _`         := `ComputablePred dc.asr.RT`
  * `SemanticRemainder _`:= `¬ ComputablePred dc.asr.RT`
  * `FinalSelfTheory _` := `ComputablePred dc.asr.RT`
  * `BarrierHyp`        := `True`

  Both axioms discharge directly:
  - `no_final_self_theory`: BarrierHyp → Int _ → ¬ Final _ = diagonal_barrier_rt F
  - `no_remainder_and_total_implies_final`: Int _ → Total _ → ¬ Rem _ → Final _ = hTot
-/

import NemS.MFRR.DiagonalBarrier
import ReflexiveArchitecture.Outer.Interface

universe u

namespace ReflexiveArchitecture.Instances

open NemS
open NemS.Framework
open NemS.MFRR

/-- Concrete NEMS outer layer. Zero open gaps. -/
@[reducible]
def concreteNEMSReflexiveLayer
    (F : Framework)
    [dc : DiagonalCapable F] :
    Outer.ReflexiveLayer Framework where
  Theory             := PUnit
  InternalTheory     := fun _ => True
  TotalOn            := fun _ => ComputablePred dc.asr.RT
  SemanticRemainder  := fun _ => ¬ ComputablePred dc.asr.RT
  FinalSelfTheory    := fun _ => ComputablePred dc.asr.RT
  BarrierHyp         := True
  no_final_self_theory := fun _ _ _ => diagonal_barrier_rt F
  no_remainder_and_total_implies_final := fun _ _ hTot _ => hTot

/-- The barrier holds trivially. -/
theorem concreteNEMSBarrierHolds (F : Framework) [dc : DiagonalCapable F] :
    (concreteNEMSReflexiveLayer F (dc := dc)).BarrierHyp := trivial

/-- Semantic remainder holds: the barrier IS the semantic remainder. -/
theorem concreteNEMS_has_semantic_remainder (F : Framework) [dc : DiagonalCapable F] :
    (concreteNEMSReflexiveLayer F (dc := dc)).SemanticRemainder PUnit.unit :=
  diagonal_barrier_rt F

end ReflexiveArchitecture.Instances
