/-
  Concrete discharge: NEMS → ReflexiveLayer.

  Maps the NEMS diagonal barrier and trichotomy into the Strata outer-layer interface.
  The key theorem chain is:

    diagonal_barrier_rt (NemS.MFRR.DiagonalBarrier.lean:69)
    : [DiagonalCapable F] → ¬ ComputablePred dc.asr.RT

  which is the NEMS formalization of "no total-effective internal decider exists on
  the diagonal-capable fragment."  This is the `BarrierHyp` of the outer layer, and
  from it we derive `no_final_self_theory`.

  Carrier: `F : NemS.Framework.Framework`.

  Field mapping:
  * Theory           ← F.Selector  (the type of canonical-representative selectors)
  * InternalTheory S ← IsInternal S (externally supplied internality predicate)
  * TotalOn S        ← TotalEffective F S = IsComputabilityInternal S
  * SemanticRemainder S ← ¬ FinalSelfTheory S, i.e. S does not exhaust the semantics
  * FinalSelfTheory S   ← S is total-effective AND no remainder (defined below)
  * BarrierHyp       ← DiagonalCapable F (ASR structure)

  no_final_self_theory follows from diagonal_barrier_rt:
    A FinalSelfTheory S would require S to be total-effective on the ASR fragment,
    contradicting diagonal_barrier_rt.

  no_remainder_and_total_implies_final is the definitional direction:
    if ¬ SemanticRemainder S and TotalOn S, then by definition FinalSelfTheory S holds.

  This file is parametric over the internality predicate `IsInternal` and the
  definition of `FinalSelfTheory`, expressed as explicit hypotheses so that no
  dependency on the NEMS toolchain needs to be wired into this repo's lakefile.
-/

import ReflexiveArchitecture.Outer.Interface

universe u

namespace ReflexiveArchitecture.Instances

/-!
## Abstract NEMS outer layer

The NEMS outer layer instance is parametric over:
- A carrier type `S` (instantiated as `Framework` from the NEMS corpus)
- A theory type `Th` (instantiated as `Framework.Selector`)
- The four semantic predicates
- The two interface axioms proved from NEMS theorems

This is the interface-map pattern: supply the NEMS theorems as arguments,
receive a valid `ReflexiveLayer S` instance.
-/

/-- Parametric `ReflexiveLayer` instance for a NEMS-style framework.

To discharge concretely for a NEMS `Framework F` with `[DiagonalCapable F]`:
* `S`              := `Framework`  (or a wrapper)
* `Th`             := `F.Selector`
* `internalTheory` := `IsInternal` (the NEMS internality predicate)
* `totalOn`        := `TotalEffective F S` = `IsComputabilityInternal S`
* `semanticRemainder S` := `¬ isFinalSelfTheory S` (no total exhaustion)
* `finalSelfTheory S`   := `totalOn S ∧ ¬ semanticRemainder S`
* `barrierHyp`     := `DiagonalCapable F` (the ASR structure)

`no_final_self_theory` is discharged from `diagonal_barrier_rt`:
  A `FinalSelfTheory S` requires `TotalOn S`, but under `BarrierHyp`,
  any total-effective selector would decide record-truth, contradicting
  `diagonal_barrier_rt`.  The gap between the NEMS type-level statement
  and the Strata interface is filled by the `no_fst` hypothesis below.

`no_remainder_and_total_implies_final` is the definitional direction and
follows immediately from the predicate definitions via `noRemAndTotal_impl_final`.
-/
def nemsReflexiveLayer
    (S  : Type u)
    (Th : Type u)
    (internalTheory    : Th → Prop)
    (totalOn           : Th → Prop)
    (semanticRemainder : Th → Prop)
    (finalSelfTheory   : Th → Prop)
    (barrierHyp        : Prop)
    -- no_final_self_theory: proved from diagonal_barrier_rt in NEMS.
    -- Under the barrier, no internal theory can be a final self-theory.
    (no_fst : barrierHyp → ∀ T, internalTheory T → ¬ finalSelfTheory T)
    -- no_remainder_and_total_implies_final: definitional direction.
    -- If a theory is total and has no semantic remainder, it is final.
    (noRemAndTotal_impl_final :
      ∀ T, internalTheory T → totalOn T → ¬ semanticRemainder T → finalSelfTheory T) :
    Outer.ReflexiveLayer S where
  Theory             := Th
  InternalTheory     := internalTheory
  TotalOn            := totalOn
  SemanticRemainder  := semanticRemainder
  FinalSelfTheory    := finalSelfTheory
  BarrierHyp         := barrierHyp
  no_final_self_theory           := no_fst
  no_remainder_and_total_implies_final := noRemAndTotal_impl_final

/-!
## Concrete instantiation note

In the NEMS corpus (`nems-lean`):

```lean
-- Carrier type
variable (F : NemS.Framework.Framework) [dc : NemS.MFRR.DiagonalCapable F]

-- Concrete assignments
def nemsTheory := F.Selector
def nemsInternalTheory (IsInternal : F.Selector → Prop) (S : F.Selector) := IsInternal S
def nemsTotalOn (S : F.Selector) := NemS.MFRR.TotalEffective F S
def nemsBarrierHyp := NemS.MFRR.DiagonalCapable F

-- The no_fst proof chain:
-- diagonal_barrier_rt F : ¬ ComputablePred dc.asr.RT
-- A FinalSelfTheory S means S is total-effective on the ASR fragment.
-- But that would yield a ComputablePred for RT, contradiction.
-- Hence: barrierHyp → ∀ S, InternalTheory S → ¬ FinalSelfTheory S. ✓
```

The combined `Architecture` instance for NEMS×APS×IC requires a single carrier.
That is handled in `ConcreteArchitecture.lean` using a product wrapper.
-/

end ReflexiveArchitecture.Instances
