/-
  EPIC_020 — Small **counterexample library** for universal claims over minimal `RCS`.

  * **Identity comparison** on a shared carrier: injective ⇒ `MinimalExhaustive`, not
    `NonExhaustive`.
  * Use these to test candidate “strong class” axioms: nontrivial carriers alone do not
    rule out injective collapse (e.g. `Bool → Bool`, `id`).
-/

import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal.Strong

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-- Identity comparison on `Bool` (identity-style collapse on a nontrivial carrier). -/
def identityCompareRCS : ReflectiveCertificationSystem Bool Bool where
  compare := id
  Canonical := fun _ => True
  Sound := True

theorem identityCompare_minimalExhaustive : MinimalExhaustive identityCompareRCS := by
  simp [MinimalExhaustive, identityCompareRCS]

theorem identityCompare_not_nonExhaustive : ¬NonExhaustive identityCompareRCS := by
  intro ⟨x, y, hne, heq⟩
  dsimp [identityCompareRCS] at heq
  exact hne heq

theorem identityCompare_not_nonExhaustive' : NonExhaustive identityCompareRCS → False := fun h =>
  identityCompare_not_nonExhaustive h

/-- Injective `compare` from an equivalence (illustrates non-`id` injective collapse). -/
def equivCompareRCS (e : Realized ≃ Bare) : ReflectiveCertificationSystem Bare Realized where
  compare := e
  Canonical := fun _ => True
  Sound := True

theorem equivCompare_minimalExhaustive (e : Realized ≃ Bare) : MinimalExhaustive (equivCompareRCS e) :=
  e.injective

end ReflexiveArchitecture.Universal.Strong
