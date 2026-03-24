/-
  EPIC_020 — First **stronger class**: `StructuredReflectiveCertificationSystem`.

  Adds: both carriers are **nontrivial** (excludes the degenerate one-point/singleton
  story on *both* sides). This does **not** exclude injective maps like `id : Bool → Bool`
  when both types are nontrivial — see `Strong/Counterexamples.lean`.
-/

import Mathlib.Logic.Nontrivial.Defs
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal.Strong

/-- Structured RCS: minimal lift over `ReflectiveCertificationSystem` requiring **nontrivial**
bare and realized carriers. -/
structure StructuredReflectiveCertificationSystem (Bare Realized : Type u) [Nontrivial Bare]
    [Nontrivial Realized] extends ReflectiveCertificationSystem Bare Realized

/-- Forget the extra typing; use where EPIC_019 lemmas expect a bare `RCS`. -/
abbrev StructuredReflectiveCertificationSystem.toRCS {Bare Realized : Type u} [Nontrivial Bare]
    [Nontrivial Realized] (S : StructuredReflectiveCertificationSystem Bare Realized) :
    ReflectiveCertificationSystem Bare Realized :=
  { compare := S.compare, Canonical := S.Canonical, Sound := S.Sound }

end ReflexiveArchitecture.Universal.Strong
