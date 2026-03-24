/-
  EPIC_020 — **Bundled rich classes** where non-exhaustion is a **theorem of the class**:
  the forcing condition is packaged as data (or fixed by typeclasses), so there is no
  separate hypothesis beyond membership in the class.

  This yields **unconditional** `NonExhaustive` on these nonempty subclasses — the
  strongest honest “universality” at the abstract layer short of a false `∀ RCS`.
-/

import ReflexiveArchitecture.Universal.Forcing.SelfLocationForcing
import ReflexiveArchitecture.Universal.Strong.Inevitability
import ReflexiveArchitecture.Universal.Strong.StructuredRCS

universe u

namespace ReflexiveArchitecture.Universal.Strong

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Forcing

variable {Bare Realized : Type u}

/-- **Finite pigeonhole rich class:** a structured `RCS` plus a witnessed cardinal gap. -/
structure FinitePigeonholeStructured (Bare Realized : Type u) [Fintype Bare] [Fintype Realized]
    [Nontrivial Bare] [Nontrivial Realized] where
  base : StructuredReflectiveCertificationSystem Bare Realized
  card_gap : Fintype.card Bare < Fintype.card Realized

theorem nonExhaustive_of_finitePigeonholeStructured [Fintype Bare] [Fintype Realized]
    [Nontrivial Bare] [Nontrivial Realized] (S : FinitePigeonholeStructured Bare Realized) :
    NonExhaustive (StructuredReflectiveCertificationSystem.toRCS S.base) :=
  inevitability_structured_finiteCard S.base S.card_gap

theorem not_minimalExhaustive_of_finitePigeonholeStructured [Fintype Bare] [Fintype Realized]
    [Nontrivial Bare] [Nontrivial Realized] (S : FinitePigeonholeStructured Bare Realized) :
    ¬MinimalExhaustive (StructuredReflectiveCertificationSystem.toRCS S.base) :=
  inevitability_structured_not_minimal_finiteCard S.base S.card_gap

/-- **Infinite→finite rich class:** typeclasses force infinite realized + finite bare. -/
structure InfiniteFiniteStructured (Bare Realized : Type u) [Infinite Realized] [Finite Bare]
    [Nontrivial Bare] [Nontrivial Realized] where
  base : StructuredReflectiveCertificationSystem Bare Realized

theorem nonExhaustive_of_infiniteFiniteStructured [Infinite Realized] [Finite Bare]
    [Nontrivial Bare] [Nontrivial Realized] (S : InfiniteFiniteStructured Bare Realized) :
    NonExhaustive (StructuredReflectiveCertificationSystem.toRCS S.base) :=
  inevitability_structured_infiniteFinite S.base

theorem not_minimalExhaustive_of_infiniteFiniteStructured [Infinite Realized] [Finite Bare]
    [Nontrivial Bare] [Nontrivial Realized] (S : InfiniteFiniteStructured Bare Realized) :
    ¬MinimalExhaustive (StructuredReflectiveCertificationSystem.toRCS S.base) :=
  inevitability_structured_not_minimal_infiniteFinite S.base

/-- **Self-location gap rich class.** -/
structure SelfLocationGapStructured (Bare Realized : Type u) [Nontrivial Bare] [Nontrivial Realized] where
  base : StructuredReflectiveCertificationSystem Bare Realized
  gap : SelfLocationGap (StructuredReflectiveCertificationSystem.toRCS base)

theorem nonExhaustive_of_selfLocationGapStructured [Nontrivial Bare] [Nontrivial Realized]
    (S : SelfLocationGapStructured Bare Realized) :
    NonExhaustive (StructuredReflectiveCertificationSystem.toRCS S.base) :=
  inevitability_structured_selfLocationGap S.base S.gap

theorem not_minimalExhaustive_of_selfLocationGapStructured [Nontrivial Bare] [Nontrivial Realized]
    (S : SelfLocationGapStructured Bare Realized) :
    ¬MinimalExhaustive (StructuredReflectiveCertificationSystem.toRCS S.base) :=
  inevitability_structured_not_minimal_selfLocationGap S.base S.gap

/-!
### Umbrella API (EPIC_020 hygiene)

`BundledRich` is an inductive **sum** of the three bundled patterns. `BundledRichStructured` is a
thin `@[class]` wrapper so generic lemmas can assume `[BundledRichStructured Bare Realized]` with
one field `bundled : BundledRich …`. Instance synthesis does **not** infer this from a concrete
`FinitePigeonholeStructured` value; construct `⟨.finitePigeonhole S⟩`, `⟨.infiniteFinite S⟩`, or
`⟨.selfLocationGap S⟩`, or declare a `def`/`instance` for a fixed carrier pair.
-/

/-- Umbrella data: one of the three bundled EPIC_020 patterns (each implies `NonExhaustive`). -/
inductive BundledRich (Bare Realized : Type u) [Nontrivial Bare] [Nontrivial Realized] where
  | finitePigeonhole [Fintype Bare] [Fintype Realized] (S : FinitePigeonholeStructured Bare Realized) :
      BundledRich Bare Realized
  | infiniteFinite [Infinite Realized] [Finite Bare] (S : InfiniteFiniteStructured Bare Realized) :
      BundledRich Bare Realized
  | selfLocationGap (S : SelfLocationGapStructured Bare Realized) : BundledRich Bare Realized

namespace BundledRich

variable [Nontrivial Bare] [Nontrivial Realized]

/-- Underlying structured `RCS` common to every branch.

Uses tactic `cases` (not term-mode `match`) so instance parameters on constructors
(`Fintype`, `Infinite`, `Finite`) enter the local context in each branch. -/
def base (m : BundledRich Bare Realized) : StructuredReflectiveCertificationSystem Bare Realized := by
  cases m with
  | finitePigeonhole S => exact S.base
  | infiniteFinite S => exact S.base
  | selfLocationGap S => exact S.base

/-- Forget to the minimal universal-layer `RCS`. -/
abbrev toRCS (m : BundledRich Bare Realized) : ReflectiveCertificationSystem Bare Realized :=
  StructuredReflectiveCertificationSystem.toRCS (base m)

theorem nonExhaustive (m : BundledRich Bare Realized) : NonExhaustive (toRCS m) := by
  cases m with
  | finitePigeonhole S => exact nonExhaustive_of_finitePigeonholeStructured S
  | infiniteFinite S => exact nonExhaustive_of_infiniteFiniteStructured S
  | selfLocationGap S => exact nonExhaustive_of_selfLocationGapStructured S

theorem not_minimalExhaustive (m : BundledRich Bare Realized) : ¬MinimalExhaustive (toRCS m) := by
  cases m with
  | finitePigeonhole S => exact not_minimalExhaustive_of_finitePigeonholeStructured S
  | infiniteFinite S => exact not_minimalExhaustive_of_infiniteFiniteStructured S
  | selfLocationGap S => exact not_minimalExhaustive_of_selfLocationGapStructured S

end BundledRich

/-- Typeclass packaging a `BundledRich` witness (generic API over the three subclasses). -/
class BundledRichStructured (Bare Realized : Type u) [Nontrivial Bare] [Nontrivial Realized] where
  bundled : BundledRich Bare Realized

namespace BundledRichStructured

variable [Nontrivial Bare] [Nontrivial Realized]

theorem nonExhaustive [inst : BundledRichStructured Bare Realized] :
    NonExhaustive (BundledRich.toRCS inst.bundled) :=
  BundledRich.nonExhaustive inst.bundled

theorem not_minimalExhaustive [inst : BundledRichStructured Bare Realized] :
    ¬MinimalExhaustive (BundledRich.toRCS inst.bundled) :=
  BundledRich.not_minimalExhaustive inst.bundled

theorem nonExhaustive_toRCS [inst : BundledRichStructured Bare Realized] :
    NonExhaustive (StructuredReflectiveCertificationSystem.toRCS (BundledRich.base inst.bundled)) :=
  BundledRich.nonExhaustive inst.bundled

end BundledRichStructured

end ReflexiveArchitecture.Universal.Strong
