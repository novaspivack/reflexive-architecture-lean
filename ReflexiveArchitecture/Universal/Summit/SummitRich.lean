/-
  EPIC_021 — **Summit-rich formal class** (honest maximum at the abstract universal layer).

  The disjunctive union of the three EPIC_020 **bundled forcing** patterns (`BundledRich`)
  is the strongest *proved* “∀ members → `NonExhaustive`” story available without a false
  `∀ ReflectiveCertificationSystem` or smuggled predicates.

  *Mathematical honesty:* this is **not** a single new axiom weaker than `SelfLocationGap`
  that forces non-exhaustion for all “philosophically rich” systems; that remains research.
  What *is* formal is: **membership in `SummitRichReflectiveSystem`** (alias of `BundledRich`)
  **implies** non-exhaustion, with a thesis-level name `summit_universality`.
-/

import ReflexiveArchitecture.Universal.Strong.RichStructuredClasses

universe u

namespace ReflexiveArchitecture.Universal.Summit

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Strong

variable {Bare Realized : Type u}

/-- EPIC_021 summit carrier: same inductive data as `BundledRich` (finite pigeonhole,
infinite→finite, or self-location gap on a structured `RCS`). -/
abbrev SummitRichReflectiveSystem (Bare Realized : Type u) [Nontrivial Bare] [Nontrivial Realized] :=
  BundledRich Bare Realized

theorem inevitability_of_summitRich [Nontrivial Bare] [Nontrivial Realized]
    (m : SummitRichReflectiveSystem Bare Realized) : NonExhaustive (BundledRich.toRCS m) :=
  BundledRich.nonExhaustive m

/-- Thesis-style name: every summit-rich witness is non-exhaustive at the `RCS` layer. -/
theorem summit_universality [Nontrivial Bare] [Nontrivial Realized]
    (m : SummitRichReflectiveSystem Bare Realized) : NonExhaustive (BundledRich.toRCS m) :=
  inevitability_of_summitRich m

theorem summit_not_minimal [Nontrivial Bare] [Nontrivial Realized]
    (m : SummitRichReflectiveSystem Bare Realized) : ¬MinimalExhaustive (BundledRich.toRCS m) :=
  BundledRich.not_minimalExhaustive m

/-- Forgetful map to minimal `RCS` (same as `BundledRich.toRCS`). -/
abbrev summitToRCS [Nontrivial Bare] [Nontrivial Realized] (m : SummitRichReflectiveSystem Bare Realized) :
    ReflectiveCertificationSystem Bare Realized :=
  BundledRich.toRCS m

@[simp]
theorem summitToRCS_eq [Nontrivial Bare] [Nontrivial Realized] (m : SummitRichReflectiveSystem Bare Realized) :
    summitToRCS m = BundledRich.toRCS m :=
  rfl

/-- Typeclass alias: packaged summit witness (same as `BundledRichStructured`). -/
abbrev SummitRichStructured := BundledRichStructured

variable [Nontrivial Bare] [Nontrivial Realized]

theorem summitRichStructured_nonExhaustive [inst : SummitRichStructured Bare Realized] :
    NonExhaustive (BundledRich.toRCS inst.bundled) :=
  BundledRichStructured.nonExhaustive

theorem summitRichStructured_not_minimal [inst : SummitRichStructured Bare Realized] :
    ¬MinimalExhaustive (BundledRich.toRCS inst.bundled) :=
  BundledRichStructured.not_minimalExhaustive

end ReflexiveArchitecture.Universal.Summit
