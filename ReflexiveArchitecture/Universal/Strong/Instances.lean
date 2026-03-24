/-
  EPIC_020 — Inhabitants of `StructuredReflectiveCertificationSystem` (toy + reuse of EPIC_019
  product projection).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.Strong.Inevitability
import ReflexiveArchitecture.Universal.Summit.SummitRich
import ReflexiveArchitecture.Universal.Strong.RichStructuredClasses
import ReflexiveArchitecture.Universal.Strong.StructuredRCS

universe u

namespace ReflexiveArchitecture.Universal.Strong

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

instance nontrivial_bool_prod_bool : Nontrivial (Bool × Bool) :=
  ⟨⟨(true, false), (true, true), by simp [Ne]⟩⟩

/-- Toy product from EPIC_019, repackaged as a **structured** RCS (`Bool` and `Bool × Bool`
are both nontrivial). -/
def toyProductStructured : StructuredReflectiveCertificationSystem Bool (Bool × Bool) where
  compare := fun p => p.1
  Canonical := fun _ => True
  Sound := True

theorem fintype_card_bool_lt_bool_prod_bool : Fintype.card Bool < Fintype.card (Bool × Bool) := by
  classical
  simp [Fintype.card_prod, Fintype.card_bool]

theorem toyProductStructured_nonExhaustive : NonExhaustive toyProductStructured.toRCS :=
  inevitability_structured_finiteCard toyProductStructured fintype_card_bool_lt_bool_prod_bool

theorem toyProductStructured_not_minimal : ¬MinimalExhaustive toyProductStructured.toRCS :=
  (nonExhaustive_iff_not_minimal toyProductStructured.toRCS).1 toyProductStructured_nonExhaustive

/-- **Bundled rich class** inhabitant: same toy, with cardinal gap as a field — unconditional
`NonExhaustive` via `nonExhaustive_of_finitePigeonholeStructured`. -/
def toyFinitePigeonholeStructured : FinitePigeonholeStructured Bool (Bool × Bool) where
  base := toyProductStructured
  card_gap := fintype_card_bool_lt_bool_prod_bool

theorem toyFinitePigeonholeStructured_nonExhaustive :
    NonExhaustive (StructuredReflectiveCertificationSystem.toRCS toyFinitePigeonholeStructured.base) :=
  nonExhaustive_of_finitePigeonholeStructured toyFinitePigeonholeStructured

/-- Umbrella `BundledRichStructured` witness for the same toy (generic API smoke test). -/
instance toyBundledRichStructured : BundledRichStructured Bool (Bool × Bool) where
  bundled := .finitePigeonhole toyFinitePigeonholeStructured

theorem toyBundledRichStructured_nonExhaustive :
    NonExhaustive (BundledRich.toRCS toyBundledRichStructured.bundled) :=
  BundledRichStructured.nonExhaustive

/-- Same witness under EPIC_021 summit naming (`SummitRichReflectiveSystem`). -/
def toySummitRichReflectiveSystem : SummitRichReflectiveSystem Bool (Bool × Bool) :=
  toyBundledRichStructured.bundled

theorem toy_summit_universality :
    NonExhaustive (summitToRCS toySummitRichReflectiveSystem) :=
  summit_universality _

end ReflexiveArchitecture.Universal.Strong
