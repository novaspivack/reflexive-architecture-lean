/-
  EPIC_020 — **Composed inevitability** (U5-style): `StructuredReflectiveCertificationSystem`
  plus EPIC_019 **forcing** hypotheses from `Universal/Forcing/`.

  This is strictly stronger than the bare dichotomy in the sense of EPIC_020 §2.C (A):
  conclusion is unconditional `NonExhaustive` on the **subclass** cut out by the forcing
  hypothesis (finite-card / infinite-finite / self-location gap), not merely
  `MinimalExhaustive ∨ NonExhaustive` for an arbitrary abstract `RCS`.
-/

import ReflexiveArchitecture.Universal.Forcing.FiniteCardForcing
import ReflexiveArchitecture.Universal.Forcing.InfiniteFiniteForcing
import ReflexiveArchitecture.Universal.Forcing.SelfLocationForcing
import ReflexiveArchitecture.Universal.Strong.StructuredRCS

universe u

namespace ReflexiveArchitecture.Universal.Strong

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Forcing

variable {Bare Realized : Type u}

/-- **U5 (finite-card wave):** structured + finite pigeonhole ⇒ `NonExhaustive`. -/
theorem inevitability_structured_finiteCard [Fintype Realized] [Fintype Bare] [Nontrivial Bare]
    [Nontrivial Realized] (S : StructuredReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : NonExhaustive S.toRCS :=
  nonExhaustive_of_fintype_card_lt S.toRCS h

theorem inevitability_structured_not_minimal_finiteCard [Fintype Realized] [Fintype Bare]
    [Nontrivial Bare] [Nontrivial Realized] (S : StructuredReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : ¬MinimalExhaustive S.toRCS :=
  not_minimalExhaustive_of_fintype_card_lt S.toRCS h

/-- **U5 (infinite→finite wave):** structured + infinite realized + finite bare ⇒ `NonExhaustive`. -/
theorem inevitability_structured_infiniteFinite [Infinite Realized] [Finite Bare] [Nontrivial Bare]
    [Nontrivial Realized] (S : StructuredReflectiveCertificationSystem Bare Realized) :
    NonExhaustive S.toRCS :=
  nonExhaustive_of_infinite_realized_finite_bare S.toRCS

theorem inevitability_structured_not_minimal_infiniteFinite [Infinite Realized] [Finite Bare]
    [Nontrivial Bare] [Nontrivial Realized] (S : StructuredReflectiveCertificationSystem Bare Realized) :
    ¬MinimalExhaustive S.toRCS :=
  not_minimalExhaustive_of_infinite_realized_finite_bare S.toRCS

/-- **U5 (self-location gap wave):** structured + `SelfLocationGap` ⇒ `NonExhaustive`. -/
theorem inevitability_structured_selfLocationGap [Nontrivial Bare] [Nontrivial Realized]
    (S : StructuredReflectiveCertificationSystem Bare Realized) (h : SelfLocationGap S.toRCS) :
    NonExhaustive S.toRCS :=
  nonExhaustive_of_selfLocationGap S.toRCS h

theorem inevitability_structured_not_minimal_selfLocationGap [Nontrivial Bare] [Nontrivial Realized]
    (S : StructuredReflectiveCertificationSystem Bare Realized) (h : SelfLocationGap S.toRCS) :
    ¬MinimalExhaustive S.toRCS :=
  not_minimalExhaustive_of_selfLocationGap S.toRCS h

end ReflexiveArchitecture.Universal.Strong
