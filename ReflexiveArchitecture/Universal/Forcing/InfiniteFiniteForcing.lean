/-
  EPIC_019 — Route 1: **infinite** realized witnesses mapping into a **finite**
  bare carrier force a collision (infinite pigeonhole).

  Hypotheses: `[Infinite Realized] [Finite Bare]`. No `Fintype` cardinality
  inequality required.
-/

import Mathlib.Data.Fintype.Pigeonhole
import ReflexiveArchitecture.Universal.ExhaustionDefinitions

universe u

namespace ReflexiveArchitecture.Universal.Forcing

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

theorem nonExhaustive_of_infinite_realized_finite_bare [Infinite Realized] [Finite Bare]
    (S : ReflectiveCertificationSystem Bare Realized) : NonExhaustive S := by
  rcases Finite.exists_ne_map_eq_of_infinite S.compare with ⟨x, y, hne, heq⟩
  exact ⟨x, y, hne, heq⟩

theorem not_minimalExhaustive_of_infinite_realized_finite_bare [Infinite Realized] [Finite Bare]
    (S : ReflectiveCertificationSystem Bare Realized) : ¬MinimalExhaustive S :=
  (nonExhaustive_iff_not_minimal S).1 (nonExhaustive_of_infinite_realized_finite_bare S)

structure InfiniteRealizedFiniteBare (Bare Realized : Type u) [Infinite Realized]
    [Finite Bare] where
  system : ReflectiveCertificationSystem Bare Realized

theorem nonExhaustive_of_infiniteRealizedFiniteBare [Infinite Realized] [Finite Bare]
    (H : InfiniteRealizedFiniteBare Bare Realized) : NonExhaustive H.system :=
  nonExhaustive_of_infinite_realized_finite_bare H.system

end ReflexiveArchitecture.Universal.Forcing
