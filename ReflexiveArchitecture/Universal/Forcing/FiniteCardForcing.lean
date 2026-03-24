/-
  EPIC_019 — Route 1 (strengthen the class): a **finite cardinality gap** between
  realized witnesses and bare certificates forces a collision for `compare`.

  This is one honest **Theorem B**-shaped result: the hypothesis is *structural* (sizes),
  not the conclusion `NonExhaustive` in disguise. It rules out identity-style collapse
  whenever `Realized` and `Bare` are both finite and there are strictly more realizations
  than bare values.

  Main Mathlib input: `Fintype.exists_ne_map_eq_of_card_lt` (pigeonhole).
-/

import Mathlib.Data.Fintype.Pigeonhole
import ReflexiveArchitecture.Universal.ExhaustionDefinitions

universe u

namespace ReflexiveArchitecture.Universal.Forcing

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-- Finite **richness** data: an RCS together with a proof that there are more realized
values than bare ones (hence `compare` cannot be injective). -/
structure FiniteCardRichRCS (Bare Realized : Type u) [Fintype Realized] [Fintype Bare] where
  system : ReflectiveCertificationSystem Bare Realized
  /-- Strictly more realizations than bare certificates — pigeonhole input. -/
  card_gap : Fintype.card Bare < Fintype.card Realized

theorem nonExhaustive_of_finiteCardRichRCS [Fintype Realized] [Fintype Bare]
    (H : FiniteCardRichRCS Bare Realized) :
    NonExhaustive H.system := by
  rcases Fintype.exists_ne_map_eq_of_card_lt H.system.compare H.card_gap with
    ⟨x, y, hne, heq⟩
  exact ⟨x, y, hne, heq⟩

theorem not_minimalExhaustive_of_finiteCardRichRCS [Fintype Realized] [Fintype Bare]
    (H : FiniteCardRichRCS Bare Realized) :
    ¬MinimalExhaustive H.system :=
  (nonExhaustive_iff_not_minimal H.system).1 (nonExhaustive_of_finiteCardRichRCS H)

/-- Standalone pigeonhole lemma for an abstract `ReflectiveCertificationSystem` (no bundle). -/
theorem nonExhaustive_of_fintype_card_lt [Fintype Realized] [Fintype Bare]
    (S : ReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : NonExhaustive S := by
  exact nonExhaustive_of_finiteCardRichRCS ⟨S, h⟩

theorem not_minimalExhaustive_of_fintype_card_lt [Fintype Realized] [Fintype Bare]
    (S : ReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : ¬MinimalExhaustive S :=
  (nonExhaustive_iff_not_minimal S).1 (nonExhaustive_of_fintype_card_lt S h)

end ReflexiveArchitecture.Universal.Forcing
