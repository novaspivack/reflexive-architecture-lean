/-
  EPIC_019 — Route 1 (strengthen the class): if the **bare** carrier is a
  subsingleton but **realized** witnesses are nontrivial, then `compare` cannot be
  injective: all bare images agree, so distinct realizations collide.

  Degenerate bare interface plus plural realization, without assuming `NonExhaustive` as a hypothesis.
-/

import Mathlib.Logic.Nontrivial.Defs
import ReflexiveArchitecture.Universal.ExhaustionDefinitions

universe u

namespace ReflexiveArchitecture.Universal.Forcing

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

theorem nonExhaustive_of_subsingleton_bare_nontrivial_realized [Subsingleton Bare]
    [Nontrivial Realized] (S : ReflectiveCertificationSystem Bare Realized) :
    NonExhaustive S := by
  rcases exists_pair_ne Realized with ⟨x, y, hne⟩
  refine ⟨x, y, hne, ?_⟩
  exact Subsingleton.elim (S.compare x) (S.compare y)

theorem not_minimalExhaustive_of_subsingleton_bare_nontrivial_realized [Subsingleton Bare]
    [Nontrivial Realized] (S : ReflectiveCertificationSystem Bare Realized) :
    ¬MinimalExhaustive S :=
  (nonExhaustive_iff_not_minimal S).1 (nonExhaustive_of_subsingleton_bare_nontrivial_realized S)

/-- Bundle: subsingleton bare + nontrivial realized (no further fields). -/
structure SubsingletonBarePluralRealized (Bare Realized : Type u) [Subsingleton Bare]
    [Nontrivial Realized] where
  system : ReflectiveCertificationSystem Bare Realized

theorem nonExhaustive_of_subsingletonBarePlural [Subsingleton Bare] [Nontrivial Realized]
    (H : SubsingletonBarePluralRealized Bare Realized) : NonExhaustive H.system :=
  nonExhaustive_of_subsingleton_bare_nontrivial_realized H.system

end ReflexiveArchitecture.Universal.Forcing
