/-
  EPIC_019 — Phase IV (minimal): a “formal system” in the weakest sense is a type
  family plus a realization-to-bare map. **Extraction** builds a full
  `ReflectiveCertificationSystem` by choosing canonical-region and soundness data.

  This is intentionally minimal: it does **not** claim that every real-world formal
  system is *only* such a map — only that this data is **sufficient** to obtain an
  abstract RCS carrier for further reasoning.
-/

import ReflexiveArchitecture.Universal.Forcing.SubsingletonBareForcing
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal

open Forcing

variable {Bare Realized : Type u}

/-- Minimal raw data: one forgetful map `Realized → Bare`. -/
structure RawReflectiveFormalSystem (Bare Realized : Type u) where
  compare : Realized → Bare

/-- Extraction: extend raw data to a full `ReflectiveCertificationSystem` once
canonical and soundness predicates are chosen. -/
def RawReflectiveFormalSystem.toRCS {Bare Realized : Type u}
    (F : RawReflectiveFormalSystem Bare Realized)
    (Canonical : Bare → Prop) (Sound : Prop) : ReflectiveCertificationSystem Bare Realized :=
  { compare := F.compare, Canonical, Sound }

/-- **U2 (existence).** From any raw map and any canonical/soundness choice, some
associated `ReflectiveCertificationSystem` exists with that `compare`. -/
theorem exists_rcs_of_raw {Bare Realized : Type u} (F : RawReflectiveFormalSystem Bare Realized)
    (Canonical : Bare → Prop) (Sound : Prop) :
    ∃ S : ReflectiveCertificationSystem Bare Realized, S.compare = F.compare ∧
      S.Canonical = Canonical ∧ S.Sound = Sound :=
  ⟨F.toRCS Canonical Sound, rfl, rfl, rfl⟩

/-- Default extraction: canonical predicate and soundness both trivially `True`. -/
def RawReflectiveFormalSystem.toRCS_default {Bare Realized : Type u}
    (F : RawReflectiveFormalSystem Bare Realized) :
    ReflectiveCertificationSystem Bare Realized :=
  F.toRCS (fun _ => True) True

theorem toRCS_default_compare {Bare Realized : Type u} (F : RawReflectiveFormalSystem Bare Realized) :
    (F.toRCS_default).compare = F.compare :=
  rfl

/-- **Route 2 (extraction):** default RCS extension inherits `compare`; structural forcing on
the carriers (subsingleton bare + nontrivial realized) therefore yields `NonExhaustive`
for the extracted system. -/
theorem nonExhaustive_toRCS_default_of_subsingletonBare_nontrivialRealized [Subsingleton Bare]
    [Nontrivial Realized] (F : RawReflectiveFormalSystem Bare Realized) :
    NonExhaustive (F.toRCS_default) :=
  nonExhaustive_of_subsingleton_bare_nontrivial_realized (F.toRCS_default)

end ReflexiveArchitecture.Universal
