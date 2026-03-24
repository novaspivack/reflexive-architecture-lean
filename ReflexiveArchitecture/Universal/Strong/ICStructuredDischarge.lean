/-
  EPIC_020 — IC summit mirror packaged as `StructuredReflectiveCertificationSystem` when both
  carriers are **nontrivial**.

  * `ReflectiveMirrorWitness A` is **nontrivial** as soon as there exist two distinct
    `RoleSeparatedSkeleton A` values (same extraction `H`): see
    `nontrivial_reflectiveMirrorWitness_of_distinct_roles`.

  * `AdmissibleSummitDerivation` nontriviality is **architecture-dependent**; supply it as a
    typeclass assumption when your instance admits two distinct bare derivations.
-/

import InfinityCompression.MetaProof.CanonicalCertification
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import Mathlib.Logic.Nontrivial.Defs
import ReflexiveArchitecture.Universal.Instances.ICInstance
import ReflexiveArchitecture.Universal.Strong.StructuredRCS

universe u

namespace ReflexiveArchitecture.Universal.Strong

open InfinityCompression.Meta
open InfinityCompression.MetaProof
open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Instances

variable {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)

theorem nontrivial_reflectiveMirrorWitness_of_distinct_roles
    (r₁ r₂ : RoleSeparatedSkeleton A) (hne : r₁ ≠ r₂) (H : SummitComponentExtraction A) :
    Nontrivial (ReflectiveMirrorWitness A) :=
  ⟨⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₁ H,
      ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₂ H,
      reflective_mirror_from_roles_ne_of_roles_ne r₁ r₂ H hne⟩⟩

variable [Nontrivial (AdmissibleSummitDerivation)] [Nontrivial (ReflectiveMirrorWitness A)]

/-- IC universal `RCS` as a **structured** carrier (requires both nontrivial instances). -/
def icStructuredReflectiveCertificationSystem (H : SummitComponentExtraction A) :
    StructuredReflectiveCertificationSystem (AdmissibleSummitDerivation) (ReflectiveMirrorWitness A) :=
  { compare := (icReflectiveCertificationSystem A H).compare
    Canonical := (icReflectiveCertificationSystem A H).Canonical
    Sound := (icReflectiveCertificationSystem A H).Sound }

theorem icStructuredReflectiveCertificationSystem_toRCS (H : SummitComponentExtraction A) :
    (icStructuredReflectiveCertificationSystem A H).toRCS = icReflectiveCertificationSystem A H :=
  rfl

end ReflexiveArchitecture.Universal.Strong
