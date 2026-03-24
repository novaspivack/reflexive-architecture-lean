/-
  EPIC_021 — **IC discharge** into `AdequateReflectiveSystem`.

  Two distinct `RoleSeparatedSkeleton`s with the same `SummitComponentExtraction`
  yield the **witness diversity** data required by the summit class.
-/

import InfinityCompression.MetaProof.CanonicalCertification
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import ReflexiveArchitecture.Universal.Instances.ICInstance
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Summit

open InfinityCompression.Meta
open InfinityCompression.MetaProof
open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Instances

variable {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)

/-- **IC → Adequate:** two distinct role-separated skeletons supply the witness-diversity
fields of `AdequateReflectiveSystem`. -/
def icAdequateReflectiveSystem (H : SummitComponentExtraction A)
    (r₁ r₂ : RoleSeparatedSkeleton A) (hne : r₁ ≠ r₂) :
    AdequateReflectiveSystem AdmissibleSummitDerivation (ReflectiveMirrorWitness A) where
  compare := (icReflectiveCertificationSystem A H).compare
  Canonical := (icReflectiveCertificationSystem A H).Canonical
  Sound := (icReflectiveCertificationSystem A H).Sound
  witness₁ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₁ H
  witness₂ := ReflectiveMirrorWitness.fromRolesAndExtraction_standard r₂ H
  witnesses_distinct := reflective_mirror_from_roles_ne_of_roles_ne r₁ r₂ H hne
  witnesses_certify_same := ic_compare_eq_standard_witnesses A H r₁ r₂

/-- The adequate system forgets to the same `RCS` as the IC instance. -/
theorem icAdequateReflectiveSystem_toRCS (H : SummitComponentExtraction A)
    (r₁ r₂ : RoleSeparatedSkeleton A) (hne : r₁ ≠ r₂) :
    (icAdequateReflectiveSystem A H r₁ r₂ hne).toRCS = icReflectiveCertificationSystem A H :=
  rfl

/-- **IC summit universality:** the IC adequate system is non-exhaustive. -/
theorem ic_adequate_nonExhaustive (H : SummitComponentExtraction A)
    (r₁ r₂ : RoleSeparatedSkeleton A) (hne : r₁ ≠ r₂) :
    NonExhaustive (icAdequateReflectiveSystem A H r₁ r₂ hne).toRCS :=
  adequate_nonExhaustive _

end ReflexiveArchitecture.Universal.Summit
