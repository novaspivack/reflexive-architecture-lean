/-
  EPIC_019 Phase II — Infinity Compression (summit mirror witness) as a
  `ReflectiveCertificationSystem`: bare = `AdmissibleSummitDerivation`, realized =
  `ReflectiveMirrorWitness`, compare = bridge derivation.

  This does not replace `CertificationLayer`; it is a **parallel universal interface**
  under which the same “upstairs multiplicity over collapsed bare record” phenomenon
  is expressed as abstract `NonExhaustive` (nontrivial fiber over the shared bare
  certificate).
-/

import InfinityCompression.MetaProof.CanonicalCertification
import InfinityCompression.MetaProof.ReflectiveMirrorWitness
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem
import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.FiberBasics

universe u

namespace ReflexiveArchitecture.Universal.Instances

open InfinityCompression.MetaProof
open InfinityCompression.Meta

variable {BD : Type u} {n : Nat} (A : CompressionArchitecture BD n)

/-- IC summit witnesses organized as a universal reflective certification system.

* `Bare` = bare summit derivation record.
* `Realized` = full reflective mirror witness (roles + bridge + shape bookkeeping).
* `compare` = forget witness to bare `AdmissibleSummitDerivation`.
* `Canonical` = suite predicate `IsCanonicalBareSummitCertification`.
* `Sound` = trivially `True` here; richer soundness predicates can refine this field
  in later phases without changing the carriers. -/
@[reducible]
def icReflectiveCertificationSystem (_H : SummitComponentExtraction A) :
    ReflectiveCertificationSystem (AdmissibleSummitDerivation) (ReflectiveMirrorWitness A) where
  compare := fun m => m.bridge.derivation
  Canonical := IsCanonicalBareSummitCertification
  Sound := True

theorem ic_compare_eq_standard_witnesses (H : SummitComponentExtraction A)
    (roles₁ roles₂ : RoleSeparatedSkeleton A) :
    (icReflectiveCertificationSystem A H).compare
        (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H) =
      (icReflectiveCertificationSystem A H).compare
        (ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H) := by
  dsimp [icReflectiveCertificationSystem]
  exact Eq.trans (reflective_mirror_bridge_derivation_eq_admissibleStandard roles₁ H)
    (Eq.symm (reflective_mirror_bridge_derivation_eq_admissibleStandard roles₂ H))

/-- Direct packaging: any two distinct witnesses with the same bare image are abstract
`NonExhaustive` (the same conjunct used in IC enriched-irreducibility statements). -/
theorem ic_nonExhaustive_of_witnesses (H : SummitComponentExtraction A)
    (w₁ w₂ : ReflectiveMirrorWitness A) (hne : w₁ ≠ w₂)
    (heq : w₁.bridge.derivation = w₂.bridge.derivation) :
    NonExhaustive (icReflectiveCertificationSystem A H) :=
  ⟨w₁, w₂, hne, heq⟩

/-- **Abstract non-exhaustion** from the IC standard role pair: two distinct skeletons
yield distinct witnesses but **identical** bare derivations (`admissibleStandard`). -/
theorem ic_nonExhaustive_of_distinct_roles (H : SummitComponentExtraction A)
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (hne : roles₁ ≠ roles₂) :
    NonExhaustive (icReflectiveCertificationSystem A H) := by
  refine
    ⟨ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₁ H,
      ReflectiveMirrorWitness.fromRolesAndExtraction_standard roles₂ H, ?_, ?_⟩
  · exact reflective_mirror_from_roles_ne_of_roles_ne roles₁ roles₂ H hne
  · exact ic_compare_eq_standard_witnesses A H roles₁ roles₂

theorem ic_not_minimalExhaustive_of_distinct_roles (H : SummitComponentExtraction A)
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (hne : roles₁ ≠ roles₂) :
    ¬MinimalExhaustive (icReflectiveCertificationSystem A H) :=
  (nonExhaustive_iff_not_minimal _).1 (ic_nonExhaustive_of_distinct_roles A H roles₁ roles₂ hne)

theorem ic_fiber_nontrivial_of_distinct_roles (H : SummitComponentExtraction A)
    (roles₁ roles₂ : RoleSeparatedSkeleton A) (hne : roles₁ ≠ roles₂) :
    ∃ b : AdmissibleSummitDerivation,
      ∃ x y : ReflectiveMirrorWitness A,
        x ≠ y ∧ x ∈ Fiber (icReflectiveCertificationSystem A H) b ∧
          y ∈ Fiber (icReflectiveCertificationSystem A H) b :=
  fiber_nontrivial_of_not_injective _ (ic_not_minimalExhaustive_of_distinct_roles A H roles₁ roles₂ hne)

end ReflexiveArchitecture.Universal.Instances
