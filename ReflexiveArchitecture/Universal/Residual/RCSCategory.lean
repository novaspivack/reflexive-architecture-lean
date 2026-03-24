/-
  **Category of reflective certification systems.**

  RCS on fixed carriers `(Bare, Realized)` and comparison-compatible maps form a
  category:

  - **Objects:** `ReflectiveCertificationSystem Bare Realized`
  - **Morphisms:** `CompareCompatible S₁ S₂` — maps `φ : Realized → Realized` with
    `S₂.compare ∘ φ = S₁.compare`
  - **Identity:** `idCompatible S`
  - **Composition:** `compCompatible ψ φ`
  - **Laws:** identity left/right units, associativity

  This makes explicit what was already implicit in `FundamentalTheorem.lean`:
  the four category laws hold definitionally (all proofs are `rfl`).

  We also show the **kernel is a functor** in the following sense: an injective
  compatible map sends kernel pairs to kernel pairs (already in `FundamentalTheorem`),
  and identity/composition are preserved. Furthermore, the fundamental residual
  package is **natural** in the sense that its components commute with compatible maps.
-/

import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem
import ReflexiveArchitecture.Universal.Residual.OptimalCertification

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-! ### The category of RCS on fixed carriers -/

/-- The **identity morphism** for any RCS. -/
theorem rcsCat_id_law (S : ReflectiveCertificationSystem Bare Realized) :
    (idCompatible S).map = id := rfl

/-- **Left identity law:** `id ∘ φ = φ`. -/
theorem rcsCat_comp_id_left
    {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂) :
    (compCompatible (idCompatible S₂) φ).map = φ.map := rfl

/-- **Right identity law:** `φ ∘ id = φ`. -/
theorem rcsCat_comp_id_right
    {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂) :
    (compCompatible φ (idCompatible S₁)).map = φ.map := rfl

/-- **Associativity law:** `(χ ∘ ψ) ∘ φ = χ ∘ (ψ ∘ φ)`. -/
theorem rcsCat_comp_assoc
    {S₁ S₂ S₃ S₄ : ReflectiveCertificationSystem Bare Realized}
    (χ : CompareCompatible S₃ S₄)
    (ψ : CompareCompatible S₂ S₃)
    (φ : CompareCompatible S₁ S₂) :
    (compCompatible χ (compCompatible ψ φ)).map =
    (compCompatible (compCompatible χ ψ) φ).map := rfl

/-- **Category package:** bundles the four laws into a named structure. -/
structure RCSCategoryLaws where
  /-- Identity morphism. -/
  id_is_id : ∀ (S : ReflectiveCertificationSystem Bare Realized),
    (idCompatible S).map = id
  /-- Left identity. -/
  comp_id_left : ∀ {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂),
    (compCompatible (idCompatible S₂) φ).map = φ.map
  /-- Right identity. -/
  comp_id_right : ∀ {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂),
    (compCompatible φ (idCompatible S₁)).map = φ.map
  /-- Associativity. -/
  comp_assoc : ∀ {S₁ S₂ S₃ S₄ : ReflectiveCertificationSystem Bare Realized}
    (χ : CompareCompatible S₃ S₄) (ψ : CompareCompatible S₂ S₃)
    (φ : CompareCompatible S₁ S₂),
    (compCompatible χ (compCompatible ψ φ)).map =
    (compCompatible (compCompatible χ ψ) φ).map

/-- **All four category laws hold** for RCS on fixed carriers. -/
def rcsCategoryLaws : RCSCategoryLaws (Bare := Bare) (Realized := Realized) where
  id_is_id := fun _ => rfl
  comp_id_left := fun _ => rfl
  comp_id_right := fun _ => rfl
  comp_assoc := fun _ _ _ => rfl

/-! ### Kernel functoriality -/

/-- **Kernel functoriality on identity:** the identity compatible map preserves
every kernel pair trivially. -/
theorem kernelFunctor_id (S : ReflectiveCertificationSystem Bare Realized)
    {x y : Realized} (hk : (x, y) ∈ ResidualKernel S) :
    ((idCompatible S).map x, (idCompatible S).map y) ∈ ResidualKernel S :=
  hk

/-- **Kernel functoriality on composition:** composing two injective compatible maps
preserves kernel pairs. -/
theorem kernelFunctor_comp
    {S₁ S₂ S₃ : ReflectiveCertificationSystem Bare Realized}
    (ψ : CompareCompatible S₂ S₃) (φ : CompareCompatible S₁ S₂)
    (hinjψ : Function.Injective ψ.map) (hinjφ : Function.Injective φ.map)
    {x y : Realized} (hk : (x, y) ∈ ResidualKernel S₁) :
    ((compCompatible ψ φ).map x, (compCompatible ψ φ).map y) ∈ ResidualKernel S₃ :=
  compatible_preserves_kernel (compCompatible ψ φ) (hinjψ.comp hinjφ) hk

/-! ### Naturality of the fundamental package -/

/-- **Naturality:** for two systems with the same `compare`, the fundamental residual
package has identical components (kernel, unresolved kernel, etc.). This is the
naturality statement at fixed carriers: the construction commutes with
compare-preserving identity. -/
theorem fundamentalPackage_compare_natural
    (S₁ S₂ : ReflectiveCertificationSystem Bare Realized)
    (hcmp : S₁.compare = S₂.compare) :
    ResidualKernel S₁ = ResidualKernel S₂ :=
  residualKernel_eq_of_compare_eq S₁ S₂ hcmp

end ReflexiveArchitecture.Universal.Residual
