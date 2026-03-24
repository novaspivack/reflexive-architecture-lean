/-
  EPIC_024 — **Residual kernel** and the veil theorem.

  The **residual kernel** of a comparison map is the set of nontrivial fiber pairs:
  `{(x, y) | x ≠ y ∧ compare x = compare y}`. This is the **core** of the residual —
  the totality of what certification cannot distinguish.

  ## Key results

  - The kernel is nonempty iff `NonExhaustive`.
  - The kernel is intrinsic to `compare` (independent of witnesses, canonical region, etc.).
  - A refinement resolves the system iff it separates every kernel pair.
  - The **unresolved kernel** of a refinement (pairs it fails to separate) is monotone
    in the refinement preorder: finer refinements have smaller unresolved kernels.
  - **Veil theorem:** for adequate systems, the kernel is nonempty and no trivial
    refinement can empty it.
  - **Kernel-observable duality:** a predicate is non-bare-determined iff it separates
    at least one kernel pair.
-/

import ReflexiveArchitecture.Universal.Residual.FiberResidual
import ReflexiveArchitecture.Universal.Residual.ObservableAlgebra
import ReflexiveArchitecture.Universal.Residual.ResidualStructure
import ReflexiveArchitecture.Universal.Residual.RefinementOrder
import ReflexiveArchitecture.Universal.Residual.Incompressibility
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### The residual kernel -/

/-- The **residual kernel**: the set of ordered pairs `(x, y)` of distinct realizations
with the same bare certificate. This is the totality of what `compare` cannot distinguish. -/
def ResidualKernel : Set (Realized × Realized) :=
  { p | p.1 ≠ p.2 ∧ S.compare p.1 = S.compare p.2 }

theorem mem_residualKernel_iff (x y : Realized) :
    (x, y) ∈ ResidualKernel S ↔ x ≠ y ∧ S.compare x = S.compare y :=
  Iff.rfl

/-- **RDT-T2:** The kernel is nonempty iff the system is non-exhaustive. -/
theorem residualKernel_nonempty_iff :
    (∃ p, p ∈ ResidualKernel S) ↔ NonExhaustive S := by
  constructor
  · rintro ⟨⟨x, y⟩, hne, heq⟩
    exact ⟨x, y, hne, heq⟩
  · rintro ⟨x, y, hne, heq⟩
    exact ⟨(x, y), hne, heq⟩

/-- **RDT-T3:** The kernel depends only on `compare`. -/
theorem residualKernel_eq_of_compare_eq (S₁ S₂ : ReflectiveCertificationSystem Bare Realized)
    (hcmp : S₁.compare = S₂.compare) :
    ResidualKernel S₁ = ResidualKernel S₂ := by
  ext ⟨x, y⟩
  simp [ResidualKernel, hcmp]

/-! ### Refinement resolution via kernel separation -/

/-- A refinement **separates** a kernel pair if it assigns different values. -/
def SeparatesKernelPair {Extra : Type u} (r : Refinement Realized Extra)
    (p : Realized × Realized) : Prop :=
  r.refine p.1 ≠ r.refine p.2

/-- **RDT-T4:** A refinement resolves the system (makes refined comparison injective) iff
it separates every kernel pair. -/
theorem resolves_iff_separates_all_kernel_pairs {Extra : Type u} (r : Refinement Realized Extra) :
    Function.Injective (refinedCompare S r) ↔
      ∀ p ∈ ResidualKernel S, SeparatesKernelPair r p := by
  constructor
  · intro hinj ⟨x, y⟩ ⟨hne, heq⟩
    simp [SeparatesKernelPair]
    intro hreq
    have : x = y := hinj (by simp [refinedCompare, heq, hreq])
    exact hne this
  · intro hsep x y heq
    by_contra hne
    simp [refinedCompare, Prod.mk.injEq] at heq
    have hk : (x, y) ∈ ResidualKernel S := ⟨hne, heq.1⟩
    exact hsep ⟨x, y⟩ hk heq.2

/-! ### Unresolved kernel -/

/-- The **unresolved kernel** of a refinement: kernel pairs it fails to separate. -/
def UnresolvedKernel {Extra : Type u} (r : Refinement Realized Extra) : Set (Realized × Realized) :=
  { p ∈ ResidualKernel S | r.refine p.1 = r.refine p.2 }

theorem mem_unresolvedKernel_iff {Extra : Type u} (r : Refinement Realized Extra)
    (x y : Realized) :
    (x, y) ∈ UnresolvedKernel S r ↔
      x ≠ y ∧ S.compare x = S.compare y ∧ r.refine x = r.refine y := by
  simp [UnresolvedKernel, ResidualKernel, and_assoc]

/-- The unresolved kernel is a subset of the full kernel. -/
theorem unresolvedKernel_subset {Extra : Type u} (r : Refinement Realized Extra) :
    UnresolvedKernel S r ⊆ ResidualKernel S := by
  intro p hp
  exact hp.1

/-- **RDT-T5 (monotonicity):** finer refinements have smaller unresolved kernels. -/
theorem unresolvedKernel_antitone {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (hfine : RefinesTo r₁ r₂) :
    UnresolvedKernel S r₂ ⊆ UnresolvedKernel S r₁ := by
  intro ⟨x, y⟩ ⟨hk, hreq⟩
  exact ⟨hk, hfine x y hreq⟩

/-- The trivial refinement leaves the entire kernel unresolved. -/
theorem unresolvedKernel_trivial :
    UnresolvedKernel S (trivialRefinement (Realized := Realized)) = ResidualKernel S := by
  ext ⟨x, y⟩
  simp [UnresolvedKernel, trivialRefinement]

/-- The identity refinement resolves everything: its unresolved kernel is empty. -/
theorem unresolvedKernel_identity_empty :
    UnresolvedKernel S (identityRefinement (Realized := Realized)) = ∅ := by
  ext ⟨x, y⟩
  simp [UnresolvedKernel, identityRefinement, ResidualKernel]
  intro hne _
  exact hne

/-- A refinement resolves iff its unresolved kernel is empty. -/
theorem resolves_iff_unresolvedKernel_empty {Extra : Type u} (r : Refinement Realized Extra) :
    Function.Injective (refinedCompare S r) ↔ UnresolvedKernel S r = ∅ := by
  rw [resolves_iff_separates_all_kernel_pairs]
  constructor
  · intro hsep
    ext ⟨x, y⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨hk, hreq⟩
    exact (hsep ⟨x, y⟩ hk) hreq
  · intro hempty ⟨x, y⟩ hk
    simp [SeparatesKernelPair]
    intro heq
    have hmem : (x, y) ∈ UnresolvedKernel S r := ⟨hk, heq⟩
    rw [hempty] at hmem
    exact hmem.elim

/-! ### The veil theorem -/

/-- **Veil theorem (EPIC_024):** for any adequate system, the residual kernel is
nonempty — the veil has substance. -/
theorem adequate_kernel_nonempty (A : AdequateReflectiveSystem Bare Realized) :
    ∃ p, p ∈ ResidualKernel A.toRCS :=
  (residualKernel_nonempty_iff A.toRCS).2 (adequate_nonExhaustive A)

/-- **Veil persistence:** the trivial refinement leaves the adequate kernel fully intact. -/
theorem adequate_veil_persists_trivial (A : AdequateReflectiveSystem Bare Realized) :
    UnresolvedKernel A.toRCS (trivialRefinement (Realized := Realized)) = ResidualKernel A.toRCS :=
  unresolvedKernel_trivial A.toRCS

/-- **Veil theorem (strong form):** the adequate witnesses are a canonical kernel pair. -/
theorem adequate_witnesses_in_kernel (A : AdequateReflectiveSystem Bare Realized) :
    (A.witness₁, A.witness₂) ∈ ResidualKernel A.toRCS :=
  ⟨A.witnesses_distinct, A.witnesses_certify_same⟩

/-! ### Kernel-observable duality -/

/-- **RDT-T8 (kernel-observable duality, forward):** if a predicate separates a kernel pair,
it is not bare-determined. -/
theorem not_bareDetermined_of_separates_kernel {P : Realized → Prop}
    {x y : Realized} (hk : (x, y) ∈ ResidualKernel S)
    (hPx : P x) (hPy : ¬P y) : ¬BareDetermined S P := by
  intro ⟨Q, hQ⟩
  have heq := hk.2
  have h1 := (hQ x).1 hPx
  rw [heq] at h1
  exact hPy ((hQ y).2 h1)

/-- **RDT-T8 (kernel-observable duality, reverse):** if a predicate is not bare-determined,
it separates some kernel pair (classically). -/
theorem separates_kernel_of_not_bareDetermined {P : Realized → Prop}
    (hP : ¬BareDetermined S P) :
    ∃ x y, (x, y) ∈ ResidualKernel S ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y) := by
  by_contra hall
  push_neg at hall
  apply hP
  refine ⟨fun b => ∀ x, S.compare x = b → P x, fun x => ?_⟩
  constructor
  · intro hPx y heq
    by_contra hPy
    have hne : x ≠ y := fun heqxy => hPy (heqxy ▸ hPx)
    have hk : (x, y) ∈ ResidualKernel S := ⟨hne, heq.symm⟩
    rcases hall x y hk with ⟨h1, _⟩
    exact hPy (h1 hPx)
  · intro hQ
    exact hQ x rfl

/-- **Kernel-observable duality (biconditional):** a predicate is non-bare-determined iff
it separates at least one kernel pair. -/
theorem not_bareDetermined_iff_separates_kernel (P : Realized → Prop) :
    ¬BareDetermined S P ↔
      ∃ x y, (x, y) ∈ ResidualKernel S ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y) := by
  constructor
  · exact separates_kernel_of_not_bareDetermined S
  · rintro ⟨x, y, hk, hPxy⟩
    rcases hPxy with ⟨hPx, hPy⟩ | ⟨hPx, hPy⟩
    · exact not_bareDetermined_of_separates_kernel S hk hPx hPy
    · exact not_bareDetermined_of_separates_kernel S
        (show (y, x) ∈ ResidualKernel S from ⟨(Ne.symm hk.1), hk.2.symm⟩) hPy hPx

/-! ### Residual transfer -/

/-- **RDT-T7 (residual transfer):** two systems with the same `compare` have identical
residual kernels, identical unresolved kernels for any refinement, and identical
incompressibility at any type. -/
theorem residualTransfer_unresolvedKernel
    (S₁ S₂ : ReflectiveCertificationSystem Bare Realized)
    (hcmp : S₁.compare = S₂.compare) {Extra : Type u} (r : Refinement Realized Extra) :
    UnresolvedKernel S₁ r = UnresolvedKernel S₂ r := by
  ext ⟨x, y⟩
  simp [UnresolvedKernel, ResidualKernel, hcmp]

theorem residualTransfer_incompressibleAt
    (S₁ S₂ : ReflectiveCertificationSystem Bare Realized)
    (hcmp : S₁.compare = S₂.compare) (Extra : Type u) :
    IncompressibleAt S₁ Extra ↔ IncompressibleAt S₂ Extra := by
  simp [IncompressibleAt, UnresolvedBy]
  have hrceq : ∀ (r : Refinement Realized Extra),
      refinedCompare S₁ r = refinedCompare S₂ r := by
    intro r; funext x
    show (S₁.compare x, r.refine x) = (S₂.compare x, r.refine x)
    congr 1
    exact congr_fun hcmp x
  constructor <;> intro h r hinj <;> apply h r
  · rwa [hrceq]
  · rwa [← hrceq]

end ReflexiveArchitecture.Universal.Residual
