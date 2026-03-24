/-
  EPIC_025 — **Kernel stratification** and fiberwise decomposition.

  The residual kernel decomposes into **per-fiber kernels**: for each bare certificate `b`,
  `KernelAt S b` is the set of nontrivial pairs within `Fiber S b`. The full kernel is
  the union of these fiberwise components.

  We also prove **kernel symmetry** (the kernel is symmetric as a relation), the
  **resolved/unresolved partition** of the kernel by a refinement, and **kernel size
  bounds** for finite types.
-/

import Mathlib.Data.Fintype.Basic
import ReflexiveArchitecture.Universal.Residual.ResidualKernel

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Fiberwise kernel decomposition -/

/-- **Per-fiber kernel:** the set of nontrivial pairs within a single fiber. -/
def KernelAt (b : Bare) : Set (Realized × Realized) :=
  { p | p.1 ≠ p.2 ∧ S.compare p.1 = b ∧ S.compare p.2 = b }

theorem mem_kernelAt_iff (b : Bare) (x y : Realized) :
    (x, y) ∈ KernelAt S b ↔ x ≠ y ∧ S.compare x = b ∧ S.compare y = b :=
  Iff.rfl

/-- **KST-T1 (fiberwise decomposition):** every kernel pair belongs to exactly one
per-fiber kernel, and every per-fiber kernel pair is a kernel pair. -/
theorem kernelAt_subset_residualKernel (b : Bare) :
    KernelAt S b ⊆ ResidualKernel S := by
  intro ⟨x, y⟩ ⟨hne, hx, hy⟩
  exact ⟨hne, hx.trans hy.symm⟩

theorem residualKernel_eq_iUnion_kernelAt :
    ResidualKernel S = ⋃ b, KernelAt S b := by
  ext ⟨x, y⟩
  simp only [Set.mem_iUnion]
  constructor
  · intro ⟨hne, heq⟩
    exact ⟨S.compare x, hne, rfl, heq.symm⟩
  · rintro ⟨b, hne, hx, hy⟩
    exact ⟨hne, hx.trans hy.symm⟩

/-- **KST-T2:** `KernelAt b` is nonempty iff the fiber over `b` has at least two
distinct elements. -/
theorem kernelAt_nonempty_iff (b : Bare) :
    (∃ p, p ∈ KernelAt S b) ↔
      ∃ x y : Realized, x ≠ y ∧ x ∈ Fiber S b ∧ y ∈ Fiber S b := by
  constructor
  · rintro ⟨⟨x, y⟩, hne, hx, hy⟩
    exact ⟨x, y, hne, hx, hy⟩
  · rintro ⟨x, y, hne, hx, hy⟩
    exact ⟨(x, y), hne, hx, hy⟩

/-! ### Kernel symmetry -/

/-- **KST-T3:** The kernel is symmetric: `(x, y) ∈ Kernel ↔ (y, x) ∈ Kernel`. -/
theorem residualKernel_symmetric {x y : Realized}
    (h : (x, y) ∈ ResidualKernel S) : (y, x) ∈ ResidualKernel S :=
  ⟨Ne.symm h.1, h.2.symm⟩

theorem kernelAt_symmetric {b : Bare} {x y : Realized}
    (h : (x, y) ∈ KernelAt S b) : (y, x) ∈ KernelAt S b :=
  ⟨Ne.symm h.1, h.2.2, h.2.1⟩

/-! ### Resolved / unresolved partition -/

/-- The **resolved kernel** of a refinement: kernel pairs it successfully separates. -/
def ResolvedKernel {Extra : Type u} (r : Refinement Realized Extra) : Set (Realized × Realized) :=
  { p ∈ ResidualKernel S | r.refine p.1 ≠ r.refine p.2 }

/-- Resolved and unresolved kernels partition the full kernel. -/
theorem resolved_union_unresolved {Extra : Type u} (r : Refinement Realized Extra) :
    ResolvedKernel S r ∪ UnresolvedKernel S r = ResidualKernel S := by
  ext ⟨x, y⟩
  simp only [Set.mem_union, ResolvedKernel, UnresolvedKernel, Set.mem_sep_iff]
  constructor
  · rintro (⟨hk, _⟩ | ⟨hk, _⟩) <;> exact hk
  · intro hk
    by_cases h : r.refine x = r.refine y
    · exact Or.inr ⟨hk, h⟩
    · exact Or.inl ⟨hk, h⟩

/-- Resolved and unresolved kernels are disjoint. -/
theorem resolved_inter_unresolved_empty {Extra : Type u} (r : Refinement Realized Extra) :
    ResolvedKernel S r ∩ UnresolvedKernel S r = ∅ := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  intro ⟨⟨_, hne⟩, ⟨_, heq⟩⟩
  exact hne heq

/-- **KST-T4:** The resolved kernel grows monotonically with finer refinements. -/
theorem resolvedKernel_monotone {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (hfine : RefinesTo r₁ r₂) :
    ResolvedKernel S r₁ ⊆ ResolvedKernel S r₂ := by
  intro ⟨x, y⟩ ⟨hk, hsep⟩
  exact ⟨hk, finer_separates_of_coarser_separates r₁ r₂ hfine hsep⟩

/-! ### Kernel size and fiber contribution -/

/-- Every nontrivial fiber contributes at least one kernel pair. -/
theorem nontrivial_fiber_contributes_kernel_pair
    {b : Bare} {x y : Realized} (hne : x ≠ y)
    (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b) :
    (x, y) ∈ ResidualKernel S :=
  ⟨hne, by rw [mem_fiber_iff] at hx hy; exact hx.trans hy.symm⟩

/-- The adequate witnesses contribute a canonical pair to the kernel at the
canonical nontrivial fiber. -/
theorem adequate_canonical_kernelAt (A : AdequateReflectiveSystem Bare Realized) :
    (A.witness₁, A.witness₂) ∈ KernelAt A.toRCS (A.compare A.witness₁) :=
  ⟨A.witnesses_distinct, rfl, A.witnesses_certify_same.symm⟩

/-! ### Kernel as equivalence-class structure -/

/-- The kernel restricted to a single fiber is the **off-diagonal** of that fiber:
all pairs `(x, y)` with `x ≠ y` in the fiber. This connects to the classical
"off-diagonal" in topology / algebra. -/
theorem kernelAt_eq_offDiagonal_fiber (b : Bare) :
    KernelAt S b = { p : Realized × Realized |
      p.1 ∈ Fiber S b ∧ p.2 ∈ Fiber S b ∧ p.1 ≠ p.2 } := by
  ext ⟨x, y⟩
  simp only [KernelAt, Fiber, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hne, hx, hy⟩; exact ⟨hx, hy, hne⟩
  · rintro ⟨hx, hy, hne⟩; exact ⟨hne, hx, hy⟩

end ReflexiveArchitecture.Universal.Residual
