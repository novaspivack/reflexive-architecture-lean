/-
  EPIC_026 — **Kernel graph theory** and the fiber-connectivity theorem.

  The residual kernel, viewed as a symmetric relation on `Realized`, has a natural
  graph structure. We prove the **fundamental connectivity theorem**: two elements
  are connected in the kernel graph (i.e., related by the reflexive-transitive closure
  of the kernel relation) if and only if they are in the same fiber.

  This means the **connected components** of the kernel graph are exactly the **fibers**
  of `compare`. The fiber partition is not just a convenient decomposition — it is the
  **intrinsic topology** of the residual.

  We also prove that the kernel relation, extended to include the diagonal (reflexive
  closure), is an **equivalence relation** — and it is exactly `FiberEquiv`.
-/

import ReflexiveArchitecture.Universal.Residual.FiberResidual
import ReflexiveArchitecture.Universal.Residual.ResidualKernel
import ReflexiveArchitecture.Universal.Residual.KernelStratification

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Kernel as a relation -/

/-- The kernel viewed as a binary relation on `Realized`. -/
def KernelRel (x y : Realized) : Prop :=
  x ≠ y ∧ S.compare x = S.compare y

/-- The **reflexive kernel relation**: same fiber OR equal. This is the full
fiber-equivalence relation. -/
def KernelRelRefl (x y : Realized) : Prop :=
  S.compare x = S.compare y

theorem kernelRelRefl_eq_fiberEquiv :
    KernelRelRefl S = FiberEquiv S := by
  ext x y
  rfl

/-- **RGQ-T7 (fundamental connectivity theorem):** the reflexive closure of the kernel
relation is exactly fiber equivalence. Two elements are "kernel-connected" (equal or
related by a kernel pair) iff they are in the same fiber. -/
theorem kernelRelRefl_iff_fiberEquiv (x y : Realized) :
    KernelRelRefl S x y ↔ FiberEquiv S x y :=
  Iff.rfl

/-- The kernel relation (without reflexivity) implies fiber equivalence. -/
theorem kernelRel_implies_fiberEquiv {x y : Realized} (h : KernelRel S x y) :
    FiberEquiv S x y :=
  h.2

/-- Fiber equivalence decomposes into: either equal, or a kernel pair. -/
theorem fiberEquiv_iff_eq_or_kernelRel (x y : Realized) :
    FiberEquiv S x y ↔ x = y ∨ KernelRel S x y := by
  constructor
  · intro h
    by_cases heq : x = y
    · exact Or.inl heq
    · exact Or.inr ⟨heq, h⟩
  · rintro (rfl | ⟨_, h⟩)
    · exact (fiberEquiv_equivalence S).refl x
    · exact h

/-- **Fiber = connected component:** the fiber over `b` is exactly the set of elements
reachable from any member via kernel pairs (or equality). -/
theorem fiber_eq_kernelRelRefl_class (b : Bare) (x : Realized) (hx : x ∈ Fiber S b) :
    Fiber S b = { y | KernelRelRefl S x y } := by
  ext z
  simp only [Fiber, KernelRelRefl, Set.mem_setOf_eq]
  rw [mem_fiber_iff] at hx
  constructor
  · intro hz; exact hx ▸ hz.symm
  · intro hz; exact (hx ▸ hz).symm

/-! ### Kernel relation is an equivalence (reflexive closure) -/

theorem kernelRelRefl_equivalence : Equivalence (KernelRelRefl S) :=
  fiberEquiv_equivalence S

/-! ### Kernel symmetry as a relation -/

theorem kernelRel_symmetric : Symmetric (KernelRel S) :=
  fun _ _ ⟨hne, heq⟩ => ⟨hne.symm, heq.symm⟩

/-! ### Transitivity of fiber membership through kernel -/

/-- If `(x, y)` and `(y, z)` are both kernel pairs, then `(x, z)` is either a kernel
pair or `x = z`. (Transitivity of fiber equivalence, restricted to kernel pairs.) -/
theorem kernelRel_trans_fiber {x y z : Realized}
    (hxy : KernelRel S x y) (hyz : KernelRel S y z) :
    FiberEquiv S x z :=
  hxy.2.trans hyz.2

/-- Stronger: if `x ≠ z`, then `(x, z)` is also a kernel pair. -/
theorem kernelRel_trans_ne {x y z : Realized}
    (hxy : KernelRel S x y) (hyz : KernelRel S y z) (hne : x ≠ z) :
    KernelRel S x z :=
  ⟨hne, hxy.2.trans hyz.2⟩

/-! ### Fiber partition from kernel graph -/

/-- The fiber partition is the **quotient** of `Realized` by the kernel's reflexive
closure (= fiber equivalence). This is the formal statement that fibers are exactly
the connected components of the kernel graph. -/
theorem fiber_partition_eq_kernelRelRefl_classes :
    ∀ b : Bare, ∀ x ∈ Fiber S b, ∀ y : Realized,
      y ∈ Fiber S b ↔ KernelRelRefl S x y := by
  intro b x hx y
  rw [mem_fiber_iff] at hx
  simp only [Fiber, KernelRelRefl, Set.mem_setOf_eq]
  constructor
  · intro hy; exact hx ▸ hy.symm
  · intro hy; exact (hx ▸ hy).symm

end ReflexiveArchitecture.Universal.Residual
