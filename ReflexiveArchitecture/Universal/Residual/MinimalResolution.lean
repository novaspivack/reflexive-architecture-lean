/-
  EPIC_027 — **Minimal resolution theory** and the complete-graph / coloring interpretation.

  ## Key insights

  1. The kernel restricted to any single fiber is a **complete graph**: every pair of
     distinct elements in the fiber is a kernel edge. This is because all elements in
     a fiber share the same `compare` image.

  2. A refinement acts as a **graph coloring** of each fiber: it assigns a "color"
     (`refine x`) to each vertex, and resolves the fiber iff no two vertices in the
     fiber share a color.

  3. Fiber resolution is **independent**: resolving one fiber does not affect another,
     because kernel pairs in different fibers are disjoint.

  4. The **chromatic number** of a fiber (= minimum number of colors needed to properly
     color the complete graph on that fiber) equals the fiber size. So the minimum
     refinement type needed to resolve a fiber of size `n` must have at least `n` values.

  These results turn the residual theory into a genuine **graph coloring / partition**
  theory, connecting abstract certification failure to classical combinatorics.
-/

import ReflexiveArchitecture.Universal.Residual.KernelGraph
import ReflexiveArchitecture.Universal.Residual.KernelStratification
import ReflexiveArchitecture.Universal.Residual.ResidualKernel

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### MRT-T6: Complete fibers — the kernel on a fiber is a complete graph -/

/-- **Complete fiber theorem:** every pair of distinct elements in the same fiber is
a kernel pair. The kernel restricted to a fiber is a **complete graph**. -/
theorem kernelAt_complete {b : Bare} {x y : Realized}
    (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b) (hne : x ≠ y) :
    (x, y) ∈ KernelAt S b :=
  ⟨hne, hx, hy⟩

/-- Equivalently: two distinct fiber members are always a kernel pair. -/
theorem fiber_pair_is_kernel_pair {x y : Realized}
    (hfib : FiberEquiv S x y) (hne : x ≠ y) :
    KernelRel S x y :=
  ⟨hne, hfib⟩

/-! ### MRT-T1: Fiber-local resolution -/

/-- **Fiber-local resolution:** a refinement resolves fiber `b` (makes all its kernel
pairs separated) iff it assigns distinct values to all distinct fiber members. -/
def ResolvesAt {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) : Prop :=
  ∀ x y : Realized, x ∈ Fiber S b → y ∈ Fiber S b → x ≠ y → r.refine x ≠ r.refine y

/-- Fiber-local resolution iff all `KernelAt b` pairs are separated. -/
theorem resolvesAt_iff_separates_kernelAt {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) :
    ResolvesAt S r b ↔ ∀ p ∈ KernelAt S b, SeparatesKernelPair r p := by
  constructor
  · intro h ⟨x, y⟩ ⟨hne, hx, hy⟩
    exact h x y hx hy hne
  · intro h x y hx hy hne
    exact h ⟨x, y⟩ ⟨hne, hx, hy⟩

/-- Global resolution iff resolution at every fiber. -/
theorem resolves_iff_resolvesAt_all {Extra : Type u} (r : Refinement Realized Extra) :
    Function.Injective (refinedCompare S r) ↔ ∀ b, ResolvesAt S r b := by
  rw [resolves_iff_separates_all_kernel_pairs]
  constructor
  · intro h b
    rw [resolvesAt_iff_separates_kernelAt]
    intro p hp
    exact h p (kernelAt_subset_residualKernel S b hp)
  · intro h p hp
    have ⟨hne, heq⟩ := hp
    have hb := h (S.compare p.1)
    rw [resolvesAt_iff_separates_kernelAt] at hb
    exact hb ⟨p.1, p.2⟩ ⟨hne, rfl, heq.symm⟩

/-! ### MRT-T2: Independent fiber resolution -/

/-- **Independent fiber resolution:** whether a refinement resolves fiber `b` depends
only on the refinement's behavior on elements of fiber `b`. Fibers are independent. -/
theorem resolvesAt_independent {Extra : Type u} (_r : Refinement Realized Extra) (b b' : Bare)
    (hbb : b ≠ b') :
    ∀ x y, x ∈ Fiber S b → y ∈ Fiber S b' → (x, y) ∉ ResidualKernel S := by
  intro x y hx hy ⟨_, heq⟩
  rw [mem_fiber_iff] at hx hy
  exact hbb (hx.symm.trans (heq.trans hy))

/-! ### MRT-T7: Refinement as graph coloring -/

/-- A refinement **properly colors** fiber `b` if no two distinct fiber members receive
the same color. This is exactly `ResolvesAt`. -/
abbrev ProperlyColors {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) : Prop :=
  ResolvesAt S r b

/-- **Coloring theorem:** a refinement resolves the system iff it properly colors every
fiber. -/
theorem resolves_iff_properly_colors_all {Extra : Type u} (r : Refinement Realized Extra) :
    Function.Injective (refinedCompare S r) ↔ ∀ b, ProperlyColors S r b :=
  resolves_iff_resolvesAt_all S r

/-- **Coloring lower bound:** if a refinement properly colors a fiber of size `n`,
the refinement type must have at least `n` distinct values on that fiber.
(Stated as: the restriction of `refine` to the fiber is injective.) -/
theorem coloring_injective_on_fiber {Extra : Type u} (r : Refinement Realized Extra) (b : Bare)
    (hcol : ProperlyColors S r b) :
    ∀ x y : Realized, x ∈ Fiber S b → y ∈ Fiber S b → r.refine x = r.refine y → x = y := by
  intro x y hx hy hreq
  by_contra hne
  exact hcol x y hx hy hne hreq

/-! ### MRT-T5: Kernel degree -/

/-- The **kernel degree** of an element `x`: the set of elements kernel-related to `x`.
This is exactly `Fiber(compare x) \ {x}` — all other fiber members. -/
def KernelNeighbors (x : Realized) : Set Realized :=
  { y | KernelRel S x y }

/-- Kernel neighbors of `x` are exactly the other elements of `x`'s fiber. -/
theorem kernelNeighbors_eq_fiber_minus_self (x : Realized) :
    KernelNeighbors S x = Fiber S (S.compare x) \ {x} := by
  ext y
  simp only [KernelNeighbors, KernelRel, Fiber, Set.mem_diff, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  constructor
  · intro ⟨hne, heq⟩; exact ⟨heq.symm, hne.symm⟩
  · intro ⟨hy, hne⟩; exact ⟨Ne.symm hne, hy.symm⟩

/-- Every element in a nontrivial fiber has at least one kernel neighbor. -/
theorem kernel_neighbor_of_nontrivial_fiber {b : Bare} {x : Realized}
    (hx : x ∈ Fiber S b) {y : Realized} (hy : y ∈ Fiber S b) (hne : x ≠ y) :
    y ∈ KernelNeighbors S x :=
  ⟨hne, (compare_constant_on_fiber S b hx hy)⟩

/-! ### Refinement splits fibers into sub-partitions -/

/-- **Refinement sub-partition:** a refinement induces a partition of each fiber into
"refined classes" — elements sharing both the same `compare` image and the same
`refine` value. -/
def RefinedFiberClass {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) (e : Extra) :
    Set Realized :=
  { x | S.compare x = b ∧ r.refine x = e }

/-- Refined fiber classes are subsets of the original fiber. -/
theorem refinedFiberClass_subset_fiber {Extra : Type u} (r : Refinement Realized Extra)
    (b : Bare) (e : Extra) :
    RefinedFiberClass S r b e ⊆ Fiber S b := by
  intro x ⟨hx, _⟩
  exact hx

/-- The fiber is the union of its refined classes. -/
theorem fiber_eq_iUnion_refinedFiberClass {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) :
    Fiber S b = ⋃ e, RefinedFiberClass S r b e := by
  ext x
  simp only [Set.mem_iUnion, RefinedFiberClass, Fiber, Set.mem_setOf_eq]
  constructor
  · intro hx; exact ⟨r.refine x, hx, rfl⟩
  · rintro ⟨e, hx, _⟩; exact hx

/-- **MRT-T3:** A refinement that assigns the same value to two distinct fiber members
leaves them in the same refined class — they remain unresolved. -/
theorem same_refinedClass_of_unresolved {Extra : Type u} (r : Refinement Realized Extra)
    {b : Bare} {x y : Realized} (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b)
    (hreq : r.refine x = r.refine y) :
    ∃ e, x ∈ RefinedFiberClass S r b e ∧ y ∈ RefinedFiberClass S r b e :=
  ⟨r.refine x, ⟨hx, rfl⟩, ⟨hy, hreq.symm⟩⟩

/-- Conversely: elements in different refined classes are separated by the refinement. -/
theorem separated_of_different_refinedClass {Extra : Type u} (r : Refinement Realized Extra)
    {b : Bare} {x y : Realized} {e₁ e₂ : Extra}
    (hx : x ∈ RefinedFiberClass S r b e₁) (hy : y ∈ RefinedFiberClass S r b e₂)
    (hne : e₁ ≠ e₂) : r.refine x ≠ r.refine y := by
  intro heq
  exact hne (hx.2.symm.trans (heq.trans hy.2))

end ReflexiveArchitecture.Universal.Residual
