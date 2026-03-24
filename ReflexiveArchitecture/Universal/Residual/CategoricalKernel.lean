/-
  EPIC_029+ — **Categorical characterization** of the residual kernel.

  The residual kernel is the **off-diagonal of the fiber product**: the fiber
  product `Realized ×_Bare Realized = {(x,y) | compare x = compare y}` minus
  the diagonal `{(x,x)}`. This connects the abstract residual theory to the
  classical categorical notion of kernel pair / fiber product.
-/

import ReflexiveArchitecture.Universal.Residual.ResidualKernel

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Fiber product -/

/-- The **fiber product** of `compare` with itself: all pairs `(x, y)` with
`compare x = compare y`. This is `Realized ×_Bare Realized` in categorical
language. -/
def FiberProduct : Set (Realized × Realized) :=
  { p | S.compare p.1 = S.compare p.2 }

/-- The **diagonal** of `Realized`: all pairs `(x, x)`. -/
def Diagonal : Set (Realized × Realized) :=
  { p | p.1 = p.2 }

/-- **Categorical characterization:** the residual kernel is the fiber product
minus the diagonal. -/
theorem residualKernel_eq_fiberProduct_minus_diagonal :
    ResidualKernel S = FiberProduct S \ Diagonal (Realized := Realized) := by
  ext ⟨x, y⟩
  simp only [ResidualKernel, FiberProduct, Diagonal, Set.mem_diff, Set.mem_setOf_eq]
  exact ⟨fun ⟨hne, heq⟩ => ⟨heq, hne⟩, fun ⟨heq, hne⟩ => ⟨hne, heq⟩⟩

/-- The fiber product contains the diagonal. -/
theorem diagonal_subset_fiberProduct :
    Diagonal (Realized := Realized) ⊆ FiberProduct S := by
  intro ⟨x, y⟩ heq
  simp [Diagonal] at heq
  simp [FiberProduct, heq]

/-- The fiber product is the disjoint union of the diagonal and the kernel. -/
theorem fiberProduct_eq_diagonal_union_kernel :
    FiberProduct S = Diagonal (Realized := Realized) ∪ ResidualKernel S := by
  ext ⟨x, y⟩
  simp only [FiberProduct, Diagonal, ResidualKernel, Set.mem_union, Set.mem_setOf_eq]
  constructor
  · intro heq
    by_cases hxy : x = y
    · exact Or.inl hxy
    · exact Or.inr ⟨hxy, heq⟩
  · rintro (rfl | ⟨_, heq⟩)
    · rfl
    · exact heq

/-- The diagonal and kernel are disjoint. -/
theorem diagonal_inter_kernel_empty :
    Diagonal (Realized := Realized) ∩ ResidualKernel S = ∅ := by
  ext ⟨x, y⟩
  simp only [Set.mem_inter_iff, Diagonal, ResidualKernel, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false]
  rintro ⟨rfl, hne, _⟩
  exact hne rfl

/-- **Exhaustion iff fiber product = diagonal:** the system is exhaustive iff
every fiber-product pair is on the diagonal. -/
theorem exhaustive_iff_fiberProduct_eq_diagonal :
    MinimalExhaustive S ↔ FiberProduct S = Diagonal (Realized := Realized) := by
  constructor
  · intro hinj
    ext ⟨x, y⟩
    simp only [FiberProduct, Diagonal, Set.mem_setOf_eq]
    exact ⟨fun heq => hinj heq, fun heq => heq ▸ rfl⟩
  · intro heq x y hcmp
    have hmem : (x, y) ∈ FiberProduct S := hcmp
    rw [heq] at hmem
    simp [Diagonal] at hmem
    exact hmem

end ReflexiveArchitecture.Universal.Residual
