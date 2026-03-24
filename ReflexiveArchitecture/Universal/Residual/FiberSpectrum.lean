/-
  EPIC_030+ — **Fiber-size spectrum** and global resolution cost.

  The fiber-size spectrum characterizes how "spread out" the residual is.
  For finite types, the system is exhaustive iff every fiber has at most one
  element, and non-exhaustion implies some fiber has size ≥ 2.
-/

import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Fiber triviality predicates -/

/-- A fiber over `b` is **trivial** if it contains at most one element. -/
def FiberTrivial (b : Bare) : Prop :=
  ∀ x y : Realized, S.compare x = b → S.compare y = b → x = y

/-- A fiber over `b` is **nontrivial** if it contains at least two distinct elements. -/
def FiberNontrivial (b : Bare) : Prop :=
  ∃ x y : Realized, x ≠ y ∧ S.compare x = b ∧ S.compare y = b

theorem fiberNontrivial_iff_not_trivial (b : Bare) :
    FiberNontrivial S b ↔ ¬FiberTrivial S b := by
  constructor
  · rintro ⟨x, y, hne, hx, hy⟩ htriv
    exact hne (htriv x y hx hy)
  · intro h
    by_contra hall
    apply h
    intro x y hx hy
    by_contra hne
    exact hall ⟨x, y, hne, hx, hy⟩

/-- **Spectrum characterization of exhaustion:** the system is exhaustive iff
every fiber is trivial. -/
theorem exhaustive_iff_all_fibers_trivial :
    MinimalExhaustive S ↔ ∀ b, FiberTrivial S b := by
  constructor
  · intro hinj b x y hx hy
    exact hinj (hx.trans hy.symm)
  · intro htriv x y heq
    exact htriv (S.compare x) x y rfl heq.symm

/-- **Spectrum characterization of non-exhaustion:** the system is non-exhaustive
iff some fiber is nontrivial. -/
theorem nonExhaustive_iff_exists_nontrivial_fiber' :
    NonExhaustive S ↔ ∃ b, FiberNontrivial S b := by
  constructor
  · rintro ⟨x, y, hne, heq⟩
    exact ⟨S.compare x, x, y, hne, rfl, heq.symm⟩
  · rintro ⟨b, x, y, hne, hx, hy⟩
    exact ⟨x, y, hne, hx.trans hy.symm⟩

/-! ### Nontrivial fiber count -/

/-- The **nontrivial fiber locus**: the set of bare certificates with nontrivial fibers. -/
def NontrivialLocus : Set Bare :=
  { b | FiberNontrivial S b }

/-- The nontrivial locus is nonempty iff the system is non-exhaustive. -/
theorem nontrivialLocus_nonempty_iff :
    (∃ b, b ∈ NontrivialLocus S) ↔ NonExhaustive S :=
  (nonExhaustive_iff_exists_nontrivial_fiber' S).symm

/-- The nontrivial locus is empty iff the system is exhaustive. -/
theorem nontrivialLocus_empty_iff :
    NontrivialLocus S = ∅ ↔ MinimalExhaustive S := by
  constructor
  · intro hempty
    rw [exhaustive_iff_all_fibers_trivial]
    intro b
    by_contra hnt
    have : b ∈ NontrivialLocus S :=
      (fiberNontrivial_iff_not_trivial S b).2 hnt
    rw [hempty] at this
    exact this.elim
  · intro hexh
    ext b
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hnt
    have := (fiberNontrivial_iff_not_trivial S b).1 hnt
    exact this ((exhaustive_iff_all_fibers_trivial S).1 hexh b)

/-! ### Adequate systems have nontrivial spectrum -/

/-- An adequate system has at least one nontrivial fiber (the canonical one). -/
theorem adequate_has_nontrivial_fiber (A : AdequateReflectiveSystem Bare Realized) :
    FiberNontrivial A.toRCS (A.compare A.witness₁) :=
  ⟨A.witness₁, A.witness₂, A.witnesses_distinct, rfl, A.witnesses_certify_same.symm⟩

/-- The canonical fiber of an adequate system is in the nontrivial locus. -/
theorem adequate_canonical_in_nontrivialLocus (A : AdequateReflectiveSystem Bare Realized) :
    A.compare A.witness₁ ∈ NontrivialLocus A.toRCS :=
  adequate_has_nontrivial_fiber A

/-! ### Kernel-fiber connection -/

/-- The kernel is nonempty iff the nontrivial locus is nonempty. -/
theorem kernel_nonempty_iff_nontrivialLocus :
    (∃ p, p ∈ ResidualKernel S) ↔ (∃ b, b ∈ NontrivialLocus S) := by
  rw [residualKernel_nonempty_iff, nonExhaustive_iff_exists_nontrivial_fiber']
  rfl

end ReflexiveArchitecture.Universal.Residual
