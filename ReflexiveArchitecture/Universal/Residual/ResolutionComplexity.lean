/-
  EPIC_028 — **Resolution complexity**, residual invariants, and refinement dynamics.
-/

import ReflexiveArchitecture.Universal.Residual.MinimalResolution
import ReflexiveArchitecture.Universal.Residual.KernelStratification
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### RCI-T1: Per-fiber resolution complexity -/

/-- **Per-fiber lower bound:** resolving fiber `b` forces `refine` to be injective
on that fiber. -/
theorem resolving_injective_on_fiber {Extra : Type u} (r : Refinement Realized Extra) (b : Bare)
    (hres : ResolvesAt S r b) :
    ∀ x y : Realized, x ∈ Fiber S b → y ∈ Fiber S b → r.refine x = r.refine y → x = y :=
  coloring_injective_on_fiber S r b hres

/-! ### RCI-T4: Refinement progress -/

/-- **Refinement progress:** if a refinement separates at least one kernel pair that
another does not, its unresolved kernel is strictly smaller. -/
theorem strict_progress_of_new_separation {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (hfine : RefinesTo r₁ r₂)
    (hnew : ∃ p ∈ ResidualKernel S, r₁.refine p.1 = r₁.refine p.2 ∧ r₂.refine p.1 ≠ r₂.refine p.2) :
    UnresolvedKernel S r₂ ⊂ UnresolvedKernel S r₁ := by
  constructor
  · exact unresolvedKernel_antitone S r₁ r₂ hfine
  · intro heq
    rcases hnew with ⟨⟨x, y⟩, hk, hr1eq, hr2ne⟩
    have hmem : (x, y) ∈ UnresolvedKernel S r₁ := ⟨hk, hr1eq⟩
    have hmem2 : (x, y) ∈ UnresolvedKernel S r₂ := heq hmem
    exact hr2ne hmem2.2

/-! ### RCI-T6: Terminal refinement characterization -/

/-- A refined class is a **singleton** at `(b, e)` if it contains at most one element. -/
def RefinedClassSingleton {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) (e : Extra) : Prop :=
  ∀ x y : Realized, x ∈ RefinedFiberClass S r b e → y ∈ RefinedFiberClass S r b e → x = y

/-- **Terminal refinement:** a refinement is terminal (fully resolving) iff every
refined class is a singleton. -/
theorem terminal_iff_all_singletons {Extra : Type u} (r : Refinement Realized Extra) :
    Function.Injective (refinedCompare S r) ↔
      ∀ b e, RefinedClassSingleton S r b e := by
  constructor
  · intro hinj b e x y ⟨hxb, hxe⟩ ⟨hyb, hye⟩
    exact hinj (by simp [refinedCompare, hxb, hyb, hxe, hye])
  · intro hsing x y heq
    simp [refinedCompare, Prod.mk.injEq] at heq
    exact hsing (S.compare x) (r.refine x) x y ⟨rfl, rfl⟩ ⟨heq.1.symm, heq.2.symm⟩

/-! ### RCI-T5: Monotone class refinement (structural) -/

/-- Finer refinements produce **finer** partitions: if `r₂` refines `r₁`, then
every `r₂`-class is contained in some `r₁`-class (when the `r₂`-class is nonempty). -/
theorem finer_refines_classes {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (hfine : RefinesTo r₁ r₂) (b : Bare) (e₂ : E₂)
    {x : Realized} (hx : x ∈ RefinedFiberClass S r₂ b e₂) :
    RefinedFiberClass S r₂ b e₂ ⊆ RefinedFiberClass S r₁ b (r₁.refine x) := by
  intro y ⟨hyb, hye⟩
  refine ⟨hyb, ?_⟩
  have h2eq : r₂.refine x = r₂.refine y := by rw [hx.2, hye]
  exact (hfine x y h2eq).symm

/-! ### Refinement chain bound -/

/-- **Empty unresolved ⇒ resolved:** restated for convenience. -/
theorem resolved_of_empty_unresolved {Extra : Type u} (r : Refinement Realized Extra)
    (hempty : UnresolvedKernel S r = ∅) :
    Function.Injective (refinedCompare S r) :=
  (resolves_iff_unresolvedKernel_empty S r).2 hempty

/-! ### Adequate resolution complexity -/

/-- For adequate systems: resolving the canonical fiber requires distinguishing the
two witnesses — so any resolving refinement must assign them different values. -/
theorem adequate_resolution_requires_distinct_witnesses
    (A : AdequateReflectiveSystem Bare Realized) {Extra : Type u}
    (r : Refinement Realized Extra) (hres : ResolvesAt A.toRCS r (A.compare A.witness₁)) :
    r.refine A.witness₁ ≠ r.refine A.witness₂ := by
  apply hres A.witness₁ A.witness₂
  · simp [Fiber]
  · simp [Fiber, A.witnesses_certify_same.symm]
  · exact A.witnesses_distinct

/-- Adequate systems cannot be resolved by a constant refinement. -/
theorem adequate_not_resolved_by_constant
    (A : AdequateReflectiveSystem Bare Realized) {Extra : Type u}
    (r : Refinement Realized Extra) (hconst : ∀ x y : Realized, r.refine x = r.refine y) :
    ¬Function.Injective (refinedCompare A.toRCS r) := by
  rw [resolves_iff_resolvesAt_all]
  push_neg
  refine ⟨A.compare A.witness₁, fun hres => ?_⟩
  exact adequate_resolution_requires_distinct_witnesses A r hres (hconst _ _)

end ReflexiveArchitecture.Universal.Residual
