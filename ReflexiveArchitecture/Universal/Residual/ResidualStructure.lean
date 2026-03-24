/-
  EPIC_022 — **Residual structure theorems** (RFG-T1, T2, T4 family).

  Given a `compare : Realized → Bare` that is **not** injective, we study the
  structure of fibers `Fib(b) = compare⁻¹(b)`.

  ## Theorems

  ### RFG-T1 (invariant structure)
  Any predicate on `Realized` that is **determined by** `compare` (i.e., factors
  through `Bare`) is constant on each fiber. Conversely, any predicate that
  **varies** on a fiber is **invisible** to bare certification.

  ### RFG-T2 (residual necessity)
  If a fiber is nontrivial, there exists a **distinguishing predicate** — a function
  `Realized → Bool` that separates two fiber members. (This is a constructive
  consequence of `x ≠ y`.)

  ### RFG-T4 (refinement)
  Adjoining a **refinement** `refine : Realized → Extra` to the comparison map
  shrinks fibers: `Fib_{(compare, refine)}(b, e) ⊆ Fib_{compare}(b)`.
  Strict shrinkage occurs when the refinement separates fiber members.
-/

import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.FiberBasics
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### RFG-T1: Residual exclusion / invariant structure -/

/-- A predicate on `Realized` is **bare-determined** if it factors through `compare`. -/
def BareDetermined (P : Realized → Prop) : Prop :=
  ∃ Q : Bare → Prop, ∀ x, P x ↔ Q (S.compare x)

/-- **RFG-T1 (exclusion):** bare-determined predicates are constant on each fiber.
If `P` factors through `compare`, then `P x ↔ P y` for all `x, y` in the same fiber. -/
theorem bareDetermined_constant_on_fiber {P : Realized → Prop} (hP : BareDetermined S P)
    {b : Bare} {x y : Realized} (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b) :
    P x ↔ P y := by
  rcases hP with ⟨Q, hQ⟩
  rw [mem_fiber_iff] at hx hy
  rw [hQ x, hQ y, hx, hy]

/-- Contrapositive of RFG-T1: if a predicate **distinguishes** two fiber members,
it is **not** bare-determined — it sees residual structure invisible to `compare`. -/
theorem not_bareDetermined_of_fiber_distinguishing {P : Realized → Prop}
    {b : Bare} {x y : Realized} (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b)
    (hPx : P x) (hPy : ¬P y) : ¬BareDetermined S P := by
  intro hbd
  exact hPy ((bareDetermined_constant_on_fiber S hbd hx hy).1 hPx)

/-! ### RFG-T2: Residual necessity -/

/-- **RFG-T2 (necessity):** if a fiber contains two distinct points, there exists a
predicate on `Realized` that **separates** them (and is therefore not bare-determined).
This is a consequence of `x ≠ y` in a type with decidable equality, or classically
for any type. -/
theorem exists_separating_predicate_of_fiber_nontrivial
    {b : Bare} {x y : Realized} (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b) (hne : x ≠ y) :
    ∃ P : Realized → Prop, P x ∧ ¬P y ∧ ¬BareDetermined S P := by
  refine ⟨fun z => z = x, rfl, hne.symm, ?_⟩
  intro ⟨Q, hQ⟩
  have h1 := (hQ x).1 rfl
  rw [mem_fiber_iff] at hx hy
  rw [hx, ← hy] at h1
  exact hne.symm ((hQ y).2 h1)

/-- **RFG-T2 (global):** non-exhaustion implies existence of a non-bare-determined
predicate — there is **always** residual structure invisible to `compare`. -/
theorem exists_non_bareDetermined_of_nonExhaustive (h : NonExhaustive S) :
    ∃ P : Realized → Prop, ¬BareDetermined S P := by
  rcases h with ⟨x, y, hne, heq⟩
  have hx : x ∈ Fiber S (S.compare x) := by simp [Fiber]
  have hy : y ∈ Fiber S (S.compare x) := by simp [Fiber, heq]
  rcases exists_separating_predicate_of_fiber_nontrivial S hx hy hne with ⟨P, _, _, hP⟩
  exact ⟨P, hP⟩

/-! ### RFG-T4: Refinement -/

/-- A **refinement** of the comparison: an extra map `refine : Realized → Extra` that
provides additional information beyond `compare`. -/
structure Refinement (Realized Extra : Type u) where
  refine : Realized → Extra

/-- The **refined comparison** `(compare, refine)` maps `Realized → Bare × Extra`. -/
def refinedCompare {Extra : Type u} (r : Refinement Realized Extra) (x : Realized) :
    Bare × Extra :=
  (S.compare x, r.refine x)

/-- Fiber of the refined comparison. -/
def RefinedFiber {Extra : Type u} (r : Refinement Realized Extra) (be : Bare × Extra) :
    Set Realized :=
  { x | refinedCompare S r x = be }

/-- **RFG-T4 (refinement inclusion):** refined fibers are subsets of original fibers. -/
theorem refinedFiber_subset_fiber {Extra : Type u} (r : Refinement Realized Extra)
    (b : Bare) (e : Extra) : RefinedFiber S r (b, e) ⊆ Fiber S b := by
  intro x hx
  simp [RefinedFiber, refinedCompare, Fiber] at hx ⊢
  exact hx.1

/-- **RFG-T4 (strict shrinkage):** if the refinement separates two fiber members,
they land in **different** refined fibers. -/
theorem refinement_separates_fiber {Extra : Type u} (r : Refinement Realized Extra)
    {b : Bare} {x y : Realized} (_hx : x ∈ Fiber S b) (_hy : y ∈ Fiber S b)
    (hsep : r.refine x ≠ r.refine y) :
    refinedCompare S r x ≠ refinedCompare S r y := by
  intro heq
  simp [refinedCompare, Prod.mk.injEq] at heq
  exact hsep heq.2

/-- **RFG-T4 (refinement reduces non-exhaustion):** if a refinement separates all
nontrivial fiber pairs, the refined comparison is injective. -/
theorem refined_injective_of_total_separation {Extra : Type u} (r : Refinement Realized Extra)
    (hsep : ∀ x y : Realized, x ≠ y → S.compare x = S.compare y →
      r.refine x ≠ r.refine y) :
    Function.Injective (refinedCompare S r) := by
  intro x y heq
  simp [refinedCompare, Prod.mk.injEq] at heq
  by_contra hne
  exact hsep x y hne heq.1 heq.2

end ReflexiveArchitecture.Universal.Residual
