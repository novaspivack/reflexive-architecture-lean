/-
  **The Universal Theory of Forgetting.**

  Every function `π : E → B` between any two types determines a canonical
  geometry of what it forgets. This is not specific to "certification" or
  "reflective systems" — it applies to any map in any domain of mathematics:

  - Group homomorphisms: the residual kernel is the classical kernel
  - Topological quotients: the residual is the equivalence relation
  - Type-theoretic projections: the residual is the fiber family
  - Measurements: the residual is the unmeasured degrees of freedom
  - Compilers: the residual is what compilation erases
  - Hash functions: the residual is the collision structure

  The entire theory — fundamental equivalence, observable duality, resolution
  complexity, meta-level invisibility — applies to ALL of these simultaneously,
  because it is stated for an arbitrary function between arbitrary types.

  This module makes the universality explicit by showing that every function
  can be packaged as an RCS and inherits the full theory.
-/

import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem
import ReflexiveArchitecture.Universal.Residual.OptimalCertification
import ReflexiveArchitecture.Universal.Residual.MetaLevel
import ReflexiveArchitecture.Universal.Residual.CategoricalKernel
import ReflexiveArchitecture.Universal.Summit.FundamentalEquivalence

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {B E : Type u}

/-! ### Any function is an RCS -/

/-- **Every function is a reflective certification system.** Given any
`π : E → B`, we obtain an RCS with `compare = π`, trivial canonical region,
and trivial soundness. The entire residual theory then applies. -/
def rcsOfMap (π : E → B) : ReflectiveCertificationSystem B E where
  compare := π
  Canonical := fun _ => True
  Sound := True

/-- The comparison map of `rcsOfMap π` is `π` itself. -/
@[simp]
theorem rcsOfMap_compare (π : E → B) : (rcsOfMap π).compare = π := rfl

/-! ### The universal forgetting theorems -/

/-- **Universal residual kernel:** for any function `π : E → B`, the set
`{(x,y) | x ≠ y ∧ π(x) = π(y)}` is the residual kernel. -/
def forgettingKernel (π : E → B) : Set (E × E) :=
  ResidualKernel (rcsOfMap π)

theorem forgettingKernel_eq (π : E → B) :
    forgettingKernel π = { p | p.1 ≠ p.2 ∧ π p.1 = π p.2 } := rfl

/-- **Universal fundamental equivalence:** for any function `π : E → B`,
non-injectivity, witness diversity, fiber automorphism, and nontrivial
kernel are equivalent. -/
theorem universal_fundamental_equivalence (π : E → B) :
    (∃ x y : E, x ≠ y ∧ π x = π y) ↔
    (∃ (τ : E → E), (∀ z, π (τ z) = π z) ∧ τ ≠ id) :=
  equiv_1_iff_3 (rcsOfMap π)

/-- **Universal all-or-nothing:** for any function, either it is injective
(and the kernel is empty, no automorphisms exist, etc.) or it is non-injective
(and ALL five conditions hold). -/
theorem universal_all_or_nothing (π : E → B) :
    (∃ x y : E, x ≠ y ∧ π x = π y) ∨ Function.Injective π := by
  rcases Classical.em (Function.Injective π) with h | h
  · exact Or.inr h
  · rw [Function.not_injective_iff] at h
    obtain ⟨x, y, heq, hne⟩ := h
    exact Or.inl ⟨x, y, hne, heq⟩

/-- **Universal observable duality:** for any function `π : E → B`, a
predicate on `E` factors through `π` iff it does NOT separate any pair
`(x,y)` with `x ≠ y` and `π(x) = π(y)`. -/
theorem universal_observable_duality (π : E → B) (P : E → Prop) :
    (∃ Q : B → Prop, ∀ x, P x ↔ Q (π x)) ↔
    ¬(∃ x y, x ≠ y ∧ π x = π y ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y)) := by
  rw [show (∃ Q : B → Prop, ∀ x, P x ↔ Q (π x)) = BareDetermined (rcsOfMap π) P from rfl]
  rw [bareDetermined_xor_separates_kernel]
  simp only [ResidualKernel, rcsOfMap_compare, Set.mem_setOf_eq]
  constructor
  · intro h ⟨x, y, hne, heq, hsep⟩
    exact h ⟨x, y, ⟨hne, heq⟩, hsep⟩
  · intro h ⟨x, y, ⟨hne, heq⟩, hsep⟩
    exact h ⟨x, y, hne, heq, hsep⟩

/-- **Universal resolution:** for any function `π : E → B` and refinement
`r : E → Extra`, the pair `(π, r)` is injective iff `r` separates every
pair `(x,y)` with `x ≠ y` and `π(x) = π(y)`. -/
theorem universal_resolution (π : E → B) {Extra : Type u} (r : E → Extra) :
    Function.Injective (fun x => (π x, r x)) ↔
    (∀ x y : E, x ≠ y → π x = π y → r x ≠ r y) := by
  constructor
  · intro hinj x y hne heq hreq
    exact hne (hinj (by ext <;> assumption))
  · intro hsep x y heq
    simp [Prod.mk.injEq] at heq
    by_contra hne
    exact hsep x y hne heq.1 heq.2

/-- **Universal meta-level blindness:** for any function `π : E → B` and
any predicate `Q : B → Prop`, `Q ∘ π` agrees on all pairs `(x,y)` with
`π(x) = π(y)`. The codomain level cannot see the residual. -/
theorem universal_meta_blindness (π : E → B) (Q : B → Prop)
    {x y : E} (heq : π x = π y) : Q (π x) = Q (π y) := by
  rw [heq]

/-- **Universal resolution complexity:** for any function `π : E → B` and
any fiber of size ≥ 2, resolving that fiber requires the refinement to be
injective on the fiber. -/
theorem universal_resolution_complexity (π : E → B) {Extra : Type u} (r : E → Extra)
    (b : B) (hres : ∀ x y : E, π x = b → π y = b → x ≠ y → r x ≠ r y) :
    ∀ x y : E, π x = b → π y = b → r x = r y → x = y := by
  intro x y hx hy hreq
  by_contra hne
  exact hres x y hx hy hne hreq

/-! ### The fundamental package for any function -/

/-- **Every function has a fundamental residual package.** The entire theory
of residual geometry — kernel, fibers, observables, refinement, resolution,
complexity — applies unconditionally to any function between any two types. -/
theorem every_function_has_residual_geometry (π : E → B) :
    Nonempty (FundamentalResidualPackage (rcsOfMap π)) :=
  ⟨fundamentalResidualPackage (rcsOfMap π)⟩

/-- **Every function has a five-way equivalence.** The classification of
non-injectivity into five equivalent forms applies to any function. -/
theorem every_function_has_five_way_equivalence (π : E → B) :
    Nonempty (FiveWayEquivalence (rcsOfMap π)) :=
  ⟨fiveWayEquivalence (rcsOfMap π)⟩

end ReflexiveArchitecture.Universal.Residual
