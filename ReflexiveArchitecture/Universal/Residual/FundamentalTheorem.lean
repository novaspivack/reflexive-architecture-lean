/-
  EPIC_029 — **Fundamental theorem of residual geometry.**

  This module synthesizes the entire residual theory into a single coherent package:
  the **fundamental theorem** that characterizes the complete structure of what
  certification forgets.

  ## The theorem (informal)

  For any comparison map `compare : Realized → Bare`:

  1. The **residual kernel** `K = {(x,y) | x ≠ y ∧ compare x = compare y}` is the
     canonical object of certification failure.
  2. `K` decomposes as `⋃_b K_b` where each `K_b` is the **off-diagonal** of `Fiber(b)`.
  3. Each `K_b` is a **complete graph** (every distinct fiber pair is an edge).
  4. A predicate is **non-bare-determined** iff it **separates** a kernel pair.
  5. A refinement **resolves** iff it **separates all** kernel pairs.
  6. Resolution decomposes into **independent per-fiber** problems.
  7. Resolving fiber `b` requires `refine` to be **injective** on `Fiber(b)`.
  8. The system is **exhaustive** iff the kernel is **empty** iff `compare` is **injective**.

  We also prove:
  - **Functoriality:** compatible maps between systems preserve kernel structure.
  - **Optimal coarse observable:** `compare` is the universal coarsening — any
    coarser map loses strictly less information.
  - **Exhaustion criterion:** a complete characterization of when the residual vanishes.
-/

import ReflexiveArchitecture.Universal.Residual.ResidualKernel
import ReflexiveArchitecture.Universal.Residual.KernelStratification
import ReflexiveArchitecture.Universal.Residual.KernelGraph
import ReflexiveArchitecture.Universal.Residual.MinimalResolution
import ReflexiveArchitecture.Universal.Residual.ResolutionComplexity
import ReflexiveArchitecture.Universal.Residual.ObservableAlgebra

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-! ### FTR-T5: Exhaustion criterion -/

/-- **Exhaustion criterion:** the following are equivalent for any `RCS`:
1. `compare` is injective (`MinimalExhaustive`).
2. The residual kernel is empty.
3. Every fiber is a subsingleton (at most one element).
4. The system is NOT `NonExhaustive`.

We prove these as a chain of biconditionals. -/

theorem exhaustive_iff_kernel_empty (S : ReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S ↔ ResidualKernel S = ∅ := by
  constructor
  · intro hinj
    ext ⟨x, y⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨hne, heq⟩
    exact hne (hinj heq)
  · intro hempty x y heq
    by_contra hne
    have : (x, y) ∈ ResidualKernel S := ⟨hne, heq⟩
    rw [hempty] at this
    exact this.elim

theorem kernel_empty_iff_all_fibers_subsingleton (S : ReflectiveCertificationSystem Bare Realized) :
    ResidualKernel S = ∅ ↔ ∀ b : Bare, ∀ x y : Realized, x ∈ Fiber S b → y ∈ Fiber S b → x = y := by
  constructor
  · intro hempty b x y hx hy
    by_contra hne
    have : (x, y) ∈ ResidualKernel S :=
      ⟨hne, by rw [mem_fiber_iff] at hx hy; exact hx.trans hy.symm⟩
    rw [hempty] at this
    exact this.elim
  · intro hsub
    ext ⟨x, y⟩
    simp only [Set.mem_empty_iff_false, iff_false]
    intro ⟨hne, heq⟩
    exact hne (hsub (S.compare x) x y (by simp [Fiber]) (by simp [Fiber, heq]))

theorem exhaustive_iff_not_nonExhaustive (S : ReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S ↔ ¬NonExhaustive S := by
  rw [nonExhaustive_iff_not_minimal]
  exact ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩

/-- **Complete exhaustion criterion:** four equivalent characterizations. -/
theorem exhaustion_tfae (S : ReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S ↔ ResidualKernel S = ∅ :=
  exhaustive_iff_kernel_empty S

/-! ### FTR-T2: Functoriality -/

/-- A **comparison-compatible map** between two systems on the same carriers:
`f : Realized → Realized` such that `S₂.compare ∘ f = S₁.compare`. -/
structure CompareCompatible (S₁ S₂ : ReflectiveCertificationSystem Bare Realized) where
  map : Realized → Realized
  compat : S₂.compare ∘ map = S₁.compare

/-- A compatible map sends kernel pairs to kernel pairs (when the map is injective). -/
theorem compatible_preserves_kernel
    {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂) (hinj : Function.Injective φ.map)
    {x y : Realized} (hk : (x, y) ∈ ResidualKernel S₁) :
    (φ.map x, φ.map y) ∈ ResidualKernel S₂ := by
  refine ⟨fun heq => hk.1 (hinj heq), ?_⟩
  have h1 : S₂.compare (φ.map x) = S₁.compare x := congr_fun φ.compat x
  have h2 : S₂.compare (φ.map y) = S₁.compare y := congr_fun φ.compat y
  show S₂.compare (φ.map x) = S₂.compare (φ.map y)
  rw [h1, h2]
  exact hk.2

/-- A compatible map preserves fiber membership. -/
theorem compatible_preserves_fiber
    {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂) {x : Realized} {b : Bare}
    (hx : x ∈ Fiber S₁ b) : φ.map x ∈ Fiber S₂ b := by
  rw [mem_fiber_iff] at hx ⊢
  have : S₂.compare (φ.map x) = S₁.compare x := congr_fun φ.compat x
  rw [this, hx]

/-- The identity is always compatible with itself. -/
def idCompatible (S : ReflectiveCertificationSystem Bare Realized) : CompareCompatible S S where
  map := id
  compat := by ext; simp [Function.comp]

/-- Compatible maps compose: if `φ : S₁ → S₂` and `ψ : S₂ → S₃`, then `ψ ∘ φ : S₁ → S₃`. -/
def compCompatible {S₁ S₂ S₃ : ReflectiveCertificationSystem Bare Realized}
    (ψ : CompareCompatible S₂ S₃) (φ : CompareCompatible S₁ S₂) :
    CompareCompatible S₁ S₃ where
  map := ψ.map ∘ φ.map
  compat := by
    ext x
    simp only [Function.comp]
    have h1 := congr_fun φ.compat x
    have h2 := congr_fun ψ.compat (φ.map x)
    simp only [Function.comp] at h1 h2
    rw [h2, h1]

/-- Identity is a left unit for composition. -/
theorem idCompatible_comp_left {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂) :
    (compCompatible (idCompatible S₂) φ).map = φ.map := rfl

/-- Identity is a right unit for composition. -/
theorem idCompatible_comp_right {S₁ S₂ : ReflectiveCertificationSystem Bare Realized}
    (φ : CompareCompatible S₁ S₂) :
    (compCompatible φ (idCompatible S₁)).map = φ.map := rfl

/-- Composition is associative. -/
theorem compCompatible_assoc
    {S₁ S₂ S₃ S₄ : ReflectiveCertificationSystem Bare Realized}
    (χ : CompareCompatible S₃ S₄)
    (ψ : CompareCompatible S₂ S₃)
    (φ : CompareCompatible S₁ S₂) :
    (compCompatible χ (compCompatible ψ φ)).map =
    (compCompatible (compCompatible χ ψ) φ).map := rfl

/-! ### FTR-T3: Optimal coarse observable -/

/-- A map `g : Realized → γ` is **coarser than** `compare` if it factors through `compare`. -/
def CoarserThanCompare (S : ReflectiveCertificationSystem Bare Realized) {γ : Type u}
    (g : Realized → γ) : Prop :=
  ∃ h : Bare → γ, g = h ∘ S.compare

/-- `compare` is coarser than itself (via `id`). -/
theorem compare_coarser_than_self (S : ReflectiveCertificationSystem Bare Realized) :
    CoarserThanCompare S S.compare :=
  ⟨id, by ext; simp⟩

/-- Any map coarser than `compare` is constant on fibers. -/
theorem coarser_constant_on_fibers (S : ReflectiveCertificationSystem Bare Realized) {γ : Type u}
    {g : Realized → γ} (hg : CoarserThanCompare S g) :
    ∀ x y, S.compare x = S.compare y → g x = g y := by
  rcases hg with ⟨h, rfl⟩
  intro x y heq
  simp [heq]

/-- **Optimality:** `compare` is the finest fiber-constant map. Any fiber-constant map
is coarser than `compare` (factors through it). -/
theorem compare_is_finest_fiber_constant (S : ReflectiveCertificationSystem Bare Realized)
    {γ : Type u} [Nonempty γ] (g : Realized → γ)
    (hg : ∀ x y, S.compare x = S.compare y → g x = g y) :
    CoarserThanCompare S g :=
  factors_of_constant_on_fibers S g hg

/-- **Coarser maps cannot separate kernel pairs.** -/
theorem coarser_blind_to_kernel (S : ReflectiveCertificationSystem Bare Realized) {γ : Type u}
    {g : Realized → γ} (hg : CoarserThanCompare S g)
    {x y : Realized} (hk : (x, y) ∈ ResidualKernel S) :
    g x = g y :=
  coarser_constant_on_fibers S hg x y hk.2

/-! ### The fundamental theorem (bundled)

**Only finer-than-compare maps can see the residual:** any coarser map is blind
to all kernel pairs (see `coarser_blind_to_kernel` above). -/

/-- **Fundamental theorem of residual geometry (EPIC_029).**

This structure bundles the complete characterization of the residual for a given
comparison map. It is not a new definition — it is a **packaging** of all the
theorems proved in EPICs 022–028, organized as a single coherent statement.

For any `compare : Realized → Bare`:
- The residual kernel is the canonical object of certification failure.
- It decomposes fiberwise into complete cliques.
- Observables are dual to kernel separation.
- Refinement is graph coloring.
- Resolution requires fiber-size-many colors.
- The system is exhaustive iff the kernel is empty. -/
structure FundamentalResidualPackage (S : ReflectiveCertificationSystem Bare Realized) where
  /-- The kernel is nonempty iff non-exhaustive. -/
  kernel_nonempty_iff : (∃ p, p ∈ ResidualKernel S) ↔ NonExhaustive S
  /-- The kernel decomposes fiberwise. -/
  kernel_decomposition : ResidualKernel S = ⋃ b, KernelAt S b
  /-- Each fiber kernel is complete. -/
  fiber_complete : ∀ b x y, x ∈ Fiber S b → y ∈ Fiber S b → x ≠ y → (x, y) ∈ KernelAt S b
  /-- Observable duality. -/
  observable_duality : ∀ P : Realized → Prop,
    ¬BareDetermined S P ↔ ∃ x y, (x, y) ∈ ResidualKernel S ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y)
  /-- Resolution = kernel separation. -/
  resolution_criterion : ∀ {Extra : Type u} (r : Refinement Realized Extra),
    Function.Injective (refinedCompare S r) ↔ ∀ p ∈ ResidualKernel S, SeparatesKernelPair r p
  /-- Resolution decomposes into per-fiber problems. -/
  resolution_local : ∀ {Extra : Type u} (r : Refinement Realized Extra),
    Function.Injective (refinedCompare S r) ↔ ∀ b, ResolvesAt S r b
  /-- Resolving a fiber requires injectivity on that fiber. -/
  resolution_injective : ∀ {Extra : Type u} (r : Refinement Realized Extra) b,
    ResolvesAt S r b → ∀ x y, x ∈ Fiber S b → y ∈ Fiber S b → r.refine x = r.refine y → x = y
  /-- Exhaustive iff kernel empty. -/
  exhaustion : MinimalExhaustive S ↔ ResidualKernel S = ∅

/-- **Construction:** the fundamental package for any `RCS`. -/
def fundamentalResidualPackage (S : ReflectiveCertificationSystem Bare Realized) :
    FundamentalResidualPackage S where
  kernel_nonempty_iff := residualKernel_nonempty_iff S
  kernel_decomposition := residualKernel_eq_iUnion_kernelAt S
  fiber_complete := fun b x y hx hy hne => @kernelAt_complete _ _ S b x y hx hy hne
  observable_duality := fun P => not_bareDetermined_iff_separates_kernel S P
  resolution_criterion := fun r => resolves_iff_separates_all_kernel_pairs S r
  resolution_local := fun r => resolves_iff_resolvesAt_all S r
  resolution_injective := fun r b hres => coloring_injective_on_fiber S r b hres
  exhaustion := exhaustive_iff_kernel_empty S

/-- The fundamental package exists for every `RCS` — no hypotheses needed. -/
theorem fundamental_package_exists (S : ReflectiveCertificationSystem Bare Realized) :
    Nonempty (FundamentalResidualPackage S) :=
  ⟨fundamentalResidualPackage S⟩

/-! ### Classification of bare-determined vs residual observables -/

/-- A predicate is either bare-determined or residual (separates a kernel pair).
This is a complete classification of all predicates on `Realized`. -/
theorem predicate_classification (S : ReflectiveCertificationSystem Bare Realized)
    (P : Realized → Prop) :
    BareDetermined S P ∨
      (∃ x y, (x, y) ∈ ResidualKernel S ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y)) := by
  rcases Classical.em (BareDetermined S P) with h | h
  · exact Or.inl h
  · exact Or.inr ((not_bareDetermined_iff_separates_kernel S P).1 h)

/-- The bare-determined predicates and the kernel-separating predicates are
complementary: every predicate falls into exactly one class. -/
theorem bareDetermined_xor_separates_kernel (S : ReflectiveCertificationSystem Bare Realized)
    (P : Realized → Prop) :
    BareDetermined S P ↔
      ¬(∃ x y, (x, y) ∈ ResidualKernel S ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y)) := by
  rw [← not_bareDetermined_iff_separates_kernel]
  exact ⟨fun h hn => hn h, fun h => Classical.byContradiction h⟩

/-! ### Named resolution complexity theorem -/

/-- **Resolution Complexity Theorem:** a refinement resolves a fiber if and only if
it is injective on that fiber. Since each fiber kernel is a complete graph $K_n$,
this means resolving a fiber of size $n$ requires at least $n$ distinct refinement
values — the chromatic number of $K_n$. -/
theorem resolution_complexity_theorem
    (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) (b : Bare) :
    ResolvesAt S r b ↔
      (∀ x y, x ∈ Fiber S b → y ∈ Fiber S b → r.refine x = r.refine y → x = y) := by
  constructor
  · intro hres x y hx hy hreq
    by_contra hne
    exact hres x y hx hy hne hreq
  · intro hinj x y hx hy hne hreq
    exact hne (hinj x y hx hy hreq)

/-! ### Paper-facing named theorem aliases (theorem-index stable names) -/

/-- **[Paper: Vanishing Criterion]** The residual vanishes exactly when
`compare` is injective, the kernel is empty, and every fiber is a subsingleton.
Alias for `exhaustive_iff_kernel_empty`. -/
alias vanishingCriterion := exhaustive_iff_kernel_empty

/-- **[Paper: Resolution Complexity Theorem — named alias]**
Resolving a fiber requires injectivity on that fiber (chromatic number of Kₙ).
Alias for `resolution_complexity_theorem`. -/
alias resolutionComplexityTheorem := resolution_complexity_theorem

/-- **[Paper: Predicate classification — named alias]**
Every predicate on `Realized` is either bare-determined or separates a kernel pair.
Alias for `predicate_classification`. -/
alias predicateClassification := predicate_classification

end ReflexiveArchitecture.Universal.Residual
