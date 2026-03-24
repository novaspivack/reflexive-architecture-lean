/-
  **Optimal certification and residual measurement.**

  ## Key results

  1. **Optimal refinement existence:** for any RCS, there exists a refinement
     that resolves it (the identity refinement). So the residual can always be
     eliminated — at a cost.

  2. **Minimal resolution per fiber:** resolving a fiber requires the refinement
     to be injective on that fiber. Any injection suffices. So the minimum
     refinement "size" for a single fiber of size `n` is `n`.

  3. **Residual measurement:** the nontrivial locus tells you where the residual
     lives; the fiber structure tells you how much.

  4. **Zero residual characterization:** the residual is zero (kernel empty) iff
     `compare` is injective iff every fiber is a singleton iff the trivial
     refinement resolves.

  5. **Adequate systems have irreducible residual:** for adequate systems, the
     canonical fiber has size ≥ 2, so no refinement to a subsingleton type can
     resolve. The minimum resolution cost is at least 2.

  6. **Refinement gap:** the "distance" from a given refinement to full resolution
     is measured by the unresolved kernel. The gap is zero iff the refinement
     resolves.
-/

import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem
import ReflexiveArchitecture.Universal.Residual.FiberSpectrum
import ReflexiveArchitecture.Universal.Residual.ResolutionComplexity
import ReflexiveArchitecture.Universal.Residual.QuantitativeResidual
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Optimal refinement existence -/

/-- **Optimal refinement exists:** the identity refinement resolves every system.
So the residual can always be eliminated — the question is at what cost. -/
theorem optimal_refinement_exists :
    ∃ (r : Refinement Realized Realized), Function.Injective (refinedCompare S r) :=
  ⟨identityRefinement, identity_always_resolves S⟩

/-- **Trivial is optimal iff exhaustive:** the cheapest possible refinement (no extra
data) resolves iff and only iff there is no residual to begin with. -/
theorem trivial_optimal_iff_exhaustive :
    Function.Injective (refinedCompare S (trivialRefinement (Realized := Realized))) ↔
      MinimalExhaustive S :=
  trivial_resolves_iff_exhaustive S

/-! ### Zero residual characterization -/

/-- **Zero residual theorem:** the following are equivalent:
1. The kernel is empty.
2. `compare` is injective.
3. Every fiber is trivial.
4. The nontrivial locus is empty.
5. The trivial refinement resolves.

When any of these hold, the residual is completely absent. -/
theorem zero_residual_iff_injective :
    ResidualKernel S = ∅ ↔ MinimalExhaustive S :=
  (exhaustive_iff_kernel_empty S).symm

theorem zero_residual_iff_all_trivial :
    ResidualKernel S = ∅ ↔ ∀ b, FiberTrivial S b := by
  rw [zero_residual_iff_injective, exhaustive_iff_all_fibers_trivial]

theorem zero_residual_iff_locus_empty :
    ResidualKernel S = ∅ ↔ NontrivialLocus S = ∅ := by
  rw [zero_residual_iff_injective, ← nontrivialLocus_empty_iff]

theorem zero_residual_iff_trivial_resolves :
    ResidualKernel S = ∅ ↔
      Function.Injective (refinedCompare S (trivialRefinement (Realized := Realized))) := by
  rw [zero_residual_iff_injective, ← trivial_optimal_iff_exhaustive]

/-! ### Refinement gap -/

/-- The **refinement gap** of a refinement: its unresolved kernel. This measures
how far the refinement is from full resolution. -/
abbrev refinementGap {Extra : Type u} (r : Refinement Realized Extra) :
    Set (Realized × Realized) :=
  UnresolvedKernel S r

/-- The gap is empty iff the refinement resolves. -/
theorem gap_empty_iff_resolves {Extra : Type u} (r : Refinement Realized Extra) :
    refinementGap S r = ∅ ↔ Function.Injective (refinedCompare S r) :=
  (resolves_iff_unresolvedKernel_empty S r).symm

/-- The gap of the trivial refinement is the full kernel. -/
theorem gap_trivial_eq_kernel :
    refinementGap S (trivialRefinement (Realized := Realized)) = ResidualKernel S :=
  unresolvedKernel_trivial S

/-- The gap of the identity refinement is empty. -/
theorem gap_identity_empty :
    refinementGap S (identityRefinement (Realized := Realized)) = ∅ :=
  unresolvedKernel_identity_empty S

/-- Finer refinements have smaller gaps (monotonicity). -/
theorem gap_antitone {E₁ E₂ : Type u}
    (r₁ : Refinement Realized E₁) (r₂ : Refinement Realized E₂)
    (hfine : RefinesTo r₁ r₂) :
    refinementGap S r₂ ⊆ refinementGap S r₁ :=
  unresolvedKernel_antitone S r₁ r₂ hfine

/-! ### Adequate irreducible residual -/

/-- **Adequate irreducible residual:** for adequate systems, the residual cannot
be eliminated by trivial refinement. The minimum resolution cost is at least 2. -/
theorem adequate_irreducible_residual (A : AdequateReflectiveSystem Bare Realized) :
    refinementGap A.toRCS (trivialRefinement (Realized := Realized)) ≠ ∅ := by
  rw [gap_trivial_eq_kernel]
  intro hempty
  have := (residualKernel_nonempty_iff A.toRCS).2 (adequate_nonExhaustive A)
  rcases this with ⟨p, hp⟩
  rw [hempty] at hp
  exact hp.elim

/-- The adequate gap contains the canonical witness pair. -/
theorem adequate_gap_contains_witnesses (A : AdequateReflectiveSystem Bare Realized) :
    (A.witness₁, A.witness₂) ∈
      refinementGap A.toRCS (trivialRefinement (Realized := Realized)) := by
  rw [gap_trivial_eq_kernel]
  exact adequate_witnesses_in_kernel A

/-! ### Can the residual be fully exhausted? -/

/-- **Yes:** for any system, the identity refinement fully exhausts the residual. -/
theorem residual_can_be_exhausted :
    refinementGap S (identityRefinement (Realized := Realized)) = ∅ :=
  gap_identity_empty S

/-- **But not cheaply:** for adequate systems, subsingleton refinements cannot
exhaust the residual. -/
theorem adequate_residual_not_cheaply_exhausted
    (A : AdequateReflectiveSystem Bare Realized) {Extra : Type u} [Subsingleton Extra]
    (r : Refinement Realized Extra) :
    refinementGap A.toRCS r ≠ ∅ := by
  intro hempty
  have hres := (gap_empty_iff_resolves A.toRCS r).1 hempty
  exact adequate_requires_nonsubsingleton_extra A r hres

/-! ### What remains at optimal? -/

/-- **At optimal certification (injective compare): nothing remains.** -/
theorem nothing_remains_at_optimal (hinj : MinimalExhaustive S) :
    ResidualKernel S = ∅ ∧
    NontrivialLocus S = ∅ ∧
    (∀ P : Realized → Prop, BareDetermined S P) ∧
    Function.Injective (refinedCompare S (trivialRefinement (Realized := Realized))) := by
  refine ⟨(exhaustive_iff_kernel_empty S).1 hinj,
    (nontrivialLocus_empty_iff S).2 hinj, ?_,
    (trivial_resolves_iff_exhaustive S).2 hinj⟩
  intro P
  by_contra hP
  have ⟨x, y, hk, _⟩ := (not_bareDetermined_iff_separates_kernel S P).1 hP
  have := hk.1
  exact this (hinj hk.2)

/-! ### The fundamental distinction: certification vs refinement -/

/-- **Certification cannot resolve its own residual.** For adequate systems,
the comparison map `compare` is not injective — the residual is intrinsic to
the certification and cannot be eliminated by the certification itself.
Refinement (adding extra data beyond `compare`) can resolve the residual,
but the refinement is *supplementary structure*, not the certification doing
better. -/
theorem adequate_certification_cannot_self_resolve
    (A : AdequateReflectiveSystem Bare Realized) :
    ¬Function.Injective A.compare :=
  adequate_not_injective A

/-- **Refinement resolves, but at a cost.** The identity refinement always
resolves, but it requires remembering all of `Realized` — defeating the
purpose of certification (which is to compress realization into something
smaller). For adequate systems, no subsingleton refinement suffices. -/
theorem resolution_requires_extra_data
    (A : AdequateReflectiveSystem Bare Realized) :
    ¬Function.Injective A.compare ∧
    Function.Injective (refinedCompare A.toRCS (identityRefinement (Realized := Realized))) :=
  ⟨adequate_not_injective A, identity_always_resolves A.toRCS⟩

/-- **The residual is intrinsic to the certification level.** Two systems with
the same `compare` have the same residual — the residual is a property of the
certification, not of the refinement. Refinement can *supplement* the
certification, but the residual *of the certification* is fixed. -/
theorem residual_intrinsic_to_certification
    (S₁ S₂ : ReflectiveCertificationSystem Bare Realized)
    (hcmp : S₁.compare = S₂.compare) :
    ResidualKernel S₁ = ResidualKernel S₂ :=
  residualKernel_eq_of_compare_eq S₁ S₂ hcmp

/-- **The price of resolution is always positive for adequate systems.**
No refinement to a subsingleton type can resolve an adequate system.
The minimum number of refinement values needed is at least 2. -/
theorem adequate_resolution_price_positive
    (A : AdequateReflectiveSystem Bare Realized) :
    ∀ {Extra : Type u} [Subsingleton Extra] (r : Refinement Realized Extra),
      ¬Function.Injective (refinedCompare A.toRCS r) :=
  fun r => adequate_requires_nonsubsingleton_extra A r

/-- **Summary: the certification-refinement gap theorem.**

For any adequate system:
1. The certification itself (`compare`) is not injective — the residual exists.
2. The residual can be resolved by adding extra data (refinement).
3. But the cheapest resolution requires at least 2 distinct refinement values.
4. The residual is intrinsic to `compare` — it cannot be changed by changing
   other system data, only by supplementing `compare` with a refinement.

This is the precise sense in which "certification does not exhaust realization":
the certification *as given* has an irreducible residual, and eliminating it
requires going beyond the certification. -/
theorem certification_refinement_gap
    (A : AdequateReflectiveSystem Bare Realized) :
    ¬Function.Injective A.compare ∧
    (∃ r : Refinement Realized Realized, Function.Injective (refinedCompare A.toRCS r)) ∧
    (∀ {Extra : Type u} [Subsingleton Extra] (r : Refinement Realized Extra),
      ¬Function.Injective (refinedCompare A.toRCS r)) :=
  ⟨adequate_not_injective A,
   ⟨identityRefinement, identity_always_resolves A.toRCS⟩,
   fun r => adequate_requires_nonsubsingleton_extra A r⟩

end ReflexiveArchitecture.Universal.Residual
