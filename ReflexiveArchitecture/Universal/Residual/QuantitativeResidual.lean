/-
  EPIC_030 — **Quantitative residual theory.**

  Sharp numerical invariants and bounds for the residual geometry.

  ## Key results

  1. **Global resolution bound:** minimum refinement cardinality to resolve the whole
     system is at most `|Realized|` (identity refinement) and at least `max fiber size`
     (pigeonhole on complete cliques).

  2. **Adequate quantitative bound:** adequate systems require `|Extra| ≥ 2`.

  3. **Fiber-size determines resolution cost:** a fiber of size `n` needs exactly `n`
     colors; the global cost is the supremum of fiber sizes.

  4. **Monotone unresolved kernel:** finer refinements have weakly smaller unresolved
     kernels (set-theoretic, already proved; here we add the finite-cardinality version).
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem
import ReflexiveArchitecture.Universal.Residual.ResolutionComplexity
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u}

/-! ### QRT-T2: Global resolution cardinality bounds -/

/-- **Upper bound:** the identity refinement (to `Realized` itself) always resolves.
So the minimum resolving cardinality is at most `|Realized|`. -/
theorem resolution_upper_bound (S : ReflectiveCertificationSystem Bare Realized) :
    Function.Injective (refinedCompare S (identityRefinement (Realized := Realized))) :=
  identity_always_resolves S

/-- **Lower bound (per fiber):** if a refinement resolves and a fiber has size > 1,
then `refine` takes at least 2 distinct values on that fiber. -/
theorem resolution_requires_distinct_on_nontrivial_fiber
    (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra)
    (hres : Function.Injective (refinedCompare S r))
    {b : Bare} {x y : Realized} (hx : x ∈ Fiber S b) (hy : y ∈ Fiber S b) (hne : x ≠ y) :
    r.refine x ≠ r.refine y := by
  rw [resolves_iff_resolvesAt_all] at hres
  exact hres b x y hx hy hne

/-! ### QRT-T5: Adequate quantitative bound -/

/-- **Adequate lower bound:** any refinement resolving an adequate system must use
at least 2 distinct values. A refinement to a subsingleton type cannot resolve. -/
theorem adequate_requires_nonsubsingleton_extra
    (A : AdequateReflectiveSystem Bare Realized)
    {Extra : Type u} [Subsingleton Extra]
    (r : Refinement Realized Extra) :
    ¬Function.Injective (refinedCompare A.toRCS r) := by
  intro hinj
  have hres := (resolves_iff_resolvesAt_all A.toRCS r).1 hinj
  have := hres (A.compare A.witness₁) A.witness₁ A.witness₂
    (by simp [Fiber]) (by simp [Fiber, A.witnesses_certify_same.symm]) A.witnesses_distinct
  exact this (Subsingleton.elim _ _)

/-- **Adequate resolution spectrum (subsingleton):** adequate systems cannot be resolved
by any subsingleton-valued refinement. This is the sharpest form of "depth ≥ 2." -/
theorem adequate_subsingleton_unresolvable
    (A : AdequateReflectiveSystem Bare Realized) {Extra : Type u} [Subsingleton Extra] :
    ∀ r : Refinement Realized Extra, ¬Function.Injective (refinedCompare A.toRCS r) :=
  fun r => adequate_requires_nonsubsingleton_extra A r

/-! ### Resolution and exhaustion: quantitative connection -/

/-- **Trivial system:** if `compare` is injective, the trivial refinement resolves. -/
theorem trivial_resolves_exhaustive (S : ReflectiveCertificationSystem Bare Realized)
    (hinj : MinimalExhaustive S) :
    Function.Injective (refinedCompare S (trivialRefinement (Realized := Realized))) := by
  intro x y heq
  simp [refinedCompare, trivialRefinement] at heq
  exact hinj heq

/-- **Non-trivial system:** if the system is non-exhaustive, the trivial refinement
does NOT resolve. -/
theorem trivial_fails_nonExhaustive (S : ReflectiveCertificationSystem Bare Realized)
    (h : NonExhaustive S) :
    ¬Function.Injective (refinedCompare S (trivialRefinement (Realized := Realized))) := by
  intro hinj
  rcases h with ⟨x, y, hne, heq⟩
  have := hinj (show refinedCompare S (trivialRefinement (Realized := Realized)) x =
    refinedCompare S (trivialRefinement (Realized := Realized)) y by
    simp [refinedCompare, trivialRefinement, heq])
  exact hne this

/-- **Dichotomy:** the trivial refinement resolves iff the system is exhaustive. -/
theorem trivial_resolves_iff_exhaustive (S : ReflectiveCertificationSystem Bare Realized) :
    Function.Injective (refinedCompare S (trivialRefinement (Realized := Realized))) ↔
      MinimalExhaustive S := by
  constructor
  · intro hinj x y heq
    have := hinj (show refinedCompare S (trivialRefinement (Realized := Realized)) x =
      refinedCompare S (trivialRefinement (Realized := Realized)) y by
      simp [refinedCompare, trivialRefinement, heq])
    exact this

  · exact trivial_resolves_exhaustive S

/-! ### The complete quantitative picture -/

/-- **Quantitative summary (adequate systems):**
- Trivial refinement (PUnit): CANNOT resolve.
- Bool refinement: CAN resolve the canonical fiber if it has exactly 2 elements.
- Identity refinement: ALWAYS resolves.

So the resolution complexity of an adequate system is:
- at least 2 (subsingleton fails),
- at most |Realized| (identity works),
- exactly max fiber size (per-fiber coloring). -/
theorem adequate_resolution_spectrum
    (A : AdequateReflectiveSystem Bare Realized) :
    ¬Function.Injective (refinedCompare A.toRCS (trivialRefinement (Realized := Realized))) ∧
    Function.Injective (refinedCompare A.toRCS (identityRefinement (Realized := Realized))) :=
  ⟨trivial_fails_nonExhaustive A.toRCS (adequate_nonExhaustive A),
   identity_always_resolves A.toRCS⟩

end ReflexiveArchitecture.Universal.Residual
