/-
  **Meta-level theorem and observable persistence under refinement.**

  The residual kernel requires access to both levels. The bare level is blind
  to the residual. Observables persist or vanish under refinement in a
  controlled way.
-/

import ReflexiveArchitecture.Universal.Residual.FundamentalTheorem
import ReflexiveArchitecture.Universal.Residual.ObservableAlgebra
import ReflexiveArchitecture.Universal.Residual.ResolutionComplexity
import ReflexiveArchitecture.Universal.Residual.QuantitativeResidual
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Summit

variable {Bare Realized : Type u}

/-! ### Bare-level blindness -/

/-- Any `Q : Bare → Prop` gives `Q(compare x) = Q(compare y)` for kernel pairs. -/
theorem bare_level_blind_to_kernel (S : ReflectiveCertificationSystem Bare Realized)
    (Q : Bare → Prop) {x y : Realized} (hk : (x, y) ∈ ResidualKernel S) :
    Q (S.compare x) = Q (S.compare y) := by
  rw [hk.2]

/-- `Q ∘ compare` agrees on all kernel pairs. -/
theorem bare_predicate_cannot_separate_kernel (S : ReflectiveCertificationSystem Bare Realized)
    (Q : Bare → Prop) {x y : Realized} (hk : (x, y) ∈ ResidualKernel S) :
    Q (S.compare x) ↔ Q (S.compare y) := by
  rw [hk.2]

/-! ### Meta-level theorem -/

/-- **Meta-level theorem:** detecting the residual requires non-bare-determined
predicates. All bare-level predicates agree on kernel pairs. -/
theorem residual_detection_requires_meta_level
    (S : ReflectiveCertificationSystem Bare Realized) (h : NonExhaustive S) :
    (∃ P : Realized → Prop, ¬BareDetermined S P) ∧
    (∀ (Q : Bare → Prop) (x y : Realized), (x, y) ∈ ResidualKernel S →
      Q (S.compare x) = Q (S.compare y)) :=
  ⟨exists_non_bareDetermined_of_nonExhaustive S h,
   fun Q x y hk => by rw [hk.2]⟩

/-- **Gödel compatibility:** the residual is visible from the meta-level but
invisible from the bare level. -/
theorem godel_compatibility (S : ReflectiveCertificationSystem Bare Realized)
    (h : NonExhaustive S) :
    (∃ P, ¬BareDetermined S P ∧
      ∃ x y, (x, y) ∈ ResidualKernel S ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y)) ∧
    (∀ P, BareDetermined S P →
      ∀ x y, (x, y) ∈ ResidualKernel S → (P x ↔ P y)) := by
  constructor
  · obtain ⟨x, y, hne, heq⟩ := h
    refine ⟨fun z => z = x, ?_, x, y, ⟨hne, heq⟩, Or.inl ⟨rfl, hne.symm⟩⟩
    intro ⟨Q, hQ⟩
    have h1 := (hQ x).1 rfl
    rw [heq] at h1
    exact hne.symm ((hQ y).2 h1)
  · intro P hP x y hk
    have hx : x ∈ Fiber S (S.compare x) := by simp [Fiber]
    have hy : y ∈ Fiber S (S.compare x) := by simp [Fiber, hk.2.symm]
    exact bareDetermined_constant_on_fiber S hP hx hy

/-! ### Observable persistence under refinement -/

/-- A predicate is **persistent** under a refinement if it remains non-bare-determined
even after the refinement is applied. That is, the predicate separates a kernel pair
that the refinement also fails to separate. -/
def PersistentObservable (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) (P : Realized → Prop) : Prop :=
  ∃ x y, (x, y) ∈ UnresolvedKernel S r ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y)

/-- A persistent observable is non-bare-determined. -/
theorem persistent_is_non_bareDetermined (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) (P : Realized → Prop)
    (hp : PersistentObservable S r P) : ¬BareDetermined S P := by
  obtain ⟨x, y, ⟨hk, _⟩, hsep⟩ := hp
  exact (not_bareDetermined_iff_separates_kernel S P).2 ⟨x, y, hk, hsep⟩

/-- If a refinement resolves, no observable is persistent (there are no unresolved
kernel pairs to separate). -/
theorem no_persistent_if_resolved (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra)
    (hres : Function.Injective (refinedCompare S r))
    (P : Realized → Prop) : ¬PersistentObservable S r P := by
  intro ⟨x, y, hmem, _⟩
  have := (resolves_iff_unresolvedKernel_empty S r).1 hres
  rw [this] at hmem
  exact hmem.elim

/-- If the unresolved kernel is nonempty, there exists a persistent observable. -/
theorem exists_persistent_of_unresolved (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra)
    (hunres : ∃ p, p ∈ UnresolvedKernel S r) :
    ∃ P, PersistentObservable S r P := by
  obtain ⟨⟨x, y⟩, ⟨⟨hne, heq⟩, hreq⟩⟩ := hunres
  exact ⟨fun z => z = x, x, y, ⟨⟨hne, heq⟩, hreq⟩, Or.inl ⟨rfl, hne.symm⟩⟩

/-- **Persistence dichotomy:** either the refinement resolves (no persistent
observables) or the unresolved kernel is nonempty (persistent observables exist). -/
theorem persistence_dichotomy (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) :
    Function.Injective (refinedCompare S r) ∨
    (∃ P, PersistentObservable S r P) := by
  rcases Classical.em (Function.Injective (refinedCompare S r)) with h | h
  · exact Or.inl h
  · right
    have hunres : ∃ p, p ∈ UnresolvedKernel S r := by
      by_contra hall
      push_neg at hall
      have : UnresolvedKernel S r = ∅ := by
        ext p; simp only [Set.mem_empty_iff_false, iff_false]; exact hall p
      exact h ((resolves_iff_unresolvedKernel_empty S r).2 this)
    exact exists_persistent_of_unresolved S r hunres

/-! ### Persistent observables — secondary theorem family -/

/-- A persistent observable is **strictly residual**: it witnesses a kernel pair
that survives the refinement. -/
theorem persistent_witnesses_unresolved_pair
    (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) (P : Realized → Prop)
    (hp : PersistentObservable S r P) :
    ∃ x y, (x, y) ∈ UnresolvedKernel S r := by
  obtain ⟨x, y, hmem, _⟩ := hp
  exact ⟨x, y, hmem⟩

/-- If a persistent observable exists, the system is non-exhaustive. -/
theorem persistent_implies_nonExhaustive
    (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) (P : Realized → Prop)
    (hp : PersistentObservable S r P) :
    NonExhaustive S := by
  obtain ⟨x, y, ⟨⟨hne, heq⟩, _⟩, _⟩ := hp
  exact ⟨x, y, hne, heq⟩

/-- **Persistence spectrum:** for any adequate system, every subsingleton-valued
refinement has persistent observables — the witness pair generates one. -/
theorem adequate_has_persistent_observables
    (A : AdequateReflectiveSystem Bare Realized)
    {Extra : Type u} [Subsingleton Extra]
    (r : Refinement Realized Extra) :
    ∃ P, PersistentObservable A.toRCS r P := by
  have hunres : ∃ p, p ∈ UnresolvedKernel A.toRCS r := by
    have hk := adequate_witnesses_in_kernel A
    by_contra hall
    push_neg at hall
    have hempty : UnresolvedKernel A.toRCS r = ∅ := by
      ext p; simp only [Set.mem_empty_iff_false, iff_false]; exact hall p
    have hres := (resolves_iff_unresolvedKernel_empty A.toRCS r).2 hempty
    exact adequate_requires_nonsubsingleton_extra A r hres
  exact exists_persistent_of_unresolved A.toRCS r hunres

/-- **Persistence measure:** the set of persistent observables for a refinement
is isomorphic (as a predicate) to the kernel-separating predicates on the
unresolved kernel. The unresolved kernel is the "persistence support". -/
theorem persistent_iff_separates_unresolved
    (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) (P : Realized → Prop) :
    PersistentObservable S r P ↔
      ∃ x y, (x, y) ∈ UnresolvedKernel S r ∧ (P x ∧ ¬P y ∨ ¬P x ∧ P y) :=
  Iff.rfl

/-- **Persistence dichotomy (sharper form):** either the refinement is terminal
(resolves fully, persistence support empty) or there exists a persistent
observable. This is a direct corollary of `persistence_dichotomy` phrased
in terms of the support. -/
theorem persistence_dichotomy_support
    (S : ReflectiveCertificationSystem Bare Realized)
    {Extra : Type u} (r : Refinement Realized Extra) :
    UnresolvedKernel S r = ∅ ∨ (∃ P, PersistentObservable S r P) := by
  rcases Classical.em (UnresolvedKernel S r = ∅) with h | h
  · exact Or.inl h
  · right
    have ⟨p, hp⟩ : ∃ p, p ∈ UnresolvedKernel S r := by
      by_contra hall
      apply h
      ext p; simp only [Set.mem_empty_iff_false, iff_false]
      exact fun hp => hall ⟨p, hp⟩
    exact exists_persistent_of_unresolved S r ⟨p, hp⟩

end ReflexiveArchitecture.Universal.Residual
