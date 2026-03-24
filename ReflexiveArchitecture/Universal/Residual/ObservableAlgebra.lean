/-
  EPIC_023 — **Observable algebra** and the Boolean structure of bare-determined predicates.

  The set of bare-determined predicates (those factoring through `compare`) is closed
  under all propositional connectives. Its complement — the **residual observables** —
  is therefore "large": any predicate that varies on a fiber escapes the algebra.

  We also prove that `compare` itself is the **universal** bare-determined map: every
  bare-determined function factors through it, and it is the coarsest such factorization.
-/

import ReflexiveArchitecture.Universal.Residual.ResidualStructure

universe u

namespace ReflexiveArchitecture.Universal.Residual

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized)

/-! ### Boolean closure of bare-determined predicates -/

theorem bareDetermined_true : BareDetermined S (fun _ => True) :=
  ⟨fun _ => True, fun _ => Iff.rfl⟩

theorem bareDetermined_false : BareDetermined S (fun _ => False) :=
  ⟨fun _ => False, fun _ => Iff.rfl⟩

theorem bareDetermined_and {P Q : Realized → Prop}
    (hP : BareDetermined S P) (hQ : BareDetermined S Q) :
    BareDetermined S (fun x => P x ∧ Q x) := by
  rcases hP with ⟨QP, hQP⟩
  rcases hQ with ⟨QQ, hQQ⟩
  refine ⟨fun b => QP b ∧ QQ b, fun x => ?_⟩
  simp only
  exact ⟨fun ⟨hp, hq⟩ => ⟨(hQP x).1 hp, (hQQ x).1 hq⟩,
         fun ⟨hp, hq⟩ => ⟨(hQP x).2 hp, (hQQ x).2 hq⟩⟩

theorem bareDetermined_or {P Q : Realized → Prop}
    (hP : BareDetermined S P) (hQ : BareDetermined S Q) :
    BareDetermined S (fun x => P x ∨ Q x) := by
  rcases hP with ⟨QP, hQP⟩
  rcases hQ with ⟨QQ, hQQ⟩
  refine ⟨fun b => QP b ∨ QQ b, fun x => ?_⟩
  simp only
  exact ⟨fun h => h.elim (fun hp => Or.inl ((hQP x).1 hp)) (fun hq => Or.inr ((hQQ x).1 hq)),
         fun h => h.elim (fun hp => Or.inl ((hQP x).2 hp)) (fun hq => Or.inr ((hQQ x).2 hq))⟩

theorem bareDetermined_not {P : Realized → Prop}
    (hP : BareDetermined S P) :
    BareDetermined S (fun x => ¬P x) := by
  rcases hP with ⟨Q, hQ⟩
  refine ⟨fun b => ¬Q b, fun x => ?_⟩
  simp only
  exact ⟨fun h hq => h ((hQ x).2 hq), fun h hp => h ((hQ x).1 hp)⟩

theorem bareDetermined_imp {P Q : Realized → Prop}
    (hP : BareDetermined S P) (hQ : BareDetermined S Q) :
    BareDetermined S (fun x => P x → Q x) := by
  rcases hP with ⟨QP, hQP⟩
  rcases hQ with ⟨QQ, hQQ⟩
  refine ⟨fun b => QP b → QQ b, fun x => ?_⟩
  simp only
  exact ⟨fun h hp => (hQQ x).1 (h ((hQP x).2 hp)),
         fun h hp => (hQQ x).2 (h ((hQP x).1 hp))⟩

/-- Any predicate that is literally `Q ∘ compare` is bare-determined. -/
theorem bareDetermined_of_comp (Q : Bare → Prop) :
    BareDetermined S (Q ∘ S.compare) :=
  ⟨Q, fun _ => Iff.rfl⟩

/-! ### Universal factorization: `compare` is the universal bare-determined map -/

/-- **Universal factorization:** any function `f : Realized → α` that is constant on
every fiber of `compare` factors through `compare` (classically). -/
theorem factors_of_constant_on_fibers {α : Type u} [Nonempty α] (f : Realized → α)
    (hf : ∀ x y : Realized, S.compare x = S.compare y → f x = f y) :
    ∃ g : Bare → α, f = g ∘ S.compare := by
  classical
  refine ⟨fun b => if h : ∃ x, S.compare x = b then f h.choose else Classical.arbitrary α, ?_⟩
  ext x
  simp only [Function.comp]
  have hex : ∃ x', S.compare x' = S.compare x := ⟨x, rfl⟩
  rw [dif_pos hex]
  exact (hf _ _ hex.choose_spec).symm

/-- Converse: if `f` factors through `compare`, it is constant on fibers. -/
theorem constant_on_fibers_of_factors {α : Type u} (f : Realized → α) (g : Bare → α)
    (hfg : f = g ∘ S.compare) : ∀ x y : Realized, S.compare x = S.compare y → f x = f y := by
  intro x y heq
  rw [hfg]
  simp [heq]

/-- **Characterization:** a function is constant on fibers iff it factors through `compare`. -/
theorem constant_on_fibers_iff_factors {α : Type u} [Nonempty α] (f : Realized → α) :
    (∀ x y : Realized, S.compare x = S.compare y → f x = f y) ↔
    ∃ g : Bare → α, f = g ∘ S.compare :=
  ⟨factors_of_constant_on_fibers S f, fun ⟨g, hg⟩ => constant_on_fibers_of_factors S f g hg⟩

end ReflexiveArchitecture.Universal.Residual
