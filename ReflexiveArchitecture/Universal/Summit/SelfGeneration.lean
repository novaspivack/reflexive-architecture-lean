/-
  EPIC_031 — **Reflective self-generation** and the fiber automorphism diagonal.

  ## The Gödelian move

  `AdequateReflectiveSystem` requires externally supplied witnesses. This module
  defines a **self-generating** class where witnesses are **derived** from the
  system's internal symmetry structure.

  A **compare-preserving endomorphism** `twist : Realized → Realized` satisfying
  `compare ∘ twist = compare` permutes elements within fibers. If `twist ≠ id`,
  then some `x` has `twist x ≠ x` while `compare (twist x) = compare x` — and
  that pair witnesses non-exhaustion.

  This is the **fiber automorphism diagonal**: the system's own internal symmetry
  generates the witness diversity that forces non-exhaustion. The witnesses are not
  supplied from outside; they are **produced** by the system's structure.

  ## Why this is Gödel-flavored

  Gödel's incompleteness uses a system's expressive power to construct a sentence
  the system cannot decide. Here, a system's internal symmetry (the twist) constructs
  the witness pair the system cannot collapse. The mechanism is the same: self-reference
  (the system acting on itself) produces the very structure that prevents completeness
  (exhaustion).

  ## Non-circularity

  The class axioms mention:
  - a compare-preserving endomorphism (`twist`)
  - the endomorphism is not the identity (`twist ≠ id`)

  They do NOT mention: `NonExhaustive`, `¬ Injective compare`, fibers, or kernel pairs.
  The non-exhaustion is a **theorem**, not an assumption.
-/

import Mathlib.Logic.Function.Basic
import ReflexiveArchitecture.Universal.Summit.Adequacy

universe u

namespace ReflexiveArchitecture.Universal.Summit

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-! ### The self-generating class -/

/-- **Reflectively sufficient system (EPIC_031):** a reflective certification system
equipped with a **non-identity compare-preserving endomorphism** — a "fiber twist"
that permutes elements within fibers without being trivial.

This is the **self-generating** version of adequacy: the twist *produces* witness
diversity from the system's internal symmetry, rather than requiring externally
supplied witness data. -/
structure ReflectivelySufficientSystem (Bare Realized : Type u) extends
    ReflectiveCertificationSystem Bare Realized where
  twist : Realized → Realized
  twist_preserves : ∀ x, compare (twist x) = compare x
  twist_nontrivial : twist ≠ id

/-! ### The diagonal theorem: self-generation of witnesses -/

/-- **Witness extraction:** from a non-identity twist, extract a concrete point where
the twist moves. -/
theorem exists_moved_point (S : ReflectivelySufficientSystem Bare Realized) :
    ∃ x : Realized, S.twist x ≠ x := by
  by_contra h
  push_neg at h
  exact S.twist_nontrivial (funext h)

/-- **Self-generation theorem (RSG-T2):** every reflectively sufficient system is
adequate. The witnesses are **derived** from the twist, not supplied externally. -/
noncomputable def toAdequate (S : ReflectivelySufficientSystem Bare Realized) :
    AdequateReflectiveSystem Bare Realized :=
  have h := exists_moved_point S
  { compare := S.compare
    Canonical := S.Canonical
    Sound := S.Sound
    witness₁ := S.twist h.choose
    witness₂ := h.choose
    witnesses_distinct := h.choose_spec
    witnesses_certify_same := S.twist_preserves h.choose }

/-- **The diagonal theorem (RSG-T3):** every reflectively sufficient system is
non-exhaustive. The proof derives witnesses from the twist, then applies
`adequate_nonExhaustive`. -/
theorem reflectivelySufficient_nonExhaustive (S : ReflectivelySufficientSystem Bare Realized) :
    NonExhaustive S.toReflectiveCertificationSystem := by
  rcases exists_moved_point S with ⟨x, hx⟩
  exact ⟨S.twist x, x, hx, S.twist_preserves x⟩

/-- Thesis-level name. -/
theorem diagonal_universality :
    ∀ (S : ReflectivelySufficientSystem Bare Realized),
      NonExhaustive S.toReflectiveCertificationSystem :=
  reflectivelySufficient_nonExhaustive

/-! ### RSG-T4: Identity collapse excluded -/

/-- **Identity collapse impossible:** if `compare = id`, no non-identity endomorphism
can preserve `compare`. So reflectively sufficient systems exclude identity collapse. -/
theorem identity_not_reflectivelySufficient :
    ∀ (S : ReflectivelySufficientSystem Bare Bare),
      S.compare = id → False := by
  intro S hid
  rcases exists_moved_point S with ⟨x, hx⟩
  have h := S.twist_preserves x
  simp only [hid, id] at h
  exact hx h

/-- More generally: injective `compare` excludes reflective sufficiency. -/
theorem injective_not_reflectivelySufficient (S : ReflectivelySufficientSystem Bare Realized)
    (hinj : Function.Injective S.compare) : False := by
  rcases exists_moved_point S with ⟨x, hx⟩
  exact hx (hinj (S.twist_preserves x))

/-! ### RSG-T6: Monoid structure of compare-preserving endomorphisms -/

/-- Compare-preserving endomorphisms compose. -/
theorem twist_comp_preserves (S : ReflectivelySufficientSystem Bare Realized)
    (f g : Realized → Realized)
    (hf : ∀ x, S.compare (f x) = S.compare x)
    (hg : ∀ x, S.compare (g x) = S.compare x) :
    ∀ x, S.compare (f (g x)) = S.compare x := by
  intro x
  rw [hf, hg]

/-- The identity is always compare-preserving (but trivial). -/
theorem id_preserves (S : ReflectivelySufficientSystem Bare Realized) :
    ∀ x, S.compare (id x) = S.compare x :=
  fun _ => rfl

/-! ### Forgetful maps -/

/-- Forget to `AdequateReflectiveSystem`. -/
noncomputable abbrev ReflectivelySufficientSystem.toAdequateReflectiveSystem
    (S : ReflectivelySufficientSystem Bare Realized) : AdequateReflectiveSystem Bare Realized :=
  toAdequate S

/-- Forget to minimal `RCS`. -/
abbrev ReflectivelySufficientSystem.toRCS
    (S : ReflectivelySufficientSystem Bare Realized) :
    ReflectiveCertificationSystem Bare Realized :=
  S.toReflectiveCertificationSystem

/-! ### The full chain -/

/-- **The complete self-generation chain:**
`ReflectivelySufficientSystem` → `AdequateReflectiveSystem` → `NonExhaustive`

The first arrow derives witnesses from the twist (self-generation).
The second arrow derives non-exhaustion from the witnesses (inevitability).
The composition is the diagonal theorem. -/
theorem self_generation_chain (S : ReflectivelySufficientSystem Bare Realized) :
    NonExhaustive (toAdequate S).toRCS :=
  adequate_nonExhaustive (toAdequate S)

end ReflexiveArchitecture.Universal.Summit
