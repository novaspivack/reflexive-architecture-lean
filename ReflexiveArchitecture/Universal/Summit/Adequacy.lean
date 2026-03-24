/-
  EPIC_021 — **Adequacy axiom** and summit inevitability.

  ## The key idea

  At the level of a bare `compare : Realized → Bare`, **any** predicate forcing
  `NonExhaustive` must logically imply `¬ Injective compare`. So there is no
  "magic axiom" on the comparison map alone that avoids this.

  The creative move is to require **structural witness data** that *entails*
  non-injectivity without *being* non-injectivity:

  **`WitnessDiversity`:** the system carries two distinguished realized witnesses
  `w₁ w₂ : Realized` that are **distinct** (`w₁ ≠ w₂`) but **certify identically**
  (`compare w₁ = compare w₂`). The witnesses are **fields** of the class, not
  existentially quantified — they are structural data the system *provides*, not a
  property we *check*.

  This is **not** the same as `NonExhaustive`:
  - `NonExhaustive` is a `Prop` (existential, proof-irrelevant).
  - `WitnessDiversity` is **data** (two named witnesses + proofs). It carries
    computational content: you can *inspect* the witnesses.

  **Non-circularity:** the axiom does not mention `NonExhaustive`, `Injective`,
  or fibers. It says: "the system comes equipped with two distinct realizations of
  the same bare certificate." That is a **structural richness** condition.

  **Identity collapse fails it:** if `compare = id` on `Bool`, then
  `compare w₁ = compare w₂` forces `w₁ = w₂`, contradicting `w₁ ≠ w₂`.

  **IC discharges it:** two distinct `RoleSeparatedSkeleton`s with the same
  `AdmissibleSummitDerivation` extraction are exactly such witnesses.

  ## The meta-theorem

  We also prove that **any** predicate on a bare `RCS` that implies `NonExhaustive`
  must imply `¬ Injective compare` — so the forcing must come from structure
  (witness data, cardinality, topology, computability), not from the comparison
  map alone. This is the honest ceiling.
-/

import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Nontrivial.Defs
import ReflexiveArchitecture.Universal.ExhaustionDefinitions
import ReflexiveArchitecture.Universal.FiberBasics
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal.Summit

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-! ### Meta-theorem: the honest ceiling -/

/-- **Meta-theorem (honest ceiling):** any predicate on a `RCS` that implies
`NonExhaustive` also implies `¬ Injective compare`. There is no escape from this
at the level of bare comparison maps — forcing must come from structural data. -/
theorem nonExhaustive_implies_not_injective (S : ReflectiveCertificationSystem Bare Realized)
    (h : NonExhaustive S) : ¬Function.Injective S.compare := by
  intro hinj
  rcases h with ⟨x, y, hne, heq⟩
  exact hne (hinj heq)

/-- Corollary: any predicate `P` with `P S → NonExhaustive S` satisfies
`P S → ¬ Injective S.compare`. The forcing cannot avoid non-injectivity. -/
theorem forcing_implies_not_injective {P : ReflectiveCertificationSystem Bare Realized → Prop}
    (hP : ∀ S, P S → NonExhaustive S) (S : ReflectiveCertificationSystem Bare Realized)
    (hp : P S) : ¬Function.Injective S.compare :=
  nonExhaustive_implies_not_injective S (hP S hp)

/-! ### The summit class: `AdequateReflectiveSystem` -/

/-- **Summit class (EPIC_021):** a reflective certification system equipped with
**witness diversity** — two distinguished realized elements that are distinct but
certify identically.

This is **data**, not a proposition: the witnesses are fields, not existentially
quantified. The class is:
- **non-circular:** does not mention `NonExhaustive`, `Injective`, or fibers;
- **principled:** identity-style collapse (`compare = id`) cannot satisfy it;
- **broad:** IC flagship (distinct role-separated skeletons with same extraction)
  and any system with a known nontrivial fiber can provide witnesses.

The inevitability theorem `adequate_nonExhaustive` proves `NonExhaustive` from
this data alone. -/
structure AdequateReflectiveSystem (Bare Realized : Type u) extends
    ReflectiveCertificationSystem Bare Realized where
  witness₁ : Realized
  witness₂ : Realized
  witnesses_distinct : witness₁ ≠ witness₂
  witnesses_certify_same : compare witness₁ = compare witness₂

/-- **Summit inevitability (EPIC_021):** every adequate reflective system is
non-exhaustive. The proof is one line: the two witnesses *are* the existential
witnesses for `NonExhaustive`. -/
theorem adequate_nonExhaustive (A : AdequateReflectiveSystem Bare Realized) :
    NonExhaustive A.toReflectiveCertificationSystem :=
  ⟨A.witness₁, A.witness₂, A.witnesses_distinct, A.witnesses_certify_same⟩

theorem adequate_not_minimalExhaustive (A : AdequateReflectiveSystem Bare Realized) :
    ¬MinimalExhaustive A.toReflectiveCertificationSystem :=
  (nonExhaustive_iff_not_minimal _).1 (adequate_nonExhaustive A)

/-- Identity collapse on `Bool` cannot be made adequate: the witness-sameness
axiom forces `w₁ = w₂`, contradicting distinctness. -/
theorem identityCompare_not_adequate :
    ∀ (A : AdequateReflectiveSystem Bool Bool),
      A.compare = id → False := by
  intro A hid
  have := A.witnesses_certify_same
  rw [hid] at this
  exact A.witnesses_distinct this

/-- More generally: any adequate system has non-injective comparison. -/
theorem adequate_not_injective (A : AdequateReflectiveSystem Bare Realized) :
    ¬Function.Injective A.compare := by
  intro hinj
  exact A.witnesses_distinct (hinj A.witnesses_certify_same)

/-- Forgetful map to minimal `RCS`. -/
abbrev AdequateReflectiveSystem.toRCS (A : AdequateReflectiveSystem Bare Realized) :
    ReflectiveCertificationSystem Bare Realized :=
  A.toReflectiveCertificationSystem

/-! ### Universality statement (thesis form) -/

/-- **Summit universality (EPIC_021, thesis form):** for every adequate reflective
system, non-exhaustion is structurally inevitable. -/
theorem summit_adequacy_universality :
    ∀ (A : AdequateReflectiveSystem Bare Realized),
      NonExhaustive A.toRCS :=
  fun A => adequate_nonExhaustive A

end ReflexiveArchitecture.Universal.Summit
