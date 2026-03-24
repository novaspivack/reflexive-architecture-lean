/-
  EPIC_019 — **H3 (non-circular):** “self-location gap” relative to a chosen
  global section.

  A **section** `s : Bare → Realized` satisfies `compare (s b) = b` for all bare
  certificates — a canonical way to realize each bare label. **Self-location gap**
  says there exists a realization `x` that is **not** the canonical lift of its own
  certificate: `x ≠ s (compare x)`.

  This does **not** assume `NonExhaustive` or mention fibers; it is a reflective
  “misalignment” hypothesis. It **implies** `NonExhaustive` because necessarily
  `compare x = compare (s (compare x))` while `x` and `s (compare x)` are distinct.

  **Identity-style collapse** (`compare = id` with `s = id`) rules out the gap:
  then `x ≠ s (compare x) = x` is impossible.
-/

import ReflexiveArchitecture.Universal.ExhaustionDefinitions

universe u

namespace ReflexiveArchitecture.Universal.Forcing

open ReflexiveArchitecture.Universal

variable {Bare Realized : Type u}

/-- **H3 — self-location gap:** some global section exists, but some witness is not its
own canonical lift. -/
def SelfLocationGap (S : ReflectiveCertificationSystem Bare Realized) : Prop :=
  ∃ s : Bare → Realized,
    (∀ b : Bare, S.compare (s b) = b) ∧
      ∃ x : Realized, x ≠ s (S.compare x)

theorem nonExhaustive_of_selfLocationGap (S : ReflectiveCertificationSystem Bare Realized)
    (h : SelfLocationGap S) : NonExhaustive S := by
  rcases h with ⟨s, hs, x, hx⟩
  exact ⟨x, s (S.compare x), hx, (hs (S.compare x)).symm⟩

theorem not_minimalExhaustive_of_selfLocationGap (S : ReflectiveCertificationSystem Bare Realized)
    (h : SelfLocationGap S) : ¬MinimalExhaustive S :=
  (nonExhaustive_iff_not_minimal S).1 (nonExhaustive_of_selfLocationGap S h)

/-- A self-location gap yields a **strong** exhaustion witness (existence of a global
left-inverse section for `compare`). -/
theorem strongExhaustive_of_selfLocationGap (S : ReflectiveCertificationSystem Bare Realized)
    (h : SelfLocationGap S) : StrongExhaustive S := by
  rcases h with ⟨s, hs, _⟩
  exact ⟨s, hs⟩

structure SelfLocationGapBundle (Bare Realized : Type u) where
  system : ReflectiveCertificationSystem Bare Realized
  gap : SelfLocationGap system

theorem nonExhaustive_of_selfLocationGapBundle (H : SelfLocationGapBundle Bare Realized) :
    NonExhaustive H.system :=
  nonExhaustive_of_selfLocationGap H.system H.gap

end ReflexiveArchitecture.Universal.Forcing
