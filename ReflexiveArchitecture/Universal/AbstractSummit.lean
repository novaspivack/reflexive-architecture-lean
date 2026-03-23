/-
  EPIC_019 — Abstract summit package: classical dichotomy (U4), raw-system extraction
  (U2), and explicit pointers to **discharged** non-exhaustion (IC Phase II + toy fiber).

  **Scope boundary (honest “summit” for this layer):**

  * **U4** is proved: `theoremU4_minimal_or_nonExhaustive` — classical
    `MinimalExhaustive ∨ NonExhaustive` for *every* abstract `ReflectiveCertificationSystem`.
  * **U2** is proved in the **existence** sense: any raw `compare` extends to a full RCS
    once canonical/soundness data are chosen (`exists_rcs_of_raw`, `toRCS_default`).
  * **Concrete non-exhaustion** is **not** universal over all abstract systems (identity
    `compare` is a counterexample). It is **witnessed** in-repo by:
    `Universal.Instances.ic_nonExhaustive_of_distinct_roles` (IC) and
    `Universal.Instances.toyProduct_nonExhaustive` (synthetic product projection).

  What is **not** here: a proof that *every* “mathematically rich” formal system in the
  wild is non-exhaustive without extra hypotheses — that would require a general
  definition of richness that **forces** non-injectivity of `compare`. The Strata
  program’s **computability / diagonal** and **IC summit** layers supply such forcing
  in **concrete** corpora; this file aggregates the abstract comparison/fiber layer
  those results map into.
-/

import ReflexiveArchitecture.Universal.Dichotomy
import ReflexiveArchitecture.Universal.ReflectiveFormalSystem
import ReflexiveArchitecture.Universal.Instances.ToyFiber
import ReflexiveArchitecture.Universal.Instances.ICInstance

universe u

namespace ReflexiveArchitecture.Universal

/-- Named re-export of **U4** (classical collapse-or-fiber dichotomy). -/
theorem theoremU4_minimal_or_nonExhaustive {Bare Realized : Type u}
    (S : ReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S ∨ NonExhaustive S :=
  minimal_exhaustive_or_nonExhaustive_classical S

/-- Named re-export of **U2** (existence of an RCS extending any raw compare-map). -/
theorem theoremU2_rcs_from_raw {Bare Realized : Type u} (F : RawReflectiveFormalSystem Bare Realized)
    (Canonical : Bare → Prop) (Sound : Prop) :
    ∃ S : ReflectiveCertificationSystem Bare Realized, S.compare = F.compare ∧
      S.Canonical = Canonical ∧ S.Sound = Sound :=
  exists_rcs_of_raw F Canonical Sound

end ReflexiveArchitecture.Universal
