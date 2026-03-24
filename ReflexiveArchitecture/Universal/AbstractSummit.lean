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

  **Conditional universality (EPIC_019):** conditional **Theorem B** is proved for explicit
  structural forcing classes (finite pigeonhole; subsingleton bare + nontrivial
  realized; infinite realized into finite bare; self-location gap) in
  `ConditionalUniversality` and `Universal/Forcing/`. This is the “summit” step for
  **Route 3** (dichotomy + exclusion) at the abstract layer; further refinements of H3
  remain optional research targets.
-/

import ReflexiveArchitecture.Universal.ConditionalUniversality
import ReflexiveArchitecture.Universal.Dichotomy
import ReflexiveArchitecture.Universal.ReflectiveFormalSystem
import ReflexiveArchitecture.Universal.Instances.ToyFiber
import ReflexiveArchitecture.Universal.Instances.ICInstance

universe u

namespace ReflexiveArchitecture.Universal

open ConditionalUniversality
open Forcing

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

/-!
### Summit aliases (conditional Theorem B re-exports)

Same logical content as in `ConditionalUniversality`; short names for the abstract
summit package (`theoremSummit_conditional*`).
-/

/-- **Theorem A** (alias of `theoremU4_minimal_or_nonExhaustive` / `theoremA_abstract_dichotomy`). -/
theorem theoremSummit_conditionalA {Bare Realized : Type u} (S : ReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S ∨ NonExhaustive S :=
  theoremA_abstract_dichotomy S

/-- **Theorem B** — finite pigeonhole forcing. -/
theorem theoremSummit_conditionalB_finiteCard {Bare Realized : Type u} [Fintype Realized] [Fintype Bare]
    (S : ReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : NonExhaustive S :=
  theoremB_finiteCard_nonExhaustive S h

/-- **Theorem B** — subsingleton bare + nontrivial realized. -/
theorem theoremSummit_conditionalB_subsingletonBare {Bare Realized : Type u} [Subsingleton Bare]
    [Nontrivial Realized] (S : ReflectiveCertificationSystem Bare Realized) : NonExhaustive S :=
  theoremB_subsingletonBare_nonExhaustive S

/-- **Theorem B** — infinite realized into finite bare. -/
theorem theoremSummit_conditionalB_infiniteFinite {Bare Realized : Type u} [Infinite Realized] [Finite Bare]
    (S : ReflectiveCertificationSystem Bare Realized) : NonExhaustive S :=
  theoremB_infiniteFinite_nonExhaustive S

/-- **Theorem B** from discharged `RichReflectiveCandidates` (H1–H2). -/
theorem theoremSummit_conditionalB_richCandidates {Bare Realized : Type u}
    (C : RichReflectiveCandidates Bare Realized) : NonExhaustive C.system :=
  theoremB_richReflectiveCandidates_nonExhaustive C

/-- **Theorem B** — self-location gap (H3). -/
theorem theoremSummit_conditionalB_selfLocationGap {Bare Realized : Type u}
    (S : ReflectiveCertificationSystem Bare Realized) (h : SelfLocationGap S) : NonExhaustive S :=
  theoremB_selfLocationGap_nonExhaustive S h

/-- **Theorem B** from `RichReflectiveSelfLocation` (H3 bundle). -/
theorem theoremSummit_conditionalB_richSelfLocation {Bare Realized : Type u}
    (C : RichReflectiveSelfLocation Bare Realized) : NonExhaustive C.system :=
  theoremB_richReflectiveSelfLocation_nonExhaustive C

end ReflexiveArchitecture.Universal
