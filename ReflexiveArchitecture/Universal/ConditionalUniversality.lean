/-
  EPIC_019 — Conditional universal non-exhaustion (abstract layer).

  * **Theorem A (abstract dichotomy)** — classical
    `MinimalExhaustive ∨ NonExhaustive` for any `ReflectiveCertificationSystem`.
  * **Theorem B (richness excludes exhaustion)** — **proved** for several **structural**
    forcing classes (finite pigeonhole; subsingleton bare + nontrivial realized;
    infinite realized into finite bare) and for **H3** as **`SelfLocationGap`**
    (`Universal/Forcing/SelfLocationForcing.lean`): a global section exists but some
    witness is not its own canonical lift (`x ≠ s (compare x)`).

-/

import ReflexiveArchitecture.Universal.Dichotomy
import ReflexiveArchitecture.Universal.Forcing.FiniteCardForcing
import ReflexiveArchitecture.Universal.Forcing.InfiniteFiniteForcing
import ReflexiveArchitecture.Universal.Forcing.SelfLocationForcing
import ReflexiveArchitecture.Universal.Forcing.SubsingletonBareForcing
import ReflexiveArchitecture.Universal.ReflectiveCertificationSystem

universe u

namespace ReflexiveArchitecture.Universal.ConditionalUniversality

open ReflexiveArchitecture.Universal
open ReflexiveArchitecture.Universal.Forcing

variable {Bare Realized : Type u}

/-- **Theorem A (abstract dichotomy).** Same content as
`minimal_exhaustive_or_nonExhaustive_classical` — the fork between injective
comparison (minimal exhaustion) and non-exhaustive comparison. -/
theorem theoremA_abstract_dichotomy (S : ReflectiveCertificationSystem Bare Realized) :
    MinimalExhaustive S ∨ NonExhaustive S :=
  minimal_exhaustive_or_nonExhaustive_classical S

/-!
### Theorem B (richness excludes exhaustion)

**Route 1 — structural forcing (proved in `Universal/Forcing/`):**

* **Finite pigeonhole:** `Fintype` + `card Bare < card Realized`.
* **Degenerate bare + plural realized:** `Subsingleton Bare` + `Nontrivial Realized`.
* **Infinite into finite:** `Infinite Realized` + `Finite Bare`.
* **H3 — self-location gap:** `SelfLocationGap S` (section + off-witness).

**H1–H2 bundle:** `RichReflectiveCandidates` discharges **H1** / **H2** only.
**H3 alone:** `RichReflectiveSelfLocation` or `SelfLocationGap` as hypothesis.
-/

/-- **Theorem B (finite-cardinality forcing).** Pigeonhole: more realizations than bare
certificates ⇒ collision ⇒ `NonExhaustive`. -/
theorem theoremB_finiteCard_nonExhaustive [Fintype Realized] [Fintype Bare]
    (S : ReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : NonExhaustive S :=
  nonExhaustive_of_fintype_card_lt S h

/-- Same as `theoremB_finiteCard_nonExhaustive`, packaged as `¬ MinimalExhaustive`. -/
theorem theoremB_finiteCard_not_minimalExhaustive [Fintype Realized] [Fintype Bare]
    (S : ReflectiveCertificationSystem Bare Realized)
    (h : Fintype.card Bare < Fintype.card Realized) : ¬MinimalExhaustive S :=
  not_minimalExhaustive_of_fintype_card_lt S h

/-- **Theorem B (subsingleton bare, nontrivial realized).** -/
theorem theoremB_subsingletonBare_nonExhaustive [Subsingleton Bare] [Nontrivial Realized]
    (S : ReflectiveCertificationSystem Bare Realized) : NonExhaustive S :=
  nonExhaustive_of_subsingleton_bare_nontrivial_realized S

theorem theoremB_subsingletonBare_not_minimalExhaustive [Subsingleton Bare] [Nontrivial Realized]
    (S : ReflectiveCertificationSystem Bare Realized) : ¬MinimalExhaustive S :=
  not_minimalExhaustive_of_subsingleton_bare_nontrivial_realized S

/-- **Theorem B (infinite realized, finite bare).** -/
theorem theoremB_infiniteFinite_nonExhaustive [Infinite Realized] [Finite Bare]
    (S : ReflectiveCertificationSystem Bare Realized) : NonExhaustive S :=
  nonExhaustive_of_infinite_realized_finite_bare S

theorem theoremB_infiniteFinite_not_minimalExhaustive [Infinite Realized] [Finite Bare]
    (S : ReflectiveCertificationSystem Bare Realized) : ¬MinimalExhaustive S :=
  not_minimalExhaustive_of_infinite_realized_finite_bare S

/-- **Theorem B (H3 — self-location gap).** Global section + a witness not on that section. -/
theorem theoremB_selfLocationGap_nonExhaustive (S : ReflectiveCertificationSystem Bare Realized)
    (h : SelfLocationGap S) : NonExhaustive S :=
  nonExhaustive_of_selfLocationGap S h

theorem theoremB_selfLocationGap_not_minimalExhaustive (S : ReflectiveCertificationSystem Bare Realized)
    (h : SelfLocationGap S) : ¬MinimalExhaustive S :=
  not_minimalExhaustive_of_selfLocationGap S h

/-- Carrier for discharged **H3** only (`SelfLocationGap`). -/
structure RichReflectiveSelfLocation (Bare Realized : Type u) where
  system : ReflectiveCertificationSystem Bare Realized
  /-- H3 — self-location gap (non-circular; see `SelfLocationForcing.lean`). -/
  h3_selfLocationGap : SelfLocationGap system

theorem theoremB_richReflectiveSelfLocation_nonExhaustive (C : RichReflectiveSelfLocation Bare Realized) :
    NonExhaustive C.system :=
  nonExhaustive_of_selfLocationGap C.system C.h3_selfLocationGap

theorem theoremB_richReflectiveSelfLocation_not_minimalExhaustive
    (C : RichReflectiveSelfLocation Bare Realized) : ¬MinimalExhaustive C.system :=
  (nonExhaustive_iff_not_minimal C.system).1 (theoremB_richReflectiveSelfLocation_nonExhaustive C)

/-- **H1–H2** carrier (structural; independent of H3). -/
structure RichReflectiveCandidates (Bare Realized : Type u) where
  system : ReflectiveCertificationSystem Bare Realized
  /-- H1 — bare certification carrier is a subsingleton (degenerate bare interface). -/
  h1_bareSingleton : Subsingleton Bare
  /-- H2 — realized carrier is nontrivial (plural witness space). -/
  h2_realizedNontrivial : Nontrivial Realized

/-- **Theorem B from the discharged H1–H2 bundle.** -/
theorem theoremB_richReflectiveCandidates_nonExhaustive (C : RichReflectiveCandidates Bare Realized) :
    NonExhaustive C.system := by
  haveI := C.h1_bareSingleton
  haveI := C.h2_realizedNontrivial
  exact nonExhaustive_of_subsingleton_bare_nontrivial_realized C.system

theorem theoremB_richReflectiveCandidates_not_minimalExhaustive
    (C : RichReflectiveCandidates Bare Realized) : ¬MinimalExhaustive C.system :=
  (nonExhaustive_iff_not_minimal C.system).1 (theoremB_richReflectiveCandidates_nonExhaustive C)

end ReflexiveArchitecture.Universal.ConditionalUniversality
