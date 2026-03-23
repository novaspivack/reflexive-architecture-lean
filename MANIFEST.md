# reflexive-architecture-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc6 (via `lakefile.lean`)  
**Build:** `lake build` from this directory  
**Root import:** `ReflexiveArchitecture.lean`  
**Formalization map:** `STRATA_FORMALIZATION_MAP.md` (module tree + theorem glosses)  
**Last verified:** 2026-03-23 — clean build on rc6 with NEMS + IC as lake deps; zero `sorry` in proof terms; EPIC_019 Phase II (IC universal instance) in root import.  
**Lake deps:** `nems-lean` (local), `infinity-compression-lean` (local).

---

## Layout

| Area | Path | Role |
|------|------|------|
| Outer | `ReflexiveArchitecture/Outer/` | `ReflexiveLayer`, `semantic_remainder_or_nontotality` |
| Middle | `ReflexiveArchitecture/Middle/` | `RealizationLayer`, composition projections |
| Inner | `ReflexiveArchitecture/Inner/` | `CertificationLayer`, `inner_residue_package` |
| Bridge | `ReflexiveArchitecture/Bridge/` | `Architecture` (with coherence axioms), layered + stratified + bridge P0–P2 + non-erasure summit + `LinkedArchitecture` (coherence discharged) |
| Universal (EPIC_019) | `ReflexiveArchitecture/Universal/` | Abstract certification/realization comparison: `ReflectiveCertificationSystem`, fiber basics, exhaustion defs, sections/liftability (independent of NEMS/APS/IC interfaces) |
| Universal / IC | `ReflexiveArchitecture/Universal/Instances/ICInstance.lean` | `icReflectiveCertificationSystem`: IC `ReflectiveMirrorWitness` → universal layer; `NonExhaustive` from distinct roles / same bare derivation (T-F1.1d route) |
| Instances | `ReflexiveArchitecture/Instances/` | `ToyCombinedInstance` (enriched + flat); `FromAPS`, `FromNEMS`, `FromIC`, `ConcreteArchitecture` (concrete discharge interfaces) |
| Papers | `paper/` | suite TeX + *Closure, Realization, and Reflective Residue* |

---

## Architecture class cross-layer coherence axioms

`Architecture` (in `Bridge/Architecture.lean`) extends the three layer interfaces and carries:

| Axiom | Direction | Meaning |
|-------|-----------|---------|
| `outer_remainder_forces_inner_enrichment` | Positive | ∃ T with SemanticRemainder → EnrichedIrreducibility |
| `outer_exhaustion_kills_inner_enrichment` | Negative | (∀ T, total and no remainder) → ¬ EnrichedIrreducibility |

Together these form the biconditional (under universal totality): `EnrichedIrreducibility ↔ ∃ T, SemanticRemainder T`.

---

## Entry-point theorems

### Core spine (milestone 1)

| Name | File |
|------|------|
| `ReflexiveArchitecture.Outer.semantic_remainder_or_nontotality` | `Outer/SemanticRemainder.lean` |
| `ReflexiveArchitecture.Middle.composition_from_tracking_and_gluing` | `Middle/CompositionExactness.lean` |
| `ReflexiveArchitecture.Inner.inner_residue_package` | `Inner/ResiduePackage.lean` |
| `ReflexiveArchitecture.Bridge.layered_architecture_theorem` | `Bridge/LayeredTheorem.lean` |
| `ReflexiveArchitecture.Bridge.stratified_noncollapse` | `Bridge/StratifiedNonCollapse.lean` |

### Bridge track (milestone 2 — EPIC 016)

| Name | File |
|------|------|
| `ReflexiveArchitecture.Bridge.ReflectiveFinality` | `Bridge/BareCanonicityNotReflectiveFinality.lean` |
| `ReflexiveArchitecture.Bridge.canonical_bare_does_not_pin_enriched_irreducibility` | `Bridge/BareCanonicityNotReflectiveFinality.lean` |
| `ReflexiveArchitecture.Bridge.bare_canonicity_independent_of_reflective_finality` | `Bridge/BareCanonicityNotReflectiveFinality.lean` |
| `ReflexiveArchitecture.Bridge.GlueRouteCoherent` | `Bridge/GluingRouteCoherence.lean` |
| `ReflexiveArchitecture.Bridge.glue_route_coherent_canonical_implies_composition_and_strict_refinement` | `Bridge/GluingRouteCoherence.lean` |
| `ReflexiveArchitecture.Bridge.InnerEnrichedGap` | `Bridge/SemanticRemainderToEnrichedGap.lean` |
| `ReflexiveArchitecture.Bridge.inner_enriched_gap_independent_of_outer_theory_extent` | `Bridge/SemanticRemainderToEnrichedGap.lean` |
| `ReflexiveArchitecture.Bridge.joint_outer_inner_from_layered` | `Bridge/SemanticRemainderToEnrichedGap.lean` |

### Non-Erasure summit (milestone 3)

| Name | File | Status |
|------|------|--------|
| `ReflexiveArchitecture.Bridge.outer_remainder_forces_enriched_irreducibility` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.outer_exhaustion_kills_enriched_irreducibility` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.enriched_iff_outer_remainder_total` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.nonerasure_principle` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.full_architecture_nonerasure` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.unified_nonerasure_law` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.nonerasure_from_barrier_with_totality` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.enriched_hence_not_reflexively_final` | `Bridge/NonErasurePrinciple.lean` | ✓ proved |
| `ReflexiveArchitecture.Bridge.LinkedArchitecture` | `Bridge/LinkedArchitecture.lean` | ✓ class: coherence derived from `enriched_iff_remainder` |
| `ReflexiveArchitecture.Bridge.linkedArchitectureFromRemainder` | `Bridge/LinkedArchitecture.lean` | ✓ constructor: both coherence axioms proved definitionally |
| `ReflexiveArchitecture.Bridge.linked_nonerasure_unconditional` | `Bridge/LinkedArchitecture.lean` | ✓ biconditional without totality hypothesis |
| `ReflexiveArchitecture.Bridge.linked_full_nonerasure` | `Bridge/LinkedArchitecture.lean` | ✓ outer+inner+residue simultaneously |
| `ReflexiveArchitecture.Bridge.linked_barrier_forces_both` | `Bridge/LinkedArchitecture.lean` | ✓ barrier forces outer remainder and inner enriched together |

---

### Concrete discharge (milestone 4 — EPIC 017)

| Name | File | Role |
|------|------|------|
| `ReflexiveArchitecture.Instances.apsRealizationLayerFromIff` | `Instances/FromAPS.lean` | Parametric `RealizationLayer` map from APS `corrected_exactness_iff` |
| `ReflexiveArchitecture.Instances.nemsReflexiveLayer` | `Instances/FromNEMS.lean` | Parametric `ReflexiveLayer` map from NEMS `diagonal_barrier_rt` |
| `ReflexiveArchitecture.Instances.icCertificationLayer` | `Instances/FromIC.lean` | Parametric `CertificationLayer` map from IC route-residue theorems |
| `ReflexiveArchitecture.Instances.concreteArchitecture` | `Instances/ConcreteArchitecture.lean` | Combined `Architecture` instance; use `linkedArchitectureFromRemainder` for fully-discharged path |
| `ReflexiveArchitecture.Instances.crossCorpusLinkedArchitecture` | `Instances/CrossCorpusInstance.lean` | Concrete `LinkedArchitecture`; cross-corpus Iff holds by `Iff.rfl` |
| `ReflexiveArchitecture.Instances.crossCorpus_enriched_iff_remainder` | `Instances/CrossCorpusInstance.lean` | ✓ The cross-corpus Iff proved |
| `ReflexiveArchitecture.Instances.crossCorpus_full_nonerasure` | `Instances/CrossCorpusInstance.lean` | ✓ Full non-erasure package for the cross-corpus instance |
| `ReflexiveArchitecture.Instances.concreteNEMSReflexiveLayer` | `Instances/ConcreteFromNEMS.lean` | ✓ `ReflexiveLayer Framework` from `nems-lean` types |
| `ReflexiveArchitecture.Instances.concreteNEMSBarrierHolds` | `Instances/ConcreteFromNEMS.lean` | ✓ Barrier holds trivially (`BarrierHyp = True`; barrier carried by `[dc]` instance) |
| `ReflexiveArchitecture.Instances.concreteNEMS_has_semantic_remainder` | `Instances/ConcreteFromNEMS.lean` | ✓ NEMS record-truth undecidability is the concrete outer semantic remainder |
| `ReflexiveArchitecture.Instances.concreteICCertificationLayer` | `Instances/ConcreteFromIC.lean` | ✓ `CertificationLayer (CompressionArchitecture BD n)` from `infinity-compression-lean` types |
| `ReflexiveArchitecture.Instances.concreteIC_enrichedIrrHolds` | `Instances/ConcreteFromIC.lean` | ✓ IC enriched irreducibility holds via T-C+.7 |
| `ReflexiveArchitecture.Bridge.nems_spine_both_strata` | `Bridge/DirectCrossCorpusBridge.lean` | ✓ Outer (NEMS barrier) + inner (IC T-C+.6) both hold on NEMS spine |
| `ReflexiveArchitecture.Bridge.nems_spine_strata_from_sources` | `Bridge/DirectCrossCorpusBridge.lean` | ✓ Both strata via concrete layer instances from source repos |
| `ReflexiveArchitecture.Bridge.SpinePluralityProp` | `Bridge/SharedReflexiveArchitecture.lean` | Common structural cause: ≥ 2 distinct role-separated skeletons |
| `ReflexiveArchitecture.Bridge.ic_enriched_iff_nems_remainder` | `Bridge/SharedReflexiveArchitecture.lean` | ✓ IC enriched irreducibility ↔ NEMS semantic remainder (biconditional) |
| `ReflexiveArchitecture.Bridge.ic_enriched_iff_nems_remainder_unconditional` | `Bridge/SharedReflexiveArchitecture.lean` | ✓ Unconditional form of the biconditional |
| `ReflexiveArchitecture.Bridge.universal_nonerasure_law` | `Bridge/UniversalNonErasureLaw.lean` | ✓ **Universal Non-Erasure Law**: IC enriched irred ↔ NEMS remainder for ALL `RolePairDiverseCrownEligible` + `DiagonalCapable` pairs |
| `ReflexiveArchitecture.Bridge.nems_spine_from_universal` | `Bridge/UniversalNonErasureLaw.lean` | ✓ NEMS spine biconditional as corollary of the universal law |

**Task D complete:** The cross-layer coherence axioms are now proved as theorems in `LinkedArchitecture` via `linkedArchitectureFromRemainder`. Coherence holds definitionally when `EnrichedIrreducibility` is defined as `∃ T, SemanticRemainder T`. The unconditional biconditional and all non-erasure theorems follow without totality assumption. `ConcreteArchitecture.lean` retains the parametric hypothesis pattern for external IC definitions; use `linkedArchitectureFromRemainder` for the fully-discharged path.

### Universal program (EPIC_019 — Phase II)

| Name | File |
|------|------|
| `ReflexiveArchitecture.Universal.Instances.icReflectiveCertificationSystem` | `Universal/Instances/ICInstance.lean` |
| `ReflexiveArchitecture.Universal.Instances.ic_nonExhaustive_of_witnesses` | same — abstract `NonExhaustive` from two witnesses + equal bare derivation |
| `ReflexiveArchitecture.Universal.Instances.ic_nonExhaustive_of_distinct_roles` | same — from two distinct `RoleSeparatedSkeleton`s (standard construction) |
| `ReflexiveArchitecture.Universal.Instances.ic_fiber_nontrivial_of_distinct_roles` | same — nontrivial fiber over shared bare certificate |

### Universal program (EPIC_019 — abstract summit package)

| Name | File | Role |
|------|------|------|
| `ReflexiveArchitecture.Universal.minimal_exhaustive_or_nonExhaustive_classical` | `Universal/Dichotomy.lean` | **U4 (classical):** `MinimalExhaustive ∨ NonExhaustive` for any abstract RCS |
| `ReflexiveArchitecture.Universal.theoremU4_minimal_or_nonExhaustive` | `Universal/AbstractSummit.lean` | Named re-export of U4 |
| `ReflexiveArchitecture.Universal.exists_rcs_of_raw` | `Universal/ReflectiveFormalSystem.lean` | **U2 (existence):** extend any raw `compare` to a full RCS |
| `ReflexiveArchitecture.Universal.theoremU2_rcs_from_raw` | `Universal/AbstractSummit.lean` | Named re-export of U2 |
| `ReflexiveArchitecture.Universal.Instances.toyProduct_nonExhaustive` | `Universal/Instances/ToyFiber.lean` | Synthetic non-exhaustion (product projection) |
| `ReflexiveArchitecture.Universal.AbstractSummit` | `Universal/AbstractSummit.lean` | Imports IC + toy + dichotomy; module doc = scope boundary for “summit” |

**Honesty note:** There is **no** unconditional theorem “every abstract RCS is `NonExhaustive`” (injective `compare` is a counterexample). The epic’s Tier-4 “universal non-exhaustion for all rich systems” is only available **under explicit forcing hypotheses** (as in Strata’s IC/NEMS concrete layers) or as **U4 ∨** classical dichotomy.

---

## Open mathematical frontier (post–M5)

The **universal** and **single-hypothesis** non-erasure theorems package the outer/inner alignment under explicit structural hypotheses:

- **`RolePairDiverseCrownEligible`** (IC / certification side), and
- **`DiagonalCapable`** (NEMS / computability side), where the latter can be collapsed using `haltingFramework` in `Bridge/NecessityTheorem.lean`.

What is **not yet proved** is a **necessity theorem** connecting these two hypotheses: i.e. whether they are independent conditions that merely **co-occur** on the NEMS spine, or whether one implies the other (or both follow from a single underlying reflective principle). Settling that question would sharpen the “one breath” statement of the flagship law and is tracked as research follow-up (see `specs/IN-PROCESS/EPIC_019_UAT1_UNIVERSAL_ARCHITECTURE_NON_EXHAUSTION_PROGRAM.md`).

---

## Sorry / axiom policy

No `sorry` in shipped proof terms. No program-specific `axiom` beyond Mathlib.
Explicit hypothesis parameters in `ConcreteArchitecture.lean` are open mathematical
claims, not proof placeholders.
