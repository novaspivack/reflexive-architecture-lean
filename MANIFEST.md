# reflexive-architecture-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc3 (via `lakefile.lean`)  
**Build:** `lake build` from this directory  
**Root import:** `ReflexiveArchitecture.lean`  
**Formalization map:** `STRATA_FORMALIZATION_MAP.md` (module tree + theorem glosses)  
**Last verified:** 2026-03-22 — clean build on rc6 with NEMS + IC as lake deps; zero `sorry` in proof terms.  
**Lake deps:** `nems-lean` (local), `infinity-compression-lean` (local).

---

## Layout

| Area | Path | Role |
|------|------|------|
| Outer | `ReflexiveArchitecture/Outer/` | `ReflexiveLayer`, `semantic_remainder_or_nontotality` |
| Middle | `ReflexiveArchitecture/Middle/` | `RealizationLayer`, composition projections |
| Inner | `ReflexiveArchitecture/Inner/` | `CertificationLayer`, `inner_residue_package` |
| Bridge | `ReflexiveArchitecture/Bridge/` | `Architecture` (with coherence axioms), layered + stratified + bridge P0–P2 + non-erasure summit + `LinkedArchitecture` (coherence discharged) |
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
| `ReflexiveArchitecture.Instances.concreteNEMSBarrierHolds` | `Instances/ConcreteFromNEMS.lean` | Barrier holds given `hChain : TotalEffective → ComputablePred RT` (explicit open gap) |
| `ReflexiveArchitecture.Instances.concreteICCertificationLayer` | `Instances/ConcreteFromIC.lean` | ✓ `CertificationLayer (CompressionArchitecture BD n)` from `infinity-compression-lean` types |
| `ReflexiveArchitecture.Instances.concreteIC_enrichedIrrHolds` | `Instances/ConcreteFromIC.lean` | ✓ IC enriched irreducibility holds via T-C+.7 |
| `ReflexiveArchitecture.Bridge.nems_spine_both_strata` | `Bridge/DirectCrossCorpusBridge.lean` | ✓ Outer (NEMS barrier) + inner (IC T-C+.6) both hold on NEMS spine |
| `ReflexiveArchitecture.Bridge.nems_spine_strata_from_sources` | `Bridge/DirectCrossCorpusBridge.lean` | ✓ Both strata via concrete layer instances from source repos |
| `ReflexiveArchitecture.Bridge.SpinePluralityProp` | `Bridge/SharedReflexiveArchitecture.lean` | Common structural cause: ≥ 2 distinct role-separated skeletons |
| `ReflexiveArchitecture.Bridge.ic_enriched_iff_nems_remainder` | `Bridge/SharedReflexiveArchitecture.lean` | ✓ IC enriched irreducibility ↔ NEMS semantic remainder (biconditional) |
| `ReflexiveArchitecture.Bridge.ic_enriched_iff_nems_remainder_unconditional` | `Bridge/SharedReflexiveArchitecture.lean` | ✓ Unconditional form of the biconditional |

**Task D complete:** The cross-layer coherence axioms are now proved as theorems in `LinkedArchitecture` via `linkedArchitectureFromRemainder`. Coherence holds definitionally when `EnrichedIrreducibility` is defined as `∃ T, SemanticRemainder T`. The unconditional biconditional and all non-erasure theorems follow without totality assumption. `ConcreteArchitecture.lean` retains the parametric hypothesis pattern for external IC definitions; use `linkedArchitectureFromRemainder` for the fully-discharged path.

---

## Sorry / axiom policy

No `sorry` in shipped proof terms. No program-specific `axiom` beyond Mathlib.
Explicit hypothesis parameters in `ConcreteArchitecture.lean` are open mathematical
claims, not proof placeholders.
