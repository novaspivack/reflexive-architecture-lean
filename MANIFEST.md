# reflexive-architecture-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc3`  
**Mathlib:** v4.29.0-rc3 (via `lakefile.lean`)  
**Build:** `lake build` from this directory  
**Root import:** `ReflexiveArchitecture.lean`  
**Formalization map:** `STRATA_FORMALIZATION_MAP.md` (module tree + theorem glosses)  
**Last verified:** 2026-03-22 — clean build; no `sorry` in proof terms under `ReflexiveArchitecture/`.

---

## Layout

| Area | Path | Role |
|------|------|------|
| Outer | `ReflexiveArchitecture/Outer/` | `ReflexiveLayer`, `semantic_remainder_or_nontotality` |
| Middle | `ReflexiveArchitecture/Middle/` | `RealizationLayer`, composition projections |
| Inner | `ReflexiveArchitecture/Inner/` | `CertificationLayer`, `inner_residue_package` |
| Bridge | `ReflexiveArchitecture/Bridge/` | `Architecture` (with coherence axioms), layered + stratified + bridge P0–P2 + non-erasure summit |
| Instances | `ReflexiveArchitecture/Instances/` | `ToyCombinedInstance` (enriched + flat architectures) |
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

---

## Sorry / axiom policy

No `sorry` in shipped proof terms. No program-specific `axiom` beyond Mathlib.
