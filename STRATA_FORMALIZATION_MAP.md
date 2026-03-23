# Strata formalization map

**Purpose:** Human-readable map of the `reflexive-architecture-lean` package: module roles, exported theorem names, and what each result does *and does not* claim. Authoritative build/policy: `MANIFEST.md`.

**Program name:** Strata (outer / middle / inner reflexive architecture).

---

## Module tree

| Path | Role |
|------|------|
| `ReflexiveArchitecture/Outer/Interface.lean` | NEMS-style outer interface: internal theories, barrier hypothesis, semantic remainder vs totality, no-final-self-theory axiom. |
| `ReflexiveArchitecture/Outer/SemanticRemainder.lean` | Derives `semantic_remainder_or_nontotality` from the outer interface + barrier hypothesis. |
| `ReflexiveArchitecture/Middle/Interface.lean` | APS-style middle: indexed composition, finite tracking, gluing, `comp_iff_finiteTracking_and_gluing`. |
| `ReflexiveArchitecture/Middle/CompositionExactness.lean` | `composition_from_tracking_and_gluing` (forward projection) and `tracking_and_gluing_from_composition` (reverse). |
| `ReflexiveArchitecture/Inner/Interface.lean` | IC-style inner: routes, adequacy, canonical bare certificate, residue predicates, implication chain to fiber nontriviality. |
| `ReflexiveArchitecture/Inner/ResiduePackage.lean` | Bundles `inner_residue_package`: canonical + adequate route → split, route necessity, strict refinement, fiber nontriviality. |
| `ReflexiveArchitecture/Bridge/Architecture.lean` | `Architecture`: single carrier extending outer + middle + inner, plus two cross-layer coherence axioms (positive and negative non-erasure). |
| `ReflexiveArchitecture/Bridge/LayeredTheorem.lean` | `layered_architecture_theorem`: all three layer conclusions from bundled hypotheses. |
| `ReflexiveArchitecture/Bridge/CollapsePredicates.lean` | Abstract collapse predicates with defeat implications for stratified non-collapse. |
| `ReflexiveArchitecture/Bridge/StratifiedNonCollapse.lean` | `stratified_noncollapse` from layered theorem + collapse predicates. |
| `ReflexiveArchitecture/Bridge/BareCanonicityNotReflectiveFinality.lean` | Bridge P0: model-theoretic separation showing `EnrichedIrreducibility` is independent of `CanonicalBareCertificate`. |
| `ReflexiveArchitecture/Bridge/GluingRouteCoherence.lean` | Bridge P1: `GlueRouteCoherent` packages middle tracking+gluing + adequate route; implies composition and inner residue under canonical bare cert. |
| `ReflexiveArchitecture/Bridge/SemanticRemainderToEnrichedGap.lean` | Bridge P2: `InnerEnrichedGap` (strict refinement + fiber); independence of inner gap from outer theory extent; joint outer+inner from layered. |
| `ReflexiveArchitecture/Bridge/NonErasurePrinciple.lean` | **Summit:** non-erasure biconditional, full architecture non-erasure, unified non-erasure law, enriched non-finality. |
| `ReflexiveArchitecture/Bridge/LinkedArchitecture.lean` | **Task D complete:** `LinkedArchitecture` class; `linkedArchitectureFromRemainder` proves both coherence axioms definitionally; unconditional biconditional and all non-erasure theorems without totality. |
| `ReflexiveArchitecture/Instances/ToyCombinedInstance.lean` | Enriched toy (outer has remainder → coherence holds by contradiction on antecedent) and flat toy (outer has no theories → coherence trivially). |
| `ReflexiveArchitecture/Universal/ReflectiveCertificationSystem.lean` | **EPIC_019 Phase I:** minimal `ReflectiveCertificationSystem` (bare/realized carriers, `compare`, `Canonical`, `Sound`). |
| `ReflexiveArchitecture/Universal/FiberBasics.lean` | Fibers of `compare`, injectivity ↔ fiber subsingleton, non-injective ⇒ distinct points in one fiber. |
| `ReflexiveArchitecture/Universal/ExhaustionDefinitions.lean` | `MinimalExhaustive` / `StrongExhaustive` / `NonExhaustive`, `CanonicalRegion`, local strong exhaustion on canonical locus. |
| `ReflexiveArchitecture/Universal/SectionsAndObstructions.lean` | `IsSection` (`LeftInverse compare s`), surjectivity, `LiftableWith`, trivial obstruction scaffold. |
| `ReflexiveArchitecture/Universal/Instances/ICInstance.lean` | **EPIC_019 Phase II:** `icReflectiveCertificationSystem` (IC mirror witness → `ReflectiveCertificationSystem`); abstract `NonExhaustive` / nontrivial fiber from distinct roles, same bare record. |

**Root:** `ReflexiveArchitecture.lean` imports all modules above (including Universal / EPIC_019 Phases I–II).

---

## Architecture cross-layer coherence axioms

`Architecture` (in `Bridge/Architecture.lean`) extends the three layer interfaces and carries two cross-layer axioms grounding the non-erasure principle:

| Field | Direction | Statement |
|-------|-----------|-----------|
| `outer_remainder_forces_inner_enrichment` | Positive | `(∃ T, InternalTheory T ∧ SemanticRemainder T) → EnrichedIrreducibility` |
| `outer_exhaustion_kills_inner_enrichment` | Negative | `(∀ T, InternalTheory T → TotalOn T ∧ ¬ SemanticRemainder T) → ¬ EnrichedIrreducibility` |

Together, under universal totality, these yield the biconditional: `EnrichedIrreducibility ↔ ∃ T, SemanticRemainder T`.

---

## Entry-point theorems

### Core spine (milestone 1)

| Lean name | Informal meaning | Does *not* claim |
|-----------|-----------------|-----------------|
| `Outer.semantic_remainder_or_nontotality` | Under barrier, every internal theory has remainder or fails totality. | Specific syntax/semantics model; abstract interface only. |
| `Middle.composition_from_tracking_and_gluing` | Finite tracking ∧ gluing ⇒ indexed composition. | Gluing from composition alone. |
| `Inner.inner_residue_package` | Canonical bare cert + ∃ adequate route ⇒ split, necessity, strict refinement, fiber nontriviality. | Routes = outer theories; no "NEMS = IC". |
| `Bridge.layered_architecture_theorem` | Bundles all three conclusions under one `Architecture` + hypotheses. | Bridge laws between *distinct* concrete corpora. |
| `Bridge.stratified_noncollapse` | No architecture collapses all three strata simultaneously. | Canonical definition of real-world collapse. |

### Bridge track (milestone 2)

| Lean name | Informal meaning | Does *not* claim |
|-----------|-----------------|-----------------|
| `Bridge.ReflectiveFinality` | Predicate: `¬ EnrichedIrreducibility`. | Identified with "truth of IC paper". |
| `Bridge.canonical_bare_does_not_pin_enriched_irreducibility` | Two certification layers share bare canonicity but differ on `EnrichedIrreducibility`. | A stronger axiomatization couldn't imply a link. |
| `Bridge.bare_canonicity_independent_of_reflective_finality` | ∃ canonical witnesses with and without `ReflectiveFinality`. | Independence outside current interface. |
| `Bridge.GlueRouteCoherent` | `HasFiniteTracking ∧ HasGluing ∧ (∃ adequate route)`. | Middle "gluing" = inner route objects. |
| `Bridge.glue_route_coherent_canonical_implies_composition_and_strict_refinement` | Coherent glue + canonical bare cert ⇒ composition ∧ strict refinement ∧ fiber nontriviality. | Gluing alone ⇒ inner fiber. |
| `Bridge.InnerEnrichedGap` | `StrictRefinement ∧ FiberNontriviality`. | — |
| `Bridge.inner_enriched_gap_independent_of_outer_theory_extent` | Inner gap holds regardless of outer theory-type extent. | A morphism from outer to inner semantics. |
| `Bridge.joint_outer_inner_from_layered` | Full layered hypotheses ⇒ outer remainder-or-nontotality ∧ inner enriched gap. | New strength beyond `layered_architecture_theorem`. |

### Non-Erasure summit (milestone 3)

| Lean name | Informal meaning | Does *not* claim |
|-----------|-----------------|-----------------|
| `Bridge.outer_remainder_forces_enriched_irreducibility` | ∃ T with remainder ⇒ enriched irreducibility holds. | Equivalent for nontotality without remainder. |
| `Bridge.outer_exhaustion_kills_enriched_irreducibility` | ∀ T total and no remainder ⇒ ¬ enriched irreducibility. | Converse without extra assumptions. |
| `Bridge.enriched_iff_outer_remainder_total` | Under universal totality: enriched ↔ ∃ T with remainder. | Holds without totality assumption. |
| `Bridge.nonerasure_principle` | Layered hypotheses + ∃ remainder witness ⇒ enriched irreducibility. | Applied to specific NEMS/IC corpora directly. |
| `Bridge.full_architecture_nonerasure` | Outer non-exhaustion ∧ enriched ∧ full inner residue, all from layered + remainder witness. | — |
| `Bridge.unified_nonerasure_law` | Enriched ↔ ∃ remainder (under universal totality): the unifying law behind NEMS and IC. | Holds without totality or without the coherence axioms. |
| `Bridge.nonerasure_from_barrier_with_totality` | Barrier + totality ⇒ every internal theory has remainder ∧ enriched holds. | — |
| `Bridge.enriched_hence_not_reflexively_final` | Under layered + remainder witness: reflective finality (`¬ enriched`) is ruled out. | Entails specific IC theorem without instantiation. |

---

## Instances

| Instance | Outer | Inner | Coherence satisfaction |
|----------|-------|-------|----------------------|
| `toyArchitecture` | `Theory = Unit`, remainder always true | `EnrichedIrreducibility = True` | Positive axiom: remainder witness exists → enriched (trivial). Negative axiom: exhaustion antecedent requires ¬ SemanticRemainder, which is always False → absurd. |
| `toyFlatArchitecture` | `Theory = Empty`, no theories | `EnrichedIrreducibility = False` | Positive axiom: ∃ T with remainder — Empty has no T, so hypothesis is vacuously False → implication trivial. Negative axiom: `¬ False = True`, trivially. |

---

## Build

```bash
cd reflexive-architecture-lean
lake build
```

Zero `sorry`. No program-specific axioms beyond Mathlib.

---

## Changelog

- **2026-03-22 (milestone 1):** Abstract architecture class + layered theorem + stratified non-collapse. Added by EPIC_015.
- **2026-03-22 (milestone 2):** Bridge P0–P2 (bare canonicity separation, gluing route coherence, inner enriched gap). Added by EPIC_016.
- **2026-03-22 (milestone 3):** Non-erasure principle + unified non-erasure law + enriched non-finality. Added by EPIC_016 continuation. Architecture class strengthened with biconditional coherence axioms.
- **2026-03-22 (milestone 4):** Concrete discharge interfaces FromAPS, FromNEMS, FromIC, ConcreteArchitecture. Task D complete: LinkedArchitecture proves both coherence axioms definitionally via `linkedArchitectureFromRemainder`; unconditional non-erasure biconditional follows without totality. Zero sorry throughout. Added by EPIC_017.
