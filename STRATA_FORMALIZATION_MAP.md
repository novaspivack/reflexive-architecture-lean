# Strata formalization map

**Purpose:** Human-readable map of the `reflexive-architecture-lean` package: module roles, exported theorem names, and what each result does *and does not* claim. Authoritative build/policy: `MANIFEST.md`. Citation snapshot and build fingerprint: `ARTIFACT.md`.

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
| `ReflexiveArchitecture/Instances/FromAPS.lean` | Parametric `RealizationLayer` from APS-style hypotheses; `apsRealizationLayer`, `apsRealizationLayerFromIff` (marked `@[reducible]` for typeclass/elaboration hygiene). |
| `ReflexiveArchitecture/Instances/FromNEMS.lean` | Parametric `ReflexiveLayer` from NEMS-style hypotheses; `nemsReflexiveLayer` (`@[reducible]`). |
| `ReflexiveArchitecture/Instances/FromIC.lean` | Parametric `CertificationLayer` from IC-style hypotheses; `icCertificationLayer` (`@[reducible]`). |
| `ReflexiveArchitecture/Instances/ConcreteArchitecture.lean` | Combined `Architecture` from outer+middle+inner parametric data; `concreteArchitecture` (`@[reducible]`). |
| `ReflexiveArchitecture/Universal/ReflectiveCertificationSystem.lean` | **EPIC_019 Phase I:** minimal `ReflectiveCertificationSystem` (bare/realized carriers, `compare`, `Canonical`, `Sound`). |
| `ReflexiveArchitecture/Universal/FiberBasics.lean` | Fibers of `compare`, injectivity ↔ fiber subsingleton, non-injective ⇒ distinct points in one fiber. |
| `ReflexiveArchitecture/Universal/ExhaustionDefinitions.lean` | `MinimalExhaustive` / `StrongExhaustive` / `NonExhaustive`, `CanonicalRegion`, local strong exhaustion on canonical locus. |
| `ReflexiveArchitecture/Universal/SectionsAndObstructions.lean` | `IsSection` (`LeftInverse compare s`), surjectivity, `LiftableWith`, trivial obstruction scaffold. |
| `ReflexiveArchitecture/Universal/Instances/ICInstance.lean` | **EPIC_019 Phase II:** `icReflectiveCertificationSystem` (IC mirror witness → `ReflectiveCertificationSystem`); abstract `NonExhaustive` / nontrivial fiber from distinct roles, same bare record. |
| `ReflexiveArchitecture/Universal/Dichotomy.lean` | **U4:** classical `MinimalExhaustive ∨ NonExhaustive`. |
| `ReflexiveArchitecture/Universal/ReflectiveFormalSystem.lean` | **U2:** `RawReflectiveFormalSystem` + `toRCS` / `exists_rcs_of_raw`. |
| `ReflexiveArchitecture/Universal/Instances/ToyFiber.lean` | Product projection toy; abstract `NonExhaustive` without IC. |
| `ReflexiveArchitecture/Universal/AbstractSummit.lean` | Aggregates summit-level universal theorems + scope doc; re-exports `theoremSummit_conditionalA` / `theoremSummit_conditionalB_*` (conditional Theorem B). |
| `ReflexiveArchitecture/Universal/ConditionalUniversality.lean` | Theorem A; Theorem B (finite card; subsingleton bare + nontrivial realized; infinite→finite; self-location gap); `RichReflectiveCandidates`, `RichReflectiveSelfLocation`. |
| `ReflexiveArchitecture/Universal/Forcing/FiniteCardForcing.lean` | Finite pigeonhole ⇒ `NonExhaustive`. |
| `ReflexiveArchitecture/Universal/Forcing/SubsingletonBareForcing.lean` | `Subsingleton Bare` + `Nontrivial Realized` ⇒ `NonExhaustive`. |
| `ReflexiveArchitecture/Universal/Forcing/InfiniteFiniteForcing.lean` | `Infinite Realized` + `Finite Bare` ⇒ `NonExhaustive`. |
| `ReflexiveArchitecture/Universal/Forcing/SelfLocationForcing.lean` | `SelfLocationGap` (section + off-witness) ⇒ `NonExhaustive`. |
| `ReflexiveArchitecture/Universal/Strong/StructuredRCS.lean` | EPIC_020: `StructuredReflectiveCertificationSystem` (nontrivial bare + realized). |
| `ReflexiveArchitecture/Universal/Strong/Inevitability.lean` | Composed `inevitability_structured_*` (structured + EPIC_019 forcing). |
| `ReflexiveArchitecture/Universal/Strong/Counterexamples.lean` | `identityCompareRCS`, `equivCompareRCS` — injective collapses. |
| `ReflexiveArchitecture/Universal/Strong/SelfLocationComponents.lean` | `HasGlobalSection` ↔ `StrongExhaustive`; `SelfLocationGap` ↔ `HasOffSectionWitness`. |
| `ReflexiveArchitecture/Universal/Strong/RichStructuredClasses.lean` | Bundled rich classes (`FinitePigeonholeStructured`, `InfiniteFiniteStructured`, `SelfLocationGapStructured`) with unconditional `NonExhaustive` for members; umbrella `BundledRich` (inductive sum) + `BundledRichStructured` typeclass. |
| `ReflexiveArchitecture/Universal/Strong/StructuredDichotomy.lean` | `structured_minimal_or_nonExhaustive`: classical dichotomy on `StructuredReflectiveCertificationSystem.toRCS`. |
| `ReflexiveArchitecture/Universal/Strong/ICStructuredDischarge.lean` | IC carriers + nontriviality ⇒ `StructuredReflectiveCertificationSystem` packaging. |
| `ReflexiveArchitecture/Universal/Strong/Instances.lean` | `toyProductStructured`, `toyFinitePigeonholeStructured` discharges. |
| `ReflexiveArchitecture/Universal/StrongProgram.lean` | Barrel import for EPIC_020 Strong modules. |
| `ReflexiveArchitecture/Universal/Summit/Adequacy.lean` | EPIC_021: `AdequateReflectiveSystem` (witness-diversity), `adequate_nonExhaustive`, meta-theorem `forcing_implies_not_injective`, `identityCompare_not_adequate`, `adequate_not_injective`. |
| `ReflexiveArchitecture/Universal/Summit/ICAdequateDischarge.lean` | EPIC_021: `icAdequateReflectiveSystem` (IC → adequate), `ic_adequate_nonExhaustive`. |
| `ReflexiveArchitecture/Universal/Summit/Instances.lean` | EPIC_021: `toyAdequateSystem`, counterexample verifications (`no_adequate_with_identity`, `no_adequate_with_injective`). |
| `ReflexiveArchitecture/Universal/Summit/SelfGeneration.lean` | EPIC_031: `ReflectivelySufficientSystem` (fiber twist); `reflectivelySufficient_nonExhaustive` (diagonal theorem); `toAdequate` (self-generation); `identity_not_reflectivelySufficient`; `injective_not_reflectivelySufficient`. |
| `ReflexiveArchitecture/Universal/Summit/FundamentalEquivalence.lean` | EPIC_031: five-way equivalence (`NonExhaustive ↔ ¬Injective ↔ ∃ fiber automorphism ↔ witness diversity ↔ nontrivial kernel`); `all_or_nothing` dichotomy; `fiberSwap` construction; `FiveWayEquivalence` package. |
| `ReflexiveArchitecture/Universal/Summit/SummitRich.lean` | EPIC_021: `SummitRichReflectiveSystem` (= `BundledRich`), `summit_universality`, `SummitRichStructured`. |
| `ReflexiveArchitecture/Universal/SummitProgram.lean` | Barrel for EPIC_021/031 Summit modules. |
| `ReflexiveArchitecture/Universal/Residual/FiberResidual.lean` | EPIC_022: `FiberEquiv`, fiber observable law, `nonExhaustive_iff_exists_nontrivial_fiber`. |
| `ReflexiveArchitecture/Universal/Residual/ResidualStructure.lean` | EPIC_022: `BareDetermined`, RFG-T1 exclusion, RFG-T2 necessity, RFG-T4 refinement. |
| `ReflexiveArchitecture/Universal/Residual/ObservableAlgebra.lean` | EPIC_023: Boolean closure of `BareDetermined` (`∧`, `∨`, `¬`, `→`, `↔`); universal factorization (`constant_on_fibers_iff_factors`). |
| `ReflexiveArchitecture/Universal/Residual/WitnessFiber.lean` | EPIC_023: adequate witnesses in same fiber; fiber nontriviality independent of witness choice; `BareDetermined` depends only on `compare`. |
| `ReflexiveArchitecture/Universal/Residual/RefinementOrder.lean` | EPIC_023: trivial/identity/product refinements; `RefinesTo` preorder; product refines both components; finer separates if coarser does. |
| `ReflexiveArchitecture/Universal/Residual/Incompressibility.lean` | EPIC_023: `IncompressibleAt`; pigeonhole incompressibility; adequate systems incompressible at `PUnit` (depth ≥ 1). |
| `ReflexiveArchitecture/Universal/Residual/ResidualKernel.lean` | EPIC_024: `ResidualKernel`; kernel-nonempty ↔ `NonExhaustive`; `UnresolvedKernel` (monotone in refinement preorder); veil theorem; kernel-observable duality; residual transfer. |
| `ReflexiveArchitecture/Universal/Residual/KernelStratification.lean` | EPIC_025: `KernelAt` (fiberwise kernel); decomposition `Kernel = ⋃ KernelAt b`; symmetry; `ResolvedKernel` + partition + monotonicity; off-diagonal characterization. |
| `ReflexiveArchitecture/Universal/Residual/KernelGraph.lean` | EPIC_026: `KernelRel`, `KernelRelRefl`; fundamental connectivity theorem (fiber = connected component); kernel relation symmetry, transitivity; fiber partition = kernel equivalence classes. |
| `ReflexiveArchitecture/Universal/Residual/QuantitativeInvariants.lean` | EPIC_026: `CompareImage`, `IsRealized`; surplus witness; resolving refinement characterization; `adequate_surplus_witness`. |
| `ReflexiveArchitecture/Universal/Residual/MinimalResolution.lean` | EPIC_027: complete-fiber theorem; fiber-local resolution; independent fiber resolution; coloring interpretation; kernel neighbors; refined fiber classes; sub-partition. |
| `ReflexiveArchitecture/Universal/Residual/ResolutionComplexity.lean` | EPIC_028: per-fiber resolution lower bound; strict refinement progress; terminal refinement ↔ all singletons; finer partitions; adequate ≥ 2 colors. |
| `ReflexiveArchitecture/Universal/Residual/FundamentalTheorem.lean` | EPIC_029: exhaustion criterion (`exhaustive_iff_kernel_empty`, aliased as `vanishingCriterion`); `CompareCompatible` + `compCompatible` + `compCompatible_assoc` (category laws); `CoarserThanCompare` + optimal coarsening; `FundamentalResidualPackage` (`fiber_complete` uses explicit `@kernelAt_complete` to bind fiber parameters); `predicate_classification` (aliased as `predicateClassification`); `bareDetermined_xor_separates_kernel`; `resolution_complexity_theorem` (aliased as `resolutionComplexityTheorem`). |
| `ReflexiveArchitecture/Universal/Residual/QuantitativeResidual.lean` | EPIC_030: resolution upper/lower bounds; adequate subsingleton unresolvable; trivial-resolves-iff-exhaustive dichotomy; adequate resolution spectrum. |
| `ReflexiveArchitecture/Universal/Residual/FiberSpectrum.lean` | EPIC_030+: `FiberTrivial`, `FiberNontrivial`, `NontrivialLocus`; spectrum characterization of exhaustion/non-exhaustion; adequate nontrivial fiber; kernel-locus connection. |
| `ReflexiveArchitecture/Universal/Residual/CategoricalKernel.lean` | EPIC_029+: `FiberProduct`, `Diagonal`; kernel = fiber product minus diagonal; fiber product = diagonal ∪ kernel (disjoint); exhaustive iff fiber product = diagonal. |
| `ReflexiveArchitecture/Universal/Residual/OptimalCertification.lean` | Optimal refinement existence; zero residual characterization (5 equivalent forms); refinement gap; adequate irreducible residual; `nothing_remains_at_optimal`; **certification-refinement gap theorem** (`certification_refinement_gap`). |
| `ReflexiveArchitecture/Universal/Residual/MetaLevel.lean` | **Meta-level theorem:** bare-level blindness; `godel_compatibility`; **observable persistence:** `PersistentObservable`, `persistence_dichotomy`, `exists_persistent_of_unresolved`, `no_persistent_if_resolved`; **persistent-observable secondary family:** `adequate_has_persistent_observables`, `persistent_iff_separates_unresolved`, `persistent_implies_nonExhaustive`, `persistence_dichotomy_support`. |
| `ReflexiveArchitecture/Universal/Residual/RCSCategory.lean` | **Category of RCS:** `RCSCategoryLaws` (4 category laws all by `rfl`); `rcsCategoryLaws`; kernel functoriality: `kernelFunctor_id`, `kernelFunctor_comp`; naturality: `fundamentalPackage_compare_natural`; `rcsCat_id_law`, `rcsCat_comp_id_left`, `rcsCat_comp_id_right`, `rcsCat_comp_assoc`. |
| `ReflexiveArchitecture/Universal/Residual/UniversalForgetting.lean` | **Universal theory of forgetting:** `rcsOfMap` (any function → RCS); `forgettingKernel`; `universal_fundamental_equivalence`; `universal_observable_duality`; `universal_resolution`; `universal_meta_blindness`; `every_function_has_residual_geometry`; `every_function_has_five_way_equivalence`. |
| `ReflexiveArchitecture/Universal/ResidualProgram.lean` | Barrel for EPIC_022–030+ Residual modules (17 files). |

**Authoritative artifact blurb:** `MANIFEST.md` (build index); **`ARTIFACT.md`** (citation/build fingerprint and paper paths).

**Root:** `ReflexiveArchitecture.lean` imports all modules above (including Universal / EPIC_019 through EPIC_031 `SummitProgram` + `ResidualProgram`).

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
- **2026-03-24:** Documented `Instances` modules in the module tree (`FromAPS`, `FromNEMS`, `FromIC`, `ConcreteArchitecture`) including `@[reducible]` on parametric layer defs; noted `FundamentalTheorem` `fiber_complete` proof binding; added **`ARTIFACT.md`** cross-links. Consumer-build linter follow-up: **`docs/CONSUMER_BUILD_NOTE.md`** (canonical in public `reflexive-architecture-lean`; mirror optional in private monorepo `reflexive-architecture/lean/NOTE.md`).
