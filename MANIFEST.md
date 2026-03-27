# reflexive-architecture-lean — manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc6 (via `lakefile.lean`)  
**Build:** `lake build` from this directory  
**Root import:** `ReflexiveArchitecture.lean`  
**Formalization map:** `STRATA_FORMALIZATION_MAP.md` (module tree + theorem glosses)  
**Artifact / citation:** `ARTIFACT.md` (build fingerprint, paper paths, consumer-build notes)  
**Last verified:** 2026-03-24 — clean build on rc6 (8270 jobs); zero `sorry`; **EPIC_019–031** (~235 theorems, 26 modules): Classification Theorem (five-way equivalence) + Vanishing Criterion + Residual Geometry Theorem + Resolution Complexity Theorem + Certification–Refinement Gap + meta-level/Gödel compatibility + **persistent-observable secondary theorem family** + **RCS category packaging** (category laws + kernel functoriality, all by `rfl`) + **universal theory of forgetting** (every function inherits the full residual geometry). New modules: `Residual/RCSCategory.lean`, expanded `Residual/MetaLevel.lean` (persistent observable spectrum, persistence-support dichotomy). **Build hygiene (same date):** consumer-facing linter cleanup — `@[reducible]` on parametric `Instances` layer constructors (`apsRealizationLayer`, `apsRealizationLayerFromIff`, `nemsReflexiveLayer`, `icCertificationLayer`, `concreteArchitecture`); proof-only `intro` / `@kernelAt_complete` polish in `Residual/FundamentalTheorem.lean` (no statement changes). See **`ARTIFACT.md`** and **`docs/CONSUMER_BUILD_NOTE.md`** (consumer linter follow-up).  
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
| Universal / conditional universality | `ReflexiveArchitecture/Universal/ConditionalUniversality.lean` | Theorem A; **Theorem B** — `theoremB_finiteCard_*`, `theoremB_subsingletonBare_*`, `theoremB_infiniteFinite_*`, `theoremB_selfLocationGap_*`, `theoremB_richReflectiveCandidates_*`, `RichReflectiveSelfLocation`; see `EPIC_019_CONDITIONAL_UNIVERSALITY_ROADMAP` |
| Universal / finite-card forcing | `ReflexiveArchitecture/Universal/Forcing/FiniteCardForcing.lean` | `nonExhaustive_of_fintype_card_lt`, `FiniteCardRichRCS` |
| Universal / subsingleton-bare forcing | `ReflexiveArchitecture/Universal/Forcing/SubsingletonBareForcing.lean` | `Subsingleton Bare` + `Nontrivial Realized` ⇒ `NonExhaustive` |
| Universal / infinite→finite forcing | `ReflexiveArchitecture/Universal/Forcing/InfiniteFiniteForcing.lean` | `Infinite Realized` + `Finite Bare` ⇒ `NonExhaustive` |
| Universal / abstract summit | `ReflexiveArchitecture/Universal/AbstractSummit.lean` | U4 + U2 re-exports; `theoremSummit_conditionalA`, `theoremSummit_conditionalB_*`; imports IC + toy + `ConditionalUniversality` |
| Universal / EPIC_020 Strong | `ReflexiveArchitecture/Universal/StrongProgram.lean` | Barrel: `StructuredReflectiveCertificationSystem`, `inevitability_structured_*`, `RichStructuredClasses` (`nonExhaustive_of_finitePigeonholeStructured`, …), `structured_minimal_or_nonExhaustive`, `icStructuredReflectiveCertificationSystem`, counterexamples, `SelfLocationComponents`; see `EPIC_020_UAT2_STRONGER_UNIVERSALITY_BEYOND_TRIVIAL_COLLAPSE` |
| Universal / EPIC_021+031 Summit | `ReflexiveArchitecture/Universal/SummitProgram.lean` | `AdequateReflectiveSystem`, `ReflectivelySufficientSystem`, five-way `FundamentalEquivalence`, `all_or_nothing`, `fiberSwap`, IC discharge, meta-theorem, `SummitRichReflectiveSystem`; see `EPIC_021` + `EPIC_031` |
| Universal / EPIC_022–030 Residual | `ReflexiveArchitecture/Universal/ResidualProgram.lean` | 17 modules: `FiberResidual`, `ResidualStructure`, `ObservableAlgebra`, `WitnessFiber`, `RefinementOrder`, `Incompressibility`, `ResidualKernel`, `KernelStratification`, `KernelGraph`, `QuantitativeInvariants`, `MinimalResolution`, `ResolutionComplexity`, `FundamentalTheorem`, `QuantitativeResidual`, `MetaLevel` (persistent observables + Gödel compatibility), `RCSCategory` (category laws + kernel functoriality), `UniversalForgetting`; see EPICs 022–030 |
| Instances | `ReflexiveArchitecture/Instances/` | `ToyCombinedInstance` (enriched + flat); `FromAPS`, `FromNEMS`, `FromIC`, `ConcreteArchitecture` (concrete discharge interfaces) |
| Papers | `paper/summit-1-closure-realization/` | *Closure, Realization, and Reflective Residue* (summit 1: program synthesis) |
| Papers | `paper/summit-2-geometry-of-what-maps-forget/` | *The Geometry of What Maps Forget* (summit 2: universal residual theory) |
| Artifact / Zenodo | `ARTIFACT.md` | Citation snapshot: build jobs, zero-sorry policy, paper paths, consumer-build note |
| Docs | `docs/CONSUMER_BUILD_NOTE.md` | Consumer `lake build` / linter hygiene (same text mirrored optionally in private monorepo `reflexive-architecture/lean/NOTE.md`) |

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
| `ReflexiveArchitecture.Universal.AbstractSummit` | `Universal/AbstractSummit.lean` | Imports IC + toy + dichotomy + `ConditionalUniversality`; `theoremSummit_conditionalA` / `theoremSummit_conditionalB_*` (conditional Theorem B) |
| `ReflexiveArchitecture.Universal.theoremSummit_conditionalA` / `theoremSummit_conditionalB_*` | same | Summit aliases for Theorem A + structural Theorem B |
| `ReflexiveArchitecture.Universal.nonExhaustive_toRCS_default_of_subsingletonBare_nontrivialRealized` | `Universal/ReflectiveFormalSystem.lean` | **Route 2:** default extraction + subsingleton-bare forcing ⇒ `NonExhaustive` |

### Universal program (EPIC_020 — stronger class scaffold)

| Name | File | Role |
|------|------|------|
| `ReflexiveArchitecture.Universal.Strong.StructuredReflectiveCertificationSystem` | `Universal/Strong/StructuredRCS.lean` | Nontrivial bare + realized; `.toRCS` forgets to minimal `RCS` |
| `ReflexiveArchitecture.Universal.Strong.inevitability_structured_finiteCard` | `Universal/Strong/Inevitability.lean` | Structured + finite pigeonhole ⇒ `NonExhaustive` |
| `ReflexiveArchitecture.Universal.Strong.FinitePigeonholeStructured` / `nonExhaustive_of_finitePigeonholeStructured` | `Universal/Strong/RichStructuredClasses.lean` | Bundled class: gap in fields ⇒ `NonExhaustive` without extra hypotheses |
| `ReflexiveArchitecture.Universal.Strong.InfiniteFiniteStructured` / `nonExhaustive_of_infiniteFiniteStructured` | same | `Infinite Realized` + `Finite Bare` packaged ⇒ `NonExhaustive` |
| `ReflexiveArchitecture.Universal.Strong.SelfLocationGapStructured` / `nonExhaustive_of_selfLocationGapStructured` | same | `SelfLocationGap` packaged ⇒ `NonExhaustive` |
| `ReflexiveArchitecture.Universal.Strong.BundledRich` / `BundledRichStructured` | `Universal/Strong/RichStructuredClasses.lean` | Umbrella sum + typeclass (`bundled : BundledRich …`); `BundledRich.base` / `toRCS` / `nonExhaustive`; `BundledRichStructured.nonExhaustive` |
| `ReflexiveArchitecture.Universal.Strong.structured_minimal_or_nonExhaustive` | `Universal/Strong/StructuredDichotomy.lean` | Classical dichotomy on `S.toRCS` for structured `S` |
| `ReflexiveArchitecture.Universal.Strong.icStructuredReflectiveCertificationSystem` | `Universal/Strong/ICStructuredDischarge.lean` | IC + nontrivial proofs ⇒ structured RCS (see file for exact typeclass assumptions) |
| `ReflexiveArchitecture.Universal.Strong.identityCompareRCS` | `Universal/Strong/Counterexamples.lean` | Injective collapse: `¬ NonExhaustive` |
| `ReflexiveArchitecture.Universal.Strong.toyFinitePigeonholeStructured_nonExhaustive` | `Universal/Strong/Instances.lean` | Bundled-class toy discharge |
| `ReflexiveArchitecture.Universal.Strong.toyBundledRichStructured` / `toyBundledRichStructured_nonExhaustive` | same | `BundledRichStructured` instance + generic `BundledRichStructured.nonExhaustive` |
| `ReflexiveArchitecture.Universal.Strong.toyProductStructured_nonExhaustive` | same | Structured toy (direct inevitability lemma) |
| `ReflexiveArchitecture.Universal.Summit.AdequateReflectiveSystem` / `adequate_nonExhaustive` | `Universal/Summit/Adequacy.lean` | **EPIC_021 summit class:** witness-diversity data ⇒ `NonExhaustive`; meta-theorem `forcing_implies_not_injective` (honest ceiling); `identityCompare_not_adequate` |
| `ReflexiveArchitecture.Universal.Summit.icAdequateReflectiveSystem` / `ic_adequate_nonExhaustive` | `Universal/Summit/ICAdequateDischarge.lean` | IC flagship discharge into `AdequateReflectiveSystem` |
| `ReflexiveArchitecture.Universal.Summit.toyAdequateSystem` / `toyAdequate_nonExhaustive` | `Universal/Summit/Instances.lean` | Toy adequate system + counterexample verifications (`no_adequate_with_identity`, `no_adequate_with_injective`) |
| `ReflexiveArchitecture.Universal.Summit.SummitRichReflectiveSystem` / `summit_universality` | `Universal/Summit/SummitRich.lean` | EPIC_021 naming for `BundledRich`; `∀ m, NonExhaustive (summitToRCS m)` |
| `ReflexiveArchitecture.Universal.Summit.ReflectivelySufficientSystem` / `reflectivelySufficient_nonExhaustive` | `Universal/Summit/SelfGeneration.lean` | **EPIC_031 self-generation:** fiber twist → adequate → non-exhaustive; `toAdequate` (witnesses derived from twist); `identity_not_reflectivelySufficient`; `injective_not_reflectivelySufficient` |
| `ReflexiveArchitecture.Universal.Summit.nonExhaustive_implies_fiberAutomorphism` | `Universal/Summit/FundamentalEquivalence.lean` | **EPIC_031 Gödel direction:** non-exhaustion → ∃ non-trivial fiber automorphism (classical swap construction) |
| `ReflexiveArchitecture.Universal.Summit.equiv_1_iff_3` | same | **Five-way equivalence:** `NonExhaustive ↔ ¬Injective ↔ ∃ fiber automorphism ↔ witness diversity ↔ nontrivial kernel` |
| `ReflexiveArchitecture.Universal.Summit.all_or_nothing` | same | **All-or-nothing dichotomy:** either ALL five hold or NONE do |
| `ReflexiveArchitecture.Universal.Summit.FiveWayEquivalence` / `fiveWayEquivalence` | same | Bundled package; exists unconditionally for every RCS |
| `ReflexiveArchitecture.Universal.Residual.FiberEquiv` / `fiber_blind_of_factors_compare` | `Universal/Residual/FiberResidual.lean` | EPIC_022: observables constant on fibers; `nonExhaustive_iff_exists_nontrivial_fiber` |
| `ReflexiveArchitecture.Universal.Residual.BareDetermined` / `bareDetermined_constant_on_fiber` | `Universal/Residual/ResidualStructure.lean` | RFG-T1: bare-determined predicates constant on fibers; contrapositive `not_bareDetermined_of_fiber_distinguishing` |
| `ReflexiveArchitecture.Universal.Residual.exists_separating_predicate_of_fiber_nontrivial` | same | RFG-T2: nontrivial fiber ⇒ ∃ non-bare-determined separating predicate |
| `ReflexiveArchitecture.Universal.Residual.exists_non_bareDetermined_of_nonExhaustive` | same | RFG-T2 (global): non-exhaustion ⇒ ∃ non-bare-determined predicate |
| `ReflexiveArchitecture.Universal.Residual.Refinement` / `refinedFiber_subset_fiber` | same | RFG-T4: refinement inclusion; `refinement_separates_fiber` (strict shrinkage); `refined_injective_of_total_separation` |
| `ReflexiveArchitecture.Universal.Residual.bareDetermined_and` / `_or` / `_not` / `_imp` | `Universal/Residual/ObservableAlgebra.lean` | EPIC_023 ROB-T1: Boolean closure of bare-determined predicates |
| `ReflexiveArchitecture.Universal.Residual.factors_of_constant_on_fibers` / `constant_on_fibers_iff_factors` | same | Universal factorization: `compare` is the universal bare-determined map |
| `ReflexiveArchitecture.Universal.Residual.adequate_witnesses_same_fiber` / `canonicalNontrivialFiber` | `Universal/Residual/WitnessFiber.lean` | EPIC_023 ROB-T3/T4: witnesses in same fiber; fiber properties depend only on `compare` |
| `ReflexiveArchitecture.Universal.Residual.RefinesTo` / `productRefinement_refines_left` | `Universal/Residual/RefinementOrder.lean` | EPIC_023 ROB-T2: refinement preorder; trivial/identity/product refinements |
| `ReflexiveArchitecture.Universal.Residual.IncompressibleAt` / `adequate_incompressibleAt_unit` | `Universal/Residual/Incompressibility.lean` | EPIC_023 ROB-T5/T6: bounded incompressibility; adequate systems have depth ≥ 1 |
| `ReflexiveArchitecture.Universal.Residual.ResidualKernel` / `residualKernel_nonempty_iff` | `Universal/Residual/ResidualKernel.lean` | EPIC_024 RDT-T1/T2: kernel = nontrivial fiber pairs; nonempty ↔ `NonExhaustive` |
| `ReflexiveArchitecture.Universal.Residual.UnresolvedKernel` / `unresolvedKernel_antitone` | same | RDT-T5: unresolved kernel monotone in refinement preorder; trivial leaves full kernel; identity empties it |
| `ReflexiveArchitecture.Universal.Residual.resolves_iff_separates_all_kernel_pairs` | same | RDT-T4: refinement resolves ↔ separates every kernel pair |
| `ReflexiveArchitecture.Universal.Residual.resolves_iff_unresolvedKernel_empty` | same | Resolution ↔ empty unresolved kernel |
| `ReflexiveArchitecture.Universal.Residual.adequate_kernel_nonempty` / `adequate_witnesses_in_kernel` | same | **Veil theorem:** adequate kernel nonempty; witnesses are canonical kernel pair |
| `ReflexiveArchitecture.Universal.Residual.not_bareDetermined_iff_separates_kernel` | same | **Kernel-observable duality:** non-bare-determined ↔ separates a kernel pair |
| `ReflexiveArchitecture.Universal.Residual.residualTransfer_unresolvedKernel` / `residualTransfer_incompressibleAt` | same | **Residual transfer:** same `compare` ⇒ same kernel, unresolved kernel, incompressibility |
| `ReflexiveArchitecture.Universal.Residual.KernelAt` / `residualKernel_eq_iUnion_kernelAt` | `Universal/Residual/KernelStratification.lean` | EPIC_025 KST-T1: fiberwise kernel decomposition |
| `ReflexiveArchitecture.Universal.Residual.kernelAt_nonempty_iff` | same | KST-T2: per-fiber kernel nonempty ↔ nontrivial fiber |
| `ReflexiveArchitecture.Universal.Residual.residualKernel_symmetric` | same | KST-T3: kernel symmetry |
| `ReflexiveArchitecture.Universal.Residual.ResolvedKernel` / `resolved_union_unresolved` / `resolvedKernel_monotone` | same | KST-T4: resolved/unresolved partition; resolved grows monotonically |
| `ReflexiveArchitecture.Universal.Residual.kernelAt_eq_offDiagonal_fiber` | same | Kernel at `b` = off-diagonal of fiber |

**Honesty note:** There is **no** unconditional theorem "every abstract RCS is `NonExhaustive`" (injective `compare` is a counterexample — `identityCompareRCS` in `Strong/Counterexamples.lean`). The **Fundamental Equivalence Theorem** (EPIC_031) proves that non-exhaustion, non-injectivity, witness diversity, fiber automorphism, and nontrivial kernel are **equivalent** — either all hold or none do. The **Fundamental Theorem of Residual Geometry** (EPIC_029) gives the complete geometry of the residual unconditionally for every RCS. Adequacy and reflective sufficiency tell us **when** the residual is nontrivial; the geometry tells us **what** it is.

**Specs:** EPICs 019–031 in `specs/IN-PROCESS/`.

---

## Open mathematical frontier

- **Broader inevitability:** whether there exist conditions that force witness diversity from more abstract principles (without supplying witnesses or twists as data).
- **Residual spectra:** fiber-size spectrum, entropy-like measures, persistent observables under bounded refinement.
- **Further categorical structure:** beyond the shipped `RCSCategory` layer (kernel functoriality + naturality of the fundamental package), e.g. limits, 2-cells, or functoriality across changing carriers.
- **Iterated certification:** dynamics of residual under repeated refinement.
- **Necessity theorem:** whether `RolePairDiverseCrownEligible` (IC) and `DiagonalCapable` (NEMS) are independent or follow from a single principle.

---

## Sorry / axiom policy

No `sorry` in shipped proof terms. No program-specific `axiom` beyond Mathlib.
