# reflexive-architecture-lean Artifact Documentation

**Version:** v1.0.0  
**Lean:** leanprover/lean4:v4.29.0-rc6  
**Mathlib:** v4.29.0-rc6  
**Build:** 8218 jobs, 0 errors, **0 sorry in proof terms**, **0 custom axioms**  
**Lake deps:** `nems-lean` (local), `infinity-compression-lean` (local)  
**Commit:** `(see git log)` — latest — see `MANIFEST.md` for full theorem index and `STRATA_FORMALIZATION_MAP.md` for module tree.

## What This Artifact Proves

This Lean 4 library formalizes the **Strata program**: a machine-checked synthesis of the NEMS (No External Model Selection), APS (Abstract Programming Systems), and Infinity Compression research lines into a single abstract architecture class with proved bridge theorems, a non-erasure principle, and a biconditional connecting the two main strata.

### Universal layer (EPIC_019 Phase I)

Under `ReflexiveArchitecture.Universal`, the library also provides a **domain-agnostic** certification/realization interface (`ReflectiveCertificationSystem`) with fiber lemmas (injectivity vs. subsingleton fibers), minimal/strong/non-exhaustion predicates, and section-based surjectivity — intended as the floor for later extraction theorems. This layer does not replace the NEMS/APS/IC strata; it factors generic comparison/fiber facts used in multiple domains.

### Abstract architecture (Milestones 1–3)

The library defines an abstract class `Architecture` with three independent layer interfaces (outer/NEMS, middle/APS, inner/IC) and proves:

- **Layered Architecture Theorem** (`Bridge.layered_architecture_theorem`): Under barrier, tracking+gluing, and canonical certification with an adequate route, all three structural conclusions hold jointly.
- **Stratified Non-Collapse** (`Bridge.stratified_noncollapse`): No architecture collapses all three strata simultaneously.
- **Bridge P0** (`Bridge.canonical_bare_does_not_pin_enriched_irreducibility`): Bare canonicity does not determine enriched irreducibility (model-theoretic separation).
- **Bridge P1** (`Bridge.glue_route_coherent_canonical_implies_composition_and_strict_refinement`): Glue-route coherence implies middle composition and inner strict refinement.
- **Bridge P2** (`Bridge.inner_enriched_gap_independent_of_outer_theory_extent`): Inner enriched gap is independent of outer theory extent.
- **Non-Erasure Principle** (`Bridge.nonerasure_principle`): Under coherence axioms and a remainder witness, enriched irreducibility holds.
- **Unified Non-Erasure Law** (`Bridge.unified_nonerasure_law`): Under universal totality, `EnrichedIrreducibility ↔ ∃ T, SemanticRemainder T`.
- **LinkedArchitecture** (`Bridge.LinkedArchitecture`): Subclass where both coherence axioms are proved theorems; biconditional holds unconditionally without totality hypothesis.

### Concrete discharge (Milestone 4)

- **CrossCorpusInstance** (`Instances.crossCorpusLinkedArchitecture`): Concrete `LinkedArchitecture` where the cross-corpus Iff holds by `Iff.rfl`.
- **ConcreteFromNEMS** (`Instances.concreteNEMSReflexiveLayer`): `ReflexiveLayer Framework` built directly from `nems-lean`; NEMS record-truth undecidability (`diagonal_barrier_rt`) is the concrete outer semantic remainder (`concreteNEMS_has_semantic_remainder`).
- **ConcreteFromIC** (`Instances.concreteICCertificationLayer`): `CertificationLayer (CompressionArchitecture BD n)` built from `infinity-compression-lean`; enriched irreducibility from T-C+.7 (`concreteIC_enrichedIrrHolds`).

### Direct cross-corpus theorems

- **Joint theorem** (`Bridge.nems_spine_both_strata`): On the NEMS spine, the outer NEMS stratum (record-truth undecidability from `diagonal_barrier_rt`) and the inner IC stratum (enriched irreducibility from T-C+.6) hold simultaneously, sourced directly from the two repositories.
- **Biconditional** (`Bridge.ic_enriched_iff_nems_remainder`): IC enriched irreducibility ↔ NEMS semantic remainder on the NEMS spine, via `SpinePluralityProp` as the common structural cause. Two nontrivial implications: T-C+.7 (IC side, from `infinity-compression-lean`) and `diagonal_barrier_rt` (NEMS side, from `nems-lean`).

### Open frontier (necessity of the structural hypotheses)

The universal non-erasure family is stated under **`RolePairDiverseCrownEligible`** and **`DiagonalCapable`** (with a single-hypothesis form after instantiating a diagonal-capable framework). The remaining mathematical frontier is **not** a missing proof obligation inside those theorems: it is the question whether those two hypotheses are **logically linked** (one forces the other, or both follow from a common principle) or are **independent** conditions that happen to align on concrete instances such as the NEMS spine. A resolution would simplify how the law is stated to external audiences and connects to the broader universalization program in EPIC_019.

## Proof Status

**Zero sorry in all shipped proof terms.** Zero program-specific axioms beyond Mathlib.

The Milestone 3 coherence axioms (`outer_remainder_forces_inner_enrichment`, `outer_exhaustion_kills_inner_enrichment`) are explicit fields of the `Architecture` class. In `LinkedArchitecture` they are proved as theorems via the `enriched_iff_remainder` field. In `linkedArchitectureFromRemainder` they hold definitionally.

## Reproduction

```bash
# Requires nems-lean and infinity-compression-lean as siblings
cd reflexive-architecture-lean
lake update
lake exe cache get
lake build
```

All builds verified clean on `leanprover/lean4:v4.29.0-rc6` with Mathlib `v4.29.0-rc6`.

## Key theorem summary

| Theorem | Location | Status |
|---------|----------|--------|
| `layered_architecture_theorem` | `Bridge/LayeredTheorem.lean` | ✓ 0 sorry |
| `stratified_noncollapse` | `Bridge/StratifiedNonCollapse.lean` | ✓ 0 sorry |
| `canonical_bare_does_not_pin_enriched_irreducibility` | `Bridge/BareCanonicityNotReflectiveFinality.lean` | ✓ 0 sorry |
| `glue_route_coherent_canonical_implies_composition_and_strict_refinement` | `Bridge/GluingRouteCoherence.lean` | ✓ 0 sorry |
| `inner_enriched_gap_independent_of_outer_theory_extent` | `Bridge/SemanticRemainderToEnrichedGap.lean` | ✓ 0 sorry |
| `nonerasure_principle` | `Bridge/NonErasurePrinciple.lean` | ✓ 0 sorry |
| `unified_nonerasure_law` | `Bridge/NonErasurePrinciple.lean` | ✓ 0 sorry |
| `linked_nonerasure_unconditional` | `Bridge/LinkedArchitecture.lean` | ✓ 0 sorry |
| `crossCorpus_enriched_iff_remainder` | `Instances/CrossCorpusInstance.lean` | ✓ 0 sorry |
| `concreteNEMS_has_semantic_remainder` | `Instances/ConcreteFromNEMS.lean` | ✓ 0 sorry |
| `concreteIC_enrichedIrrHolds` | `Instances/ConcreteFromIC.lean` | ✓ 0 sorry |
| `nems_spine_both_strata` | `Bridge/DirectCrossCorpusBridge.lean` | ✓ 0 sorry |
| `ic_enriched_iff_nems_remainder` | `Bridge/SharedReflexiveArchitecture.lean` | ✓ 0 sorry |
| `ic_enriched_iff_nems_remainder_unconditional` | `Bridge/SharedReflexiveArchitecture.lean` | ✓ 0 sorry |
| `universal_nonerasure_law` | `Bridge/UniversalNonErasureLaw.lean` | ✓ 0 sorry |
| `universal_nonerasure_law_library` | `Bridge/UniversalNonErasureLaw.lean` | ✓ 0 sorry |
| `nems_spine_from_universal` | `Bridge/UniversalNonErasureLaw.lean` | ✓ 0 sorry |

For the complete theorem table see **[MANIFEST.md](MANIFEST.md)**.
For module roles and informal glosses see **[STRATA_FORMALIZATION_MAP.md](STRATA_FORMALIZATION_MAP.md)**.
