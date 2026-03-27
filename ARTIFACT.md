# reflexive-architecture-lean — artifact documentation

**Purpose:** Citation-ready summary of what this Lean 4 library is, how to build it, and where to find the full theorem map. Authoritative tables and module index: **[MANIFEST.md](MANIFEST.md)**; human-readable module glosses: **[STRATA_FORMALIZATION_MAP.md](STRATA_FORMALIZATION_MAP.md)**.

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc6 (via `lakefile.lean`)  
**Root import:** `ReflexiveArchitecture.lean`

## Build status

- **Command:** `lake build` (from this directory).
- **Last verified (2026-03-24):** 8270 jobs, **0 errors**, **0 `sorry`** in shipped proof terms under `ReflexiveArchitecture/`.
- **Lake dependencies (local):** `nems-lean`, `infinity-compression-lean` (paths in `lakefile.lean`).

**Consumer builds:** This package is a Lake dependency of other developments (e.g. `adequacy-architecture-lean`). A full consumer `lake build` replays this tree and may surface **linter** warnings; proof-statement hygiene notes for the Strata-facing `Instances` constructors and `Residual/FundamentalTheorem.lean` are recorded in **`docs/CONSUMER_BUILD_NOTE.md`** (same content may exist as `reflexive-architecture/lean/NOTE.md` only in the optional private outer monorepo—**cite this repository’s `docs/` copy** for public artifacts).

## What this artifact contains

1. **Strata (outer / middle / inner):** abstract interfaces for NEMS-style reflexive layers, APS-style realization (indexed composition), and IC-style certification; bridge `Architecture` with cross-layer coherence; non-erasure summit; `LinkedArchitecture` with coherence discharged.
2. **Universal program (EPIC_019–031):** abstract `ReflectiveCertificationSystem`, forcing and conditional universality, summit five-way equivalence, full **residual geometry** (kernel, observables, resolution, complexity), **universal forgetting** for arbitrary maps, meta-level and persistent-observable families, **`RCSCategory`** (explicit category laws + kernel functoriality).
3. **Concrete discharge interfaces:** parametric maps `FromAPS`, `FromNEMS`, `FromIC`, combined `ConcreteArchitecture` (see `ReflexiveArchitecture/Instances/`), marked `@[reducible]` where required for typeclass-friendly elaboration.

## Papers (suite-internal)

| Paper | Path |
|-------|------|
| Summit 1 — synthesis (NEMS, APS, IC, bridge) | `paper/summit-1-closure-realization/Closure_Realization_Reflective_Residue.tex` |
| Summit 2 — universal residual geometry | `paper/summit-2-geometry-of-what-maps-forget/The_Geometry_of_What_Maps_Forget.tex` |

## Proof / axiom policy

No program-specific `axiom` beyond Mathlib. No `sorry` in shipped proof terms.

## Zenodo / citation

When registering a snapshot, cite the repository root and this file together with `MANIFEST.md` for the evolving theorem list and build fingerprint.
