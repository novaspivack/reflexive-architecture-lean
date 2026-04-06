# reflexive-architecture-lean


## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Reflexive Architecture / Strata (§B5b): closure, realization, and reflective residue (Summit 1); the geometry of what maps forget (Summit 2).

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#b5b-reflexive-architecture-summit1) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

All results are machine-checked in Lean 4 with a zero-sorry policy on proof targets.
See [MANIFEST.md](MANIFEST.md) for the sorry audit (if present).

---

Lean 4 + Mathlib library for **Strata** (Reflexive Architecture synthesis): abstract outer / middle / inner interfaces, `layered_architecture_theorem`, and `stratified_noncollapse`.

## Build

```bash
lake update
lake exe cache get
lake build
```

**Toolchain:** `leanprover/lean4:v4.29.0-rc3` (matches Mathlib pin in `lakefile.lean`).

## Root import

`ReflexiveArchitecture.lean` imports the full public surface (Outer, Middle, Inner, Bridge, Toy instance).

## Papers

See `paper/build_papers.sh` and `paper/Closure_Realization_Reflective_Residue.tex`.

## Manifest

See `MANIFEST.md` for module map and theorem entry points.
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429250
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
