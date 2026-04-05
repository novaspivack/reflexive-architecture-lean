# reflexive-architecture-lean

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
