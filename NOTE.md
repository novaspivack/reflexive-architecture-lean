# Reflexive Architecture Lean — cleanup / linter follow-up

**Public canonical copy:** `reflexive-architecture-lean/docs/CONSUMER_BUILD_NOTE.md` (same document; use that path for arXiv/Zenodo supplements when only the Lean repository is published).

**For:** another agent working in this repository (`reflexive-architecture-lean`).  
**Context:** This package is a **Lake dependency** of `adequacy-architecture` (sibling path `../../reflexive-architecture/reflexive-architecture-lean`). A full `lake build` from that consumer replays this repo and surfaces **linter warnings** here.

**Goal:** Clean warnings without changing mathematical content. After edits, run **`lake build`** from **this directory** and confirm **zero new errors**; ideally **no** (or strictly fewer) warnings on the files below.

---

## 1. `ReflexiveArchitecture/Universal/Residual/FundamentalTheorem.lean`

### ~L62 — `exhaustive_iff_kernel_empty` (backward direction)

- **Warning:** linter suggests a different `intro` pattern (e.g. combine `intro hempty` with `intro x y heq`).
- **Action:** Refactor the second branch of the `constructor` proof so the intros match the linter’s suggestion **or** an equivalent proof that satisfies the linter. Keep the statement and proof idea the same (`ResidualKernel S = ∅` → `Function.Injective S.compare`).

### ~L241 — `fundamentalResidualPackage` field `fiber_complete`

- **Warning:** unused variables `b`, `x`, `y` in `fun b x y hx hy hne => kernelAt_complete S hx hy hne`.
- **Action:** Either pass implicits explicitly (e.g. `(b := b)` to `@kernelAt_complete` if needed), use underscores only where correct for dependent types, or rewrite the lambda so bound variables are not flagged unused while preserving the same `∀ b x y, …` quantification. Do **not** weaken the field type.

---

## 2. Class-instance definitions — `@[reducible]` (or `@[implicit_reducible]`)

Lean warns when a `def` returning a **structure/class** type should be reducible for typeclass resolution.

| File | Definitions to annotate |
|------|---------------------------|
| `ReflexiveArchitecture/Instances/FromAPS.lean` | `apsRealizationLayer`, `apsRealizationLayerFromIff` |
| `ReflexiveArchitecture/Instances/FromNEMS.lean` | `nemsReflexiveLayer` |
| `ReflexiveArchitecture/Instances/FromIC.lean` | `icCertificationLayer` |

- **Action:** Add `@[reducible]` (preferred unless the project standard says otherwise) immediately above each `def`, then rebuild. If something breaks, try `@[implicit_reducible]` per Lean’s suggestion.

---

## 3. Verification

```bash
cd /path/to/reflexive-architecture-lean
lake build
```

Optional: build the consumer to ensure no regressions:

```bash
cd /path/to/Adequacy_Architecture/adequacy-architecture-lean
lake build
```

---

## 4. Out of scope (unless you choose to expand)

- Warnings only appearing inside **Mathlib** or other dependencies — ignore unless policy requires otherwise.
- Changing theorem statements or API names — **not** required for this cleanup.

---

**Last noted:** 2026-03-24 — warnings observed when building `adequacy-architecture-lean` against this tree.

**Status (2026-03-24):** Items in §§1–2 were applied in `reflexive-architecture-lean` (`exhaustive_iff_kernel_empty` intro cleanup; `fiber_complete` via explicit implicit args to `kernelAt_complete`; `@[reducible]` on `apsRealizationLayer`, `apsRealizationLayerFromIff`, `nemsReflexiveLayer`, `icCertificationLayer`). `@[reducible]` was also added on `concreteArchitecture` (same class-instance linter). `lake build` in `reflexive-architecture-lean` succeeds with zero errors.

**Documentation sync:** `reflexive-architecture-lean` **`MANIFEST.md`**, **`ARTIFACT.md`** (new), **`STRATA_FORMALIZATION_MAP.md`**, and suite papers’ code-availability blocks were updated to match this hygiene pass.
