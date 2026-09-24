# TCS #1 Lean formalization (v79)

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22939434.svg)](https://doi.org/10.5281/zenodo.22939434)

Standalone Lean formalization accompanying:

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing_.**

The archival release is preserved on Zenodo at DOI `10.5281/zenodo.22939434`.

This repository is intentionally restricted to the TCS #1 artifact. It excludes the unrelated JALC, MCFG, ORC, build-log, and historical project files contained in the broader research repository.

## Manuscript baseline

- Manuscript version: **v79**
- Manuscript SHA-256: `3d54aaea1c945e4b9bbdabe92a88f229096d94c93fa3045a3bfda5dfd22426d2`
- Verified theorem-facing head in the original integration repository: `c6fe72e31a305b159d93afd82c731c603125d907`
- Final pre-merge CI-guard head: `49556ddca69b6fb056d3d12880066d1d56315db8`
- Original integration PR #5 merge commit: `356bf51d3cded68a1a29d2957b656b25a693f7c6`

## Build

```bash
lake build LeanCfgProject.TCS1.All
```

or simply

```bash
lake build
```

The Lean toolchain and Mathlib dependency are pinned by `lean-toolchain` and `lake-manifest.json`.

## Main files

- `LeanCfgProject/TCS1/All.lean` — integrated formalization facade
- `LeanCfgProject/TCS1/V79FullManuscriptAudit.lean` — manuscript-order audit
- `FORMALIZATION_TCS1_V79.md` — coverage report
- `FORMALIZATION_TCS1_V79_BOUNDARY_AUDIT.md` — explicitly external boundary

## Scope

The artifact covers fixed finite-monoid substitutability, exact reconstruction, canonical finite witnesses, conservative Gold identification, executable CYK membership, materialized production tables and learner, paper-facing polynomial combinatorial bounds, fixed-window and linear-subclass results, and the Section 9 expressiveness examples.

The remaining non-internal material is limited to cited literature/background, representation conventions, explicit open problems, and low-level runtime cost semantics outside the manuscript's abstraction level.

This standalone repository contains only the TCS #1 source, reproducibility metadata, and its CI definition.
