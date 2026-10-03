# TCS #1 Lean formalization (v88 manuscript synchronization)

Standalone Lean formalization accompanying:

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing_.**

## Current manuscript baseline

- internal manuscript version: **v88**
- paper repository: `growupkuriyama-hub/Papers`
- source: `01_fixed-h-cfg/main.tex`
- repository state audited: `9440e3753cbeefc88b88c92c2b16d494eb875568`
- last commit changing `main.tex`: `00b7d6cb5bf72208ed78b05c21fb2ba8ab88a659`
- manuscript SHA-256: `ebe9db2b8677fb48112174e6f44bd8c554cee00ac45a18b500c3d051fc207d16`
- v88 synchronization branch: `tcs1-v88-reverification`
- v83 remains the completed core proof layer; v88 is the current exact manuscript synchronization target.

The preceding v87 theorem-facing verification is archived on Zenodo as
`tcs1-v87-formalization-2.0.0`:

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23114558.svg)](https://doi.org/10.5281/zenodo.23114558)

DOI: `10.5281/zenodo.23114558`

The earlier v79 artifact remains preserved as the immutable historical release
`tcs1-v79-formalization-1.0.0` (DOI:
`10.5281/zenodo.22939434`).

## Build

```bash
lake build LeanCfgProject.TCS1.All
```

or

```bash
lake build
```

The Lean toolchain and Mathlib dependency are pinned by `lean-toolchain`
and `lake-manifest.json`.

## v88 verification status

The v88 numbered theorem/proposition/lemma/corollary surface is unchanged from
v87 (34 environments in each source, with identical contents).  The new
theorem-facing work is the corrected unnumbered Section 10.1 center-marker
comparison.  The v88 layer now verifies:

- ordinary substitutability of the endpoint-complete language
  `P = {a^n c b^n : n >= 0}` and its `(0,0)` fixed-window membership;
- prefix- and suffix-freeness of `P`;
- ordinary substitutability and `(0,0)` membership of
  `L_x = P d P`, including the endpoint cases;
- exact semantics of the displayed grammar `S -> X d X`,
  `X -> a X b | c`;
- the erasing-homomorphism image of `L_x` onto Double-Delta; and
- an unconditional internal proof that `L_x` is not raw-linearly
  representable, using the verified bounded pumping theorem.

The later v88 parity-typing footnote is also anchored to the existing
yield-typed lifting and yield-invariant theorems.

The exact-version checkpoint is:

`v88_full_manuscript_audited`

## Main files

- `LeanCfgProject/TCS1/All.lean` — integrated formalization facade
- `LeanCfgProject/TCS1/V83FullManuscriptAudit.lean` — completed v83 proof-layer audit
- `LeanCfgProject/TCS1/V86FullManuscriptAudit.lean` — completed v86 manuscript-version synchronization audit
- `LeanCfgProject/TCS1/V87FullManuscriptAudit.lean` — completed v87 exact-version synchronization audit
- `LeanCfgProject/TCS1/V88CenterMarkerBase.lean` — endpoint-complete base language
- `LeanCfgProject/TCS1/V88CenterMarkerProduct.lean` — marked-product substitutability
- `LeanCfgProject/TCS1/V88CenterMarkerGrammar.lean` — exact displayed CFG semantics
- `LeanCfgProject/TCS1/V88CenterMarkerNonlinear.lean` — erasing image and internal nonlinearity proof
- `LeanCfgProject/TCS1/V88FullManuscriptAudit.lean` — current v88 exact-version synchronization audit
- `FORMALIZATION_TCS1_V83.md` — v83 coverage report
- `FORMALIZATION_TCS1_V86.md` — v86 source-delta and synchronization report
- `FORMALIZATION_TCS1_V87.md` — v87 exact-source synchronization report
- `FORMALIZATION_TCS1_V88.md` — v88 exact-source synchronization report
- `FORMALIZATION_TCS1_V79.md` — archived-baseline coverage report
- `FORMALIZATION_TCS1_V79_BOUNDARY_AUDIT.md` — explicit historical scope boundary

## CI

The TCS1 CI checks:

1. the level-coded critical path inherited from the completed v83 development;
2. `LeanCfgProject.TCS1.V86FullManuscriptAudit`, `LeanCfgProject.TCS1.V87FullManuscriptAudit`, and `LeanCfgProject.TCS1.V88FullManuscriptAudit`;
3. the full `LeanCfgProject.TCS1.All` facade;
4. that the TCS1 source contains no `sorry`; and
5. that it contains no project-level axioms.

A green CI run is therefore the repository-level verification checkpoint for
the current branch.

## Scope

This repository is intentionally restricted to the TCS #1 artifact.  It
contains the manuscript-facing Lean development, reproducibility metadata,
coverage reports, and CI definition.

Cited literature/background, representation conventions, and explicitly open
problems are kept separate from internally proved manuscript claims rather
than being silently promoted to Lean theorems.
