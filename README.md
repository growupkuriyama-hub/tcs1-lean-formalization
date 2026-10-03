# TCS #1 Lean formalization (v86 manuscript synchronization)

Standalone Lean formalization accompanying:

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing_.**

## Current manuscript baseline

- internal manuscript version: **v86**
- paper repository: `growupkuriyama-hub/Papers`
- source: `01_fixed-h-cfg/main.tex`
- repository state audited: `1c1222d10cbba4317c71c27752de2efce24dff7c`
- last commit changing `main.tex`: `8a0107c619bcc84c7dcd8f36422ebdf9db2da604`
- manuscript SHA-256: `4418a5c18e120f6216dec3b0c985d3c64832b2ff80075fccc2627cf21863d6d4`
- v86 synchronization branch: `tcs1-v86-reverification`
- v83 proof layer remains the completed formal mathematical baseline; v86 is the current manuscript synchronization target.

The earlier v79 artifact is preserved as an immutable archival release on
Zenodo:

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22939434.svg)](https://doi.org/10.5281/zenodo.22939434)

DOI: `10.5281/zenodo.22939434`

The v83 work does **not** rewrite or move that historical release.

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

## v86 verification status

The completed v83 proof layer already closes the revised theorem-facing mathematics. The v86 synchronization audit confirms that the current manuscript adds no new theorem-facing mathematical statement and rechecks the principal formalized claims, including:

- restriction of fixed-h substitutability to recognized unions of h-fibres;
- the generic set-driven nested-target characteristic-sample obstruction;
- sharpened typed-thickness context/witness/sample-norm bounds;
- refined fixed-window constants;
- the complete level-coded Appendix argument, culminating in the
  unconditional theorem `levelTree_clarkEyraud`;
- concrete finite indexed CFG presentations of `R_n` and `R_n^-`;
- exact generated languages `T_n` and `T_n^-`;
- reducedness of both indexed grammar families;
- ordinary thickness at most `n+5`;
- linear finite-presentation encoding-size bounds; and
- the exponential characteristic-sample norm lower bound
  `5 * 2^n - 1`.

The final aggregate theorem for the ordinary-thickness construction is:

`levelCode_indexed_ordinaryThickness_lowerBound_package`

## Main files

- `LeanCfgProject/TCS1/All.lean` — integrated formalization facade
- `LeanCfgProject/TCS1/V83FullManuscriptAudit.lean` — completed v83 proof-layer audit
- `LeanCfgProject/TCS1/V86FullManuscriptAudit.lean` — current v86 manuscript-version synchronization audit
- `FORMALIZATION_TCS1_V83.md` — v83 coverage report
- `FORMALIZATION_TCS1_V86.md` — v86 source-delta and synchronization report
- `FORMALIZATION_TCS1_V79.md` — archived-baseline coverage report
- `FORMALIZATION_TCS1_V79_BOUNDARY_AUDIT.md` — explicit historical scope boundary

## CI

The TCS1 CI checks:

1. the level-coded critical path inherited from the completed v83 development;
2. `LeanCfgProject.TCS1.V86FullManuscriptAudit`;
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
