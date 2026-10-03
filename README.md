# TCS #1 Lean formalization (v87 manuscript synchronization)

Standalone Lean formalization accompanying:

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing_.**

## Current manuscript baseline

- internal manuscript version: **v87**
- paper repository: `growupkuriyama-hub/Papers`
- source: `01_fixed-h-cfg/main.tex`
- repository state audited: `1b26c2fbaaadc0c3268ee84533eef1da3013e0b1`
- last commit changing `main.tex`: `9377366545e48a405a6f59ea5cda3b02096166ac`
- manuscript SHA-256: `efa8d3eb321e82d7d5c72d4f4fd8d6c7077b4051ac456309349118472ddeeb96`
- v87 synchronization branch: `tcs1-v87-reverification`
- v83 remains the completed formal mathematical proof layer; v87 is the current exact manuscript synchronization target.

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

## v87 verification status

The completed v83 proof layer closes the theorem-facing mathematics. The v86 synchronization re-anchored that proof layer after the larger revision delta. The v87 source changes only proof exposition: a direct comparison found 34 theorem/proposition/lemma/corollary environments in both v86 and v87 and no changes to any of those environment contents. The v87 audit rechecks the formal theorems corresponding to the edited proof regions, including:

- explicit ordinary-thickness witnesses and reducedness for the indexed `R_n` and `R_n^-` grammars;
- literal clean-node-body occurrence recognition;
- replay admissibility of shortcut/clean body toggles;
- the residual-height difference-core theorem;
- the complete level-coded Appendix argument, culminating in the unconditional theorem `levelTree_clarkEyraud`; and
- the aggregate indexed ordinary-thickness lower-bound package, including the exponential characteristic-sample norm lower bound `5 * 2^n - 1`.

The final aggregate theorem for the ordinary-thickness construction is:

`levelCode_indexed_ordinaryThickness_lowerBound_package`

## Main files

- `LeanCfgProject/TCS1/All.lean` — integrated formalization facade
- `LeanCfgProject/TCS1/V83FullManuscriptAudit.lean` — completed v83 proof-layer audit
- `LeanCfgProject/TCS1/V86FullManuscriptAudit.lean` — completed v86 manuscript-version synchronization audit
- `LeanCfgProject/TCS1/V87FullManuscriptAudit.lean` — current v87 exact-version synchronization audit
- `FORMALIZATION_TCS1_V83.md` — v83 coverage report
- `FORMALIZATION_TCS1_V86.md` — v86 source-delta and synchronization report
- `FORMALIZATION_TCS1_V87.md` — v87 exact-source synchronization report
- `FORMALIZATION_TCS1_V79.md` — archived-baseline coverage report
- `FORMALIZATION_TCS1_V79_BOUNDARY_AUDIT.md` — explicit historical scope boundary

## CI

The TCS1 CI checks:

1. the level-coded critical path inherited from the completed v83 development;
2. `LeanCfgProject.TCS1.V86FullManuscriptAudit` and `LeanCfgProject.TCS1.V87FullManuscriptAudit`;
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
