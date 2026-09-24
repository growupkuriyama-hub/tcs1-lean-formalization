# TCS #1 v79 formalization — archival release 1.0.0

This release archives the Lean formalization corresponding to manuscript **v79** of:

> Takayuki Kuriyama, *Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing*.

## Reproducibility identifiers

- Manuscript SHA-256: `3d54aaea1c945e4b9bbdabe92a88f229096d94c93fa3045a3bfda5dfd22426d2`
- Theorem-facing verification head: `c6fe72e31a305b159d93afd82c731c603125d907`
- Pre-merge CI-guard head: `49556ddca69b6fb056d3d12880066d1d56315db8`
- PR #5 merge commit: `356bf51d3cded68a1a29d2957b656b25a693f7c6`

## Verification status

- Full `LeanCfgProject/TCS1/All.lean` CI: success (#696)
- Fast Delta facade CI: success (#365)
- `sorry` guard: success
- project-level `axiom` guard: success
- manuscript-order audits for preliminaries, Sections 3--9, front/back matter, and Appendices A--C are integrated into `TCS1.All`

## Scope

The artifact contains formalized fixed-h substitutability semantics, exact reconstruction, canonical finite witnesses, conservative Gold identification, executable CYK membership, materialized production tables and learner, paper-facing polynomial combinatorial bounds, fixed-window and linear-subclass results, and the Section 9 expressiveness examples.

Statements intentionally kept external are documented in `FORMALIZATION_TCS1_V79_BOUNDARY_AUDIT.md`.

## Build

```bash
lake build LeanCfgProject.TCS1.All
```

The archival Git tag is `tcs1-v79-formalization-1.0.0`.
