# TCS #1 v83 Lean formalization — release 2.0.0

This release archives the completed Lean theorem-facing re-verification
corresponding to the internal **v83** major-revision manuscript:

> Takayuki Kuriyama, *Distributional Learning of Context-Free Languages under Fixed Finite-Monoid Typing*.

## Reproducibility identifiers

- manuscript repository: `growupkuriyama-hub/Papers`
- manuscript source: `01_fixed-h-cfg/main.tex`
- manuscript commit audited: `ca7b5d901cbdd1965e0897d4c9ef55e7eb7dbaf8`
- theorem-facing integration merge commit:
  `dbbfe69efea801e93a4d5ec85b6d2b8ae4e05b68`
- final pre-merge theorem/audit head:
  `b67c46ddf12f8eb2d5a611ba163aa2da479c76d0`
- post-merge main CI: run **#285**, success
- planned archival tag: `tcs1-v83-formalization-2.0.0`

## Verification status

The v83 integration verifies and CI-checks:

- the complete level-coded Appendix argument and unconditional
  `levelTree_clarkEyraud`;
- exact finite indexed semantics for `R_n` and `R_n^-`;
- reducedness of both compact grammar families;
- ordinary thickness at most `n+5`;
- linear finite-presentation encoding-size bounds;
- fixed-h substitutability of the two lower-bound target languages;
- characteristic-sample norm lower bound `5 * 2^n - 1`;
- the complete `LeanCfgProject/TCS1/All.lean` facade;
- absence of `sorry` in the TCS1 source tree; and
- absence of project-level axioms in the TCS1 source tree.

The principal aggregate theorem is:

`levelCode_indexed_ordinaryThickness_lowerBound_package`

The final manuscript-facing audit is:

`LeanCfgProject/TCS1/V83FullManuscriptAudit.lean`

See `FORMALIZATION_TCS1_V83.md` for the coverage report.

## Relation to the v79 archive

The previous archival release

`tcs1-v79-formalization-1.0.0`

and Zenodo DOI

`10.5281/zenodo.22939434`

remain immutable historical artifacts.  This v83 release is a new version and
does not rewrite the v79 archive.

## Build

```bash
lake build LeanCfgProject.TCS1.All
```

The Lean toolchain and Mathlib dependency are pinned by `lean-toolchain` and
`lake-manifest.json`.

## Zenodo

The Zenodo DOI for this v83 release should be inserted after Zenodo ingests
the GitHub release and assigns the new version DOI.
