# TCS #1 v88 Lean formalization — release notes

Release tag: `tcs1-v88-formalization-3.0.0`

This release freezes the theorem-facing Lean 4 verification synchronized to
the internal **v88** manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

## Exact manuscript anchor

- paper repository: `growupkuriyama-hub/Papers`
- English source of truth: `01_fixed-h-cfg/main.tex`
- paper repository state checked before archival:
  `11ca0908b6f4d52af7a4150295f37c333fdba9bc`
- last commit changing the English source:
  `00b7d6cb5bf72208ed78b05c21fb2ba8ab88a659`
- English manuscript SHA-256:
  `ebe9db2b8677fb48112174e6f44bd8c554cee00ac45a18b500c3d051fc207d16`

The paper repository commits after the original v88 audit modified only
metadata/README material and the Japanese reference translation.  The English
source `main.tex` did not change, so the theorem-facing Lean synchronization
remained current.

## Verification anchor

- v88 verification PR: **#5**
- verification merge on `main`:
  `bb0f8f5feacda2d616b6aebfca272a7a206e8351`
- full `main` CI after that merge: **TCS1 Lean CI #368 — success**
- exact-version marker:
  `LeanCfgProject.TCS1.v88_full_manuscript_audited`

The full CI builds the theorem-facing critical path and
`LeanCfgProject.TCS1.All`, and rejects both `sorry` and project-level
`axiom` declarations in the TCS1 source tree.

## New v88 formalization

The v88 layer verifies the corrected endpoint-complete Section 10.1
center-marker comparison:

- `P = {a^n c b^n : n >= 0}` is ordinarily Clark--Eyraud substitutable and
  belongs to the `(0,0)` fixed-window class;
- `P` is prefix- and suffix-free;
- `L_x = P d P` is ordinarily substitutable and belongs to the `(0,0)`
  fixed-window class, including endpoint cases;
- the displayed grammar `S -> X d X`, `X -> a X b | c` has exactly
  `L_x` as its start language;
- the manuscript erasing map sends `L_x` exactly onto Double-Delta; and
- `L_x` is internally proved non-linear via the verified bounded pumping
  theorem.

The later v88 parity-typing exposition is anchored to the existing
yield-typing lifting and uniqueness theorems.

## Archive workflow

This release is intended as the GitHub source snapshot for the next Zenodo
version.  After Zenodo mints the new version DOI, record that DOI in the paper
repository metadata and, if desired, add it to this repository's README in a
small post-release metadata commit.  The release tag itself should not move.
