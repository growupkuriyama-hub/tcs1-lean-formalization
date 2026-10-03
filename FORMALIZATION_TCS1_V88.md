# TCS #1 v88 Lean coverage and synchronization report

This report records the exact-version theorem-facing Lean synchronization of
the internal **v88** major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

## 1. Exact manuscript baseline

- paper repository: `growupkuriyama-hub/Papers`
- manuscript source: `01_fixed-h-cfg/main.tex`
- repository state audited: `9440e3753cbeefc88b88c92c2b16d494eb875568`
- last commit changing `main.tex`:
  `00b7d6cb5bf72208ed78b05c21fb2ba8ab88a659`
- internal manuscript version: **v88**
- manuscript SHA-256 recorded in `PAPER.yaml`:
  `ebe9db2b8677fb48112174e6f44bd8c554cee00ac45a18b500c3d051fc207d16`
- prior exact-version Lean synchronization: internal **v87**
- v87 archival tag: `tcs1-v87-formalization-2.0.0`
- v87 Zenodo DOI: `10.5281/zenodo.23114558`
- v88 verification branch: `tcs1-v88-reverification`
- v88 verification PR: **#5**

The v83 development remains the completed core proof layer.  The v86 and v87
passes synchronized that layer to their exact manuscript sources.  The v88
pass adds a new formal layer for the revised unnumbered center-marker
comparison and rechecks the later yield-typing exposition edit.

## 2. v87 -> v88 theorem-surface audit

A direct source comparison of theorem-like environments found:

- v87 theorem/proposition/lemma/corollary environments: **34**
- v88 theorem/proposition/lemma/corollary environments: **34**
- added environments: **0**
- removed environments: **0**
- changed environment contents: **0**

Thus the numbered theorem-facing surface is unchanged.

The mathematical change requiring new Lean work is the unnumbered Section
10.1 comparison

[
P=\{a^ncb^n:n\ge0\},\qquad
L_\times=PdP.
]

The endpoint (n=0) is included, so the proof must handle factors touching
the center marker and empty left/right pieces in the marked-product
decomposition.  The v88 formalization treats those endpoint cases explicitly.

A later v88 edit adds a parity-typing footnote to the target-refinement
discussion.  It changes no theorem statement.  Its mathematical point is
covered by the pre-existing yield-typed lifting and yield-invariant theorems.

## 3. New v88 Lean layer

### Endpoint-complete base language P

Module: `LeanCfgProject/TCS1/V88CenterMarkerBase.lean`

Key declarations:

- `CenterMarkerLanguage`
- `centerMarker_boundary_factor_shape`
- `centerMarker_boundary_factors_eq`
- `centerMarker_center_factors_distribution_eq`
- `centerMarker_clarkEyraud`
- `centerMarker_zeroWindow`

This verifies directly that
(P=\{a^ncb^n:n\ge0\}) is ordinarily Clark--Eyraud substitutable under the
paper's nonempty-factor convention, hence belongs to the concrete
((0,0))-fixed-window class.

### Marked product L_x = P d P

Module: `LeanCfgProject/TCS1/V88CenterMarkerProduct.lean`

Key declarations:

- `centerMarker_prefix_free`
- `centerMarker_suffix_free`
- `centerMarkerProduct_split_iff`
- `centerMarkerProduct_avoiding_d_distribution_eq`
- `centerMarkerProduct_containing_d_distribution_eq`
- `centerMarkerProduct_clarkEyraud`
- `centerMarkerProduct_zeroWindow`

The proof follows the manuscript's separator split.  If a compared factor
avoids (d), its distribution reduces to a (P)-distribution on the
appropriate side.  If it contains (d), its left and right pieces are
handled independently, with prefix/suffix freeness resolving the possible
empty endpoint pieces.

### Exact context-free grammar

Module: `LeanCfgProject/TCS1/V88CenterMarkerGrammar.lean`

The displayed grammar
(S\to XdX, X\to aXb\mid c) is represented by a finite binary grammar and
proved extensionally correct:

- `centerMarkerProductGrammar_language_eq`

Thus the context-free presentation used in the manuscript is connected to
the same extensional language used by the substitutability proof.

### Erasing image and nonlinearity

Module: `LeanCfgProject/TCS1/V88CenterMarkerNonlinear.lean`

The manuscript's erasing map fixing (a,b) and deleting (c,d,e) is
formalized by `centerMarkerErase`.  The exact image statement is proved:

- `centerMarkerProduct_erase_image_eq_doubleDelta`

The target (DeltaDelta) already has a fully internal nonlinearity theorem:

- `DeltaStar.doubleDelta_not_rawLinearInitialRepresentable`

For (L_\times) itself the v88 layer additionally proves nonlinearity
directly from the repository's verified bounded pumping theorem:

- `centerMarkerProduct_not_rawLinearInitialRepresentable`

This direct proof makes the final v88 nonlinearity conclusion fully internal;
it does not rely on postulating closure of linear languages under
homomorphism.  The erasing-image equality remains verified because it is the
specific map displayed in the manuscript.

## 4. Yield-typing exposition check

The later v88 parity example is checked against the existing formal kernel:

- `untypedDerives_lift`
- `typedDerives_yield_type`
- `typedDerives_type_unique`

These are the formal statements behind the manuscript's explanation that the
typed refinement forces the canonical yield and a reconstructed binary yield
to agree in their fixed-(h) type.

## 5. Exact-version audit

Module:

`LeanCfgProject/TCS1/V88FullManuscriptAudit.lean`

The audit imports the completed v87 checkpoint and compile-checks every new or
relevant v88 declaration above.  The integrated facade
`LeanCfgProject.TCS1.All` imports the v88 audit.

## 6. CI checkpoint

The v88 repository CI checks:

1. the inherited theorem-facing critical path;
2. `LeanCfgProject.TCS1.V88FullManuscriptAudit`;
3. the full `LeanCfgProject.TCS1.All` facade;
4. absence of `sorry` in the TCS1 Lean source tree; and
5. absence of project-level `axiom` declarations in the TCS1 Lean source tree.

A separate fast workflow builds the four v88 delta modules and the v88 audit
during iteration.

## 7. Scope and supported wording

This remains a **theorem-facing** verification.  It does not claim that every
sentence, citation, bibliographic assertion, or formatting choice in the
article is formalized.

Once the v88 branch has green full CI, the supported wording is:

> The theorem-facing mathematical content of the internal v88 revision has
> been machine-checked in Lean 4.

In particular, the corrected endpoint-complete center-marker comparison,
including substitutability, the displayed CFG, the erasing image, and the
nonlinearity conclusion, is covered by the v88 Lean layer.
