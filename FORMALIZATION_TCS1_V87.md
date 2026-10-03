# TCS #1 v87 Lean coverage and synchronization report

This report records the exact-version theorem-facing Lean synchronization of
the internal **v87** major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

## 1. Exact manuscript baseline

- paper repository: `growupkuriyama-hub/Papers`
- manuscript source: `01_fixed-h-cfg/main.tex`
- repository state audited: `5369c43feecfbfb23e4076356e7a0e264306b928`
- last commit changing `main.tex`:
  `43b1dd71ff57000dacbf303ca1a3c48d541fd5b4`
- internal manuscript version: **v87**
- manuscript SHA-256 recorded in `PAPER.yaml`:
  `991d0ea355a130abe60d2b2204a287d5e6b6b7522f5f2dce87ca6fa3a6ba358f`
- prior exact-version Lean synchronization: internal **v86**
- v86 manuscript source commit:
  `8a0107c619bcc84c7dcd8f36422ebdf9db2da604`
- v86 Lean integration commit:
  `46d234382057ebd07d1792ed47858c9f43ee80d9`
- current v87 Zenodo release: `tcs1-v87-formalization-2.0.0`
- current v87 Zenodo DOI: `10.5281/zenodo.23114558`

The v83 development remains the completed mathematical proof layer.  The v86
pass synchronized that proof layer to the then-current manuscript; the v87
pass below re-anchors it to the current exact source after Lean-guided proof
exposition edits.

## 2. v86 -> v87 theorem-surface audit

A direct source comparison of theorem-like environments found:

- v86 theorem/proposition/lemma/corollary environments: **34**
- v87 theorem/proposition/lemma/corollary environments: **34**
- added environments: **0**
- removed environments: **0**
- changed environment contents: **0**

Thus v87 introduces **no new theorem-facing statement, no strengthened
statement, and no changed bound**.

The v87 manuscript edits are confined to human-readable proof exposition:

1. the proof of the ordinary-thickness bounds for the displayed grammars now
   gives explicit terminal witnesses for `Z_i`, `A_i`, and `A_i^-`;
2. the Appendix clean-body occurrence argument now spells out the immediate
   parent-frame reasoning showing that a literal
   `b_i = z_{i-1} z_{i-1}` occurrence is a genuine clean node body; and
3. the Appendix difference-core induction is reorganized by residual height
   and root constructor, matching the formal case split.

These are proof-explication changes only.  A later v87 Data availability edit records the public Zenodo/GitHub artifact and likewise changes no theorem-facing statement.

## 3. Lean correspondence for the v87 edits

The exact edited proof regions correspond to already completed Lean theorems:

### Ordinary-thickness witnesses and reducedness

- `levelCodeRIndexed_thickness_atMost`
- `levelCodeRMinusIndexed_thickness_atMost`
- `levelCodeRIndexed_reduced`
- `levelCodeRMinusIndexed_reduced`

### Clean-body occurrence recognition and replay admissibility

- `levelCleanBodyRecognition_proved`
- `levelBodyToggleAdmissible_levelTree`

### Difference-core induction and substitutability

- `levelTree_difference_core`
- `levelBodyToggleCutLocality_levelTree`
- `levelTree_clarkEyraud`

### Aggregate lower-bound theorem-facing package

- `levelCode_indexed_ordinaryThickness_lowerBound_package`

The module
`LeanCfgProject/TCS1/V87FullManuscriptAudit.lean`
compile-checks these declarations and imports the completed v86 synchronization
audit.

## 4. Scope

This is a **theorem-facing** verification.  It does not claim that every
sentence, citation, exposition choice, or formatting decision in the paper is
formalized.

The manuscript proofs remain self-contained.  Lean is used here as a
reproducibility and verification artifact for the mathematical claims and the
proof machinery supporting them.

## 5. CI checkpoint

The v87 repository CI checks:

1. the level-coded critical path inherited from the completed v83 development;
2. `LeanCfgProject.TCS1.V87FullManuscriptAudit`;
3. the full `LeanCfgProject.TCS1.All` facade;
4. absence of placeholder proofs in the TCS1 Lean source tree; and
5. absence of project-level axiom declarations in the TCS1 Lean source tree.

A green CI run on the merged v87 synchronization commit is the repository-level
checkpoint for this exact manuscript version.

## 6. Supported wording

Once the v87 synchronization is merged with green CI, the supported wording is:

> The theorem-facing mathematical content of the internal v87 revision has
> been machine-checked in Lean 4.

Equivalently, the v87 manuscript has a completed **theorem-facing Lean
verification**.  This should not be broadened into a claim that every part of
the article has been fully formalized.
