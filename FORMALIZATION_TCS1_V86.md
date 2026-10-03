# TCS #1 v86 Lean coverage and synchronization report

This report records the theorem-facing Lean synchronization of the internal
**v86** major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

## 1. Exact manuscript baseline

- paper repository: `growupkuriyama-hub/Papers`
- manuscript source: `01_fixed-h-cfg/main.tex`
- repository state audited: `1c1222d10cbba4317c71c27752de2efce24dff7c`
- last commit changing `main.tex`: `8a0107c619bcc84c7dcd8f36422ebdf9db2da604`
- internal manuscript version: **v86**
- manuscript SHA-256 recorded in `PAPER.yaml`:
  `4418a5c18e120f6216dec3b0c985d3c64832b2ff80075fccc2627cf21863d6d4`
- prior fully integrated Lean baseline: internal **v83**
- prior audited manuscript commit:
  `ca7b5d901cbdd1965e0897d4c9ef55e7eb7dbaf8`

The v83 theorem-facing formalization remains the mathematical proof layer.  The
purpose of the v86 pass is to audit the manuscript delta and re-anchor that
formalization to the current exact manuscript source.

## 2. v83 -> v86 theorem-surface audit

The source comparison found **no new or strengthened theorem-facing
mathematical statement** requiring a new Lean theorem.

Across theorem, proposition, lemma, and corollary environments, the substantive
mathematical surface is unchanged.  The differences are:

- wording-only tightening in several proposition/lemma statements;
- namespace/alphabet qualification such as `RS(Sigma_c)` in place of `RS`;
- removal of the redundant displayed fixed-window context/witness lemma
  `lem:window-context`, whose quantitative content is already covered by the
  Lean fixed-window bounds;
- proof elaboration in the ordinary-thickness lower-bound section; and
- a more explicit Appendix difference-core / replay-admissibility argument.

The last two items change the human-readable proof exposition, not the final
mathematical theorem surface.

## 3. Post-v83 proof edits and Lean correspondence

The manuscript edits after v83 most directly affect the following already
formalized components:

- fixed-h fibre restriction:
  `fixedHSubstitutable_inter_recognizedPreimage`;
- set-driven nested-target obstruction:
  `nestedTarget_characteristicSample_obstruction`;
- typed-thickness quantitative bounds:
  `canonicalContext_length_le_of_typedYieldBound`,
  `canonicalWitnessWords_length_le_typedThickness`,
  `canonicalWitnessFinset_sampleNorm_le_typedThickness`;
- refined fixed-window bounds:
  `concreteTypedActive_minimalContext_length_le_fixedWindow_v83`,
  `concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow_v83`;
- completed level-coded Appendix theorem:
  `levelTree_clarkEyraud`; and
- indexed ordinary-thickness lower-bound package:
  `levelCode_indexed_ordinaryThickness_lowerBound_package`.

The v86 facade compile-checks these items again through
`LeanCfgProject/TCS1/V86FullManuscriptAudit.lean`.

## 4. Scope

This is a **theorem-facing** verification, not a claim that every sentence,
bibliographic attribution, prose explanation, or formatting decision in the
paper has been formalized.

Cited literature/background results are not silently re-proved.  The Lean
development verifies the paper's own formalized mathematical claims and the
machinery needed for them.

## 5. CI checkpoint

The repository CI for the v86 synchronization checks:

1. the level-coded critical path inherited from the completed v83 development;
2. `LeanCfgProject.TCS1.V86FullManuscriptAudit`;
3. the full `LeanCfgProject.TCS1.All` facade;
4. absence of `sorry` in the TCS1 source tree; and
5. absence of project-level `axiom` declarations in the TCS1 source tree.

A green CI run on the merged v86 synchronization commit is therefore the
repository-level checkpoint for the current manuscript version.

## 6. Status wording

After the v86 synchronization PR is merged with green CI, the supported wording
is:

> The theorem-facing mathematical content of the internal v86 revision has
> been machine-checked in Lean 4.

More strongly, one may say that the v86 manuscript has a completed
**theorem-facing Lean verification**.  One should still avoid the broader
phrase "every part of the paper is fully formalized."
