# TCS #1 v83 Lean coverage report

This report records the theorem-facing Lean re-verification of the internal
v83 major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

## 1. Baseline and audit strategy

- paper repository: `growupkuriyama-hub/Papers`
- manuscript source: `01_fixed-h-cfg/main.tex`
- manuscript commit audited: `ca7b5d901cbdd1965e0897d4c9ef55e7eb7dbaf8`
- internal manuscript version: **v83**
- Lean re-verification branch: `tcs1-v83-reverification`
- integration PR: **#1**

The archived v79 artifact remains an immutable historical baseline.  Its tag
and Zenodo release are not rewritten by this work.

The v83 audit is deliberately layered.  The existing
`V79FullManuscriptAudit.lean` remains the compile-time baseline for the
theorem surface that is unchanged from v79, while
`V83FullManuscriptAudit.lean` checks the theorem-facing delta introduced or
materially revised in v83.

Relative to the earlier v83 checkpoint `0cf7542`, the mathematical
theorem/lemma surface was unchanged.  The main structural manuscript edit was
the relocation of the level-coded substitutability proof to the Appendix,
together with the typed-thickness-gap label change and response/locator edits.

## 2. v83 theorem-facing additions and revisions

### Fixed-h fibre restriction

Formalized in:

- `FixedHTypeFiberRestriction.lean`

Primary theorem:

- `fixedHSubstitutable_inter_recognizedPreimage`

This discharges the closure step used when restricting a fixed-h
substitutable language to a recognized union of typing fibres.

### Set-driven characteristic-sample obstruction

Formalized in:

- `SetDrivenCharacteristicObstruction.lean`

Primary items:

- `IsSetDrivenCharacteristicSample`
- `nestedTarget_characteristicSample_obstruction`

The result is operator-independent at the set-driven level and is used by the
ordinary-thickness lower-bound construction.

### Typed-thickness quantitative bounds

Formalized in:

- `V83TypedThicknessWitnessBounds.lean`

Primary theorems include:

- `canonicalContext_length_le_of_typedYieldBound`
- `canonicalWitnessWords_length_le_typedThickness`
- `canonicalWitnessFinset_card_le_typedThicknessEnvelope`
- `canonicalWitnessFinset_sampleNorm_le_typedThickness`

The current bounds realize the sharpened context and witness constants used in
v83.

### Refined fixed-window constants

Formalized in:

- `V83FixedWindowRefinedBounds.lean`

Primary theorems:

- `concreteTypedActive_minimalContext_length_le_fixedWindow_v83`
- `concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow_v83`

These are derived from the already verified fixed-window typed-yield
infrastructure.

## 3. Level-coded Appendix proof

The v83 Appendix family is formalized as a residual-height indexed tree
language over the six-letter alphabet used by the manuscript.

The development includes:

- `V83LevelCodedTreeSyntax.lean`
- `V83LevelCodedTreeLanguage.lean`
- `V83LevelCodedTreeTyping.lean`
- `V83LevelCodedTreeContexts.lean`
- `V83LevelCodedTreeParsing.lean`
- `V83LevelCodedTreeToggles.lean`
- `V83LevelCodedNodeBodies.lean`
- `V83LevelCodedBracketProjection.lean`
- `V83LevelCodedDifferenceCore.lean`
- `V83LevelCodedOccurrenceKernel.lean`
- `V83LevelCodedCleanOccurrence.lean`
- `V83LevelCodedSubstitutabilityBridge.lean`

The formal proof mirrors the Appendix structure:

1. residual-height trees have an executable unique parser;
2. literal shortcut and clean-node bodies are recognized at genuine parsed
   nodes of the matching residual height;
3. two distinct parses admit a canonical serialized difference core;
4. every such core lies between any displayed common prefix/suffix cuts;
5. literal shortcut/clean-body toggles are replay-admissible inside that core;
6. the resulting replacement sequence proves Clark--Eyraud
   substitutability.

The final unconditional theorem is:

- `levelTree_clarkEyraud`

Thus the previous placeholder hypothesis for the Appendix substitutability
lemma is no longer present in the final theorem-facing package.

## 4. Concrete compact grammars R_n and R_n^-

The displayed grammar families used in the ordinary-thickness lower bound are
formalized at both paper-facing and finite indexed levels.

Paper-facing layers:

- `V83LevelCodedDisplayedGrammar.lean`
- `V83LevelCodedDisplayedThickness.lean`
- `V83OrdinaryThicknessDirectPackage.lean`

Finite indexed CFG layers:

- `V83LevelCodedIndexedGrammar.lean`
- `V83LevelCodedIndexedGrammarBridge.lean`
- `V83LevelCodedIndexedGrammarExact.lean`
- `V83LevelCodedMinusIndexedGrammarExact.lean`
- `V83LevelCodedIndexedThickness.lean`
- `V83LevelCodedIndexedReducedness.lean`
- `V83LevelCodedIndexedSize.lean`

The indexed development verifies:

- exact start language of `R_n` is `T_n`;
- exact start language of `R_n^-` is `T_n^-`;
- both finite indexed presentations are reduced;
- ordinary thickness is at most `n+5`;
- the concrete finite presentations have linear encoding scale;
- all right-hand sides have uniformly bounded length.

The theorem-facing aggregate is:

- `levelCode_indexed_ordinaryThickness_lowerBound_package`

For every `n >= 1`, this package combines exact language generation,
reducedness, the `n+5` thickness bound, a joint linear finite-presentation
size bound, fixed-h substitutability of both targets, and the exponential
characteristic-sample norm lower bound

`5 * 2^n - 1`.

## 5. Lower-bound bridge

The concrete language-theoretic lower bound is collected in:

- `V83LevelCodedLowerBoundBridge.lean`

Primary theorem:

- `levelTree_lowerBound_package`

This theorem is unconditional with respect to the Appendix combinatorics:
the Clark--Eyraud premise is supplied internally by
`levelTree_clarkEyraud`.

## 6. Final audit facade

The final v83 compile-time audit is:

- `LeanCfgProject/TCS1/V83FullManuscriptAudit.lean`

It imports the v79 full-manuscript audit as the unchanged baseline and
compile-checks the principal v83 delta theorems, including the indexed
ordinary-thickness lower-bound package.

The repository facade

- `LeanCfgProject/TCS1/All.lean`

imports the v83 audit.

## 7. CI guarantees

The TCS1 CI checks:

- the dedicated v83 level-coded critical path;
- the full `TCS1.All` facade;
- absence of `sorry` in the TCS1 source tree;
- absence of project-level axioms in the TCS1 source tree.

A green run therefore certifies both compilation of the theorem-facing
integration surface and the repository's explicit no-`sorry` /
no-project-axiom policy.

## 8. Scope boundary

As in the v79 coverage report, cited literature/background results are not
silently re-proved merely because they are mentioned by the manuscript.
Representation conventions and explicitly open questions remain classified
as such.

The v83 re-verification concerns the paper's own theorem-facing mathematical
claims and the revised Appendix/lower-bound machinery.  The historical v79
Zenodo artifact remains a separate immutable release.

## 9. Status

At the manuscript abstraction level, the v83 theorem-facing delta is
internally formalized and integrated.  In particular, the formerly open
level-coded Appendix substitutability proof and the concrete indexed
`R_n,R_n^-` exact-language/reducedness/thickness/size package are now
closed in Lean.

The authoritative integration checkpoint is
`V83FullManuscriptAudit.lean`, imported by `TCS1.All`.
