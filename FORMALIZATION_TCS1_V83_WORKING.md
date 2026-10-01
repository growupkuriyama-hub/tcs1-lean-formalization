# TCS #1 v83 Lean re-verification — working coverage

This file tracks the live re-verification branch for the major-revision
manuscript *Distributional Learning of Context-Free Languages under Fixed
Finite-Monoid Typing*.

## Manuscript baseline

- paper repository: `growupkuriyama-hub/Papers`
- source: `01_fixed-h-cfg/main.tex`
- checked commit: `ca7b5d901cbdd1965e0897d4c9ef55e7eb7dbaf8`
- internal paper version: v83
- Lean branch: `tcs1-v83-reverification`
- draft PR: #1

Relative to the earlier v83 checkpoint `0cf7542`, the theorem/lemma surface is
mathematically unchanged.  The main structural edit is that the proof of
level-coded-tree substitutability was moved to the Appendix.  The label of the
typed-thickness-gap remark changed from `prop:typed-thickness-gap` to
`rem:typed-thickness-gap`.  The reviewer response and locators were also
updated.

The archived v79 tag and Zenodo release remain immutable and are not being
rewritten.

## v83 delta status

### Formalized on this branch

1. **Restriction to fixed-h fibres**
   - `FixedHTypeFiberRestriction.lean`
   - theorem:
     `fixedHSubstitutable_inter_recognizedPreimage`

2. **Set-driven nested-target obstruction**
   - `SetDrivenCharacteristicObstruction.lean`
   - `IsSetDrivenCharacteristicSample`
   - `nestedTarget_characteristicSample_obstruction`

3. **Typed-thickness quantitative bounds**
   - `V83TypedThicknessWitnessBounds.lean`
   - exact shortest-path edge count
   - context bound `(Nt-1) * tau`
   - witness bound `(Nt+1) * tau`
   - four-family witness-count envelope
   - encoded characteristic-sample norm envelope

4. **Refined fixed-window constants**
   - `V83FixedWindowRefinedBounds.lean`
   - derives the current-manuscript constants from the already verified
     fixed-window typed-yield machinery

5. **Operator-independent ordinary-thickness lower-bound kernel**
   - `V83OrdinaryThicknessLowerBoundKernel.lean`
   - singleton-difference specialization
   - encoded sample-norm lower bound
   - clean-word recurrence and exponential closed form

6. **Concrete level-coded tree family**
   - `V83LevelCodedTreeSyntax.lean`
   - six-letter alphabet
   - residual-height-indexed trees
   - serialization
   - shortcut predicate
   - unique shortcut-free clean tree
   - `T_n \ T_n^- = {z_n}`
   - concrete clean-word length

7. **Concrete two-element typing**
   - `V83LevelCodedTreeTyping.lean`
   - two-element zero monoid
   - `h(w)=zeta` iff `c` occurs
   - `T_n^- = T_n ∩ h^{-1}({zeta})`
   - fixed-h package conditional on the Clark--Eyraud lemma

8. **Recursive manuscript definition**
   - `V83LevelCodedTreeLanguage.lean`
   - identifies the manuscript's recursive definition of `T_n` with the
     indexed tree-serialization model

9. **Unique parser**
   - `V83LevelCodedTreeParsing.lean`
   - executable residual-height prefix parser
   - parser/serialization left-inverse theorem
   - injectivity / unique parse

10. **Concrete lower-bound bridge**
    - `V83LevelCodedLowerBoundBridge.lean`
    - combines fixed-h class membership and the exponential sample lower bound
      once the Appendix Clark--Eyraud lemma is supplied

## Remaining theorem-facing obligations

The principal remaining mathematical obligation is the Appendix proof

> every level-coded tree language `T_n` is Clark--Eyraud substitutable.

The next formalization layer should encode legal shortcut/clean-node toggles
and prove that a literal replacement site in a serialization is a genuine
parsed residual-height node.  The unique parser above is intended as the
foundation for that argument.

After this language-theoretic lemma closes, the final ordinary-thickness
theorem still needs the displayed compact grammar families `R_n` and
`R_n^-` connected to the tree languages, with:

- exact generated languages;
- reducedness;
- polynomial / linear presentation size;
- ordinary thickness at most `n+5`.

Finally, a v83 manuscript-audit facade should replace the temporary
working-status marker.  Until those obligations close, this branch must not be
described as a complete v83 formalization.

## Additional v83 work after the initial checkpoint

The re-verification has now been pushed further into the new
ordinary-thickness lower-bound argument.

### CI-confirmed layers

The residual-height prefix parser and unique-parse layer now builds in the
integrated TCS1 facade. The direct displayed-grammar semantics and the n+5
productive-witness bounds have also passed earlier integration builds.

### Current working layers

The branch additionally contains the following theorem-facing layers; these
remain marked working until the latest full-facade CI run is green.

- V83LevelCodedBracketProjection.lean formalizes the l/r projection to the
  already verified one-bracket Dyck scanner, making the Appendix's
  bracket-matching argument explicit.
- V83LevelCodedIndexedGrammar.lean packages the displayed R_n and R_n^-
  families as actual finite IndexedMixedCFG objects.
- V83LevelCodedIndexedGrammarBridge.lean starts the semantic transport from
  the paper-facing derivation relations to generic MixedDerives, for both
  grammar families.
- V83OrdinaryThicknessDirectPackage.lean collects exact target-language
  equalities, direct n+5 thickness witnesses, linear displayed symbol counts,
  fixed-h class membership, and the exponential characteristic-sample lower
  bound, conditional only on the remaining Appendix combinatorics.

The shortcut-containing target is also identified explicitly with
T_n minus {z_n}.

### Exact remaining Appendix core

The substitutability proof has been decomposed into:

1. literal occurrence recognition: an occurrence of s_i or b_i in a valid
   serialization is the body of a genuine residual-height-i parsed node; and
2. cut locality: for u x v and u y v in T_n, all differing node-body
   replacements can be performed wholly inside the displayed factor.

The second formulation is intentionally body-level. This is slightly more
precise than saying that the whole differing node lies between the two cuts:
a cut may sit immediately after the common opening l or immediately before
the common closing r, while the replaceable body is still wholly inside the
factor. The Lean zipper/body factorization records exactly this boundary
case.

Until the occurrence-recognition/cut-locality proof and the converse indexed
grammar semantics/reducedness transport are closed, the branch remains a
working v83 re-verification rather than a completed v83 release.

