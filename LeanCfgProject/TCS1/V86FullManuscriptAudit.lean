import LeanCfgProject.TCS1.V83FullManuscriptAudit

/-!
# TCS #1 v86: manuscript-version synchronization audit

This module is the theorem-facing Lean checkpoint for the internal v86
major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

The fully formalized mathematical surface is inherited from the completed v83
re-verification.  A source-level comparison of the v83 audited manuscript with
v86 found no new theorem-facing mathematical claim requiring a new Lean proof:
the intervening edits strengthen or reorganize paper proofs, tighten
terminology and citations, remove one redundant displayed lemma, and make the
level-coded Appendix argument more explicit.

Accordingly, this v86 facade rechecks the principal Lean theorems whose paper
proofs were edited after v83.  In particular it checks the fixed-h fibre
restriction, the set-driven obstruction, quantitative typed-thickness and
fixed-window bounds, the unconditional level-coded substitutability theorem,
and the indexed ordinary-thickness lower-bound package.

Building this module through `LeanCfgProject.TCS1.All`, together with the CI
placeholder-proof and no-project-`axiom` gates, is the repository checkpoint
for v86 theorem-facing synchronization.
-/

namespace LeanCfgProject
namespace TCS1

#check v83_full_manuscript_audited

#check fixedHSubstitutable_inter_recognizedPreimage
#check nestedTarget_characteristicSample_obstruction

#check canonicalContext_length_le_of_typedYieldBound
#check canonicalWitnessWords_length_le_typedThickness
#check canonicalWitnessFinset_sampleNorm_le_typedThickness

#check concreteTypedActive_minimalContext_length_le_fixedWindow_v83
#check concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow_v83

#check levelTree_clarkEyraud
#check levelCode_indexed_ordinaryThickness_lowerBound_package

/-- Single marker for the integrated v86 manuscript-version synchronization audit. -/
theorem v86_full_manuscript_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
