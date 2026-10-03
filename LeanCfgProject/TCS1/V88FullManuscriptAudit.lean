import LeanCfgProject.TCS1.V87FullManuscriptAudit
import LeanCfgProject.TCS1.V88CenterMarkerNonlinear

/-!
# TCS #1 v88: exact manuscript synchronization audit

This module is the theorem-facing Lean checkpoint for the internal v88
major-revision manuscript

**Takayuki Kuriyama, _Distributional Learning of Context-Free Languages under
Fixed Finite-Monoid Typing_.**

Relative to the exactly synchronized v87 source, the numbered
theorem/proposition/lemma/corollary surface is unchanged: both sources contain
34 such environments with identical contents.

The theorem-facing mathematical change is the unnumbered Section 10.1
comparison using the endpoint-complete center-marker language

  P = { a^n c b^n : n >= 0 }

and its marked product

  L_x = P d P.

The v88 Lean delta verifies the direct substitutability proof for P, its
prefix/suffix freeness, substitutability and (0,0)-fixed-window membership of
L_x, exact semantics of the displayed context-free grammar, the manuscript's
erasing-homomorphism image onto Double-Delta, and an unconditional internal
proof that L_x is not linear.  The latter is proved directly from the verified
bounded pumping theorem, so the conclusion does not depend on importing an
external homomorphism-closure theorem.

A later v88 prose edit adds an illustrative parity-typing footnote in the
target-refinement discussion.  Its underlying yield-typing invariant is
already formalized by typedDerives_yield_type and the canonical lifting
theorem untypedDerives_lift.

Building this module through LeanCfgProject.TCS1.All is the exact-version
theorem-facing synchronization checkpoint for v88.
-/

namespace LeanCfgProject
namespace TCS1

#check v87_full_manuscript_audited

-- v88 target-refinement exposition: yield typing and its invariant.
#check untypedDerives_lift
#check typedDerives_yield_type
#check typedDerives_type_unique

-- Endpoint-complete center-marker base P.
#check centerMarker_clarkEyraud
#check centerMarker_zeroWindow
#check centerMarker_prefix_free
#check centerMarker_suffix_free

-- Marked product L_x = P d P.
#check centerMarkerProduct_clarkEyraud
#check centerMarkerProduct_zeroWindow

-- Exact context-free presentation S -> X d X, X -> a X b | c.
#check centerMarkerProductGrammar_language_eq

-- Manuscript erasing map and internally closed nonlinearity claim.
#check centerMarkerProduct_erase_image_eq_doubleDelta
#check DeltaStar.doubleDelta_not_rawLinearInitialRepresentable
#check centerMarkerProduct_not_rawLinearInitialRepresentable

/-- Single marker for the integrated v88 exact manuscript synchronization audit. -/
theorem v88_full_manuscript_audited : True :=
  v87_full_manuscript_audited

end TCS1
end LeanCfgProject
