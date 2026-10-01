import LeanCfgProject.TCS1.V79FullManuscriptAudit
import LeanCfgProject.TCS1.FixedHTypeFiberRestriction
import LeanCfgProject.TCS1.SetDrivenCharacteristicObstruction
import LeanCfgProject.TCS1.V83TypedThicknessWitnessBounds
import LeanCfgProject.TCS1.V83FixedWindowRefinedBounds
import LeanCfgProject.TCS1.V83LevelCodedSubstitutabilityBridge
import LeanCfgProject.TCS1.V83OrdinaryThicknessIndexedPackage

/-!
# TCS #1 v83: full manuscript audit facade

This module records the theorem-facing delta from the archived v79 artifact to
the current internal v83 major-revision manuscript.

The v79 audit remains the baseline for the unchanged theorem surface.  The
additional v83 checks below cover the strengthened/reworked claims introduced
or materially revised in the current manuscript:

* restriction of fixed-h substitutability to recognized unions of h-fibres;
* the set-driven nested-target characteristic-sample obstruction;
* sharpened typed-thickness context/witness/sample-norm bounds;
* refined fixed-window constants;
* the Appendix level-coded-tree Clark--Eyraud substitutability proof; and
* the concrete indexed R_n/R_n^- ordinary-thickness lower-bound package,
  including exact languages, reducedness, n+5 thickness, linear finite
  presentation size, fixed-h membership, and the exponential sample lower
  bound.

Building this module together with the repository CI therefore gives one
compile-time checkpoint for the current v83 theorem-facing re-verification.
-/

namespace LeanCfgProject
namespace TCS1

#check v79_full_manuscript_audited

#check fixedHSubstitutable_inter_recognizedPreimage
#check nestedTarget_characteristicSample_obstruction

#check canonicalContext_length_le_of_typedYieldBound
#check canonicalWitnessWords_length_le_typedThickness
#check canonicalWitnessFinset_sampleNorm_le_typedThickness

#check concreteTypedActive_minimalContext_length_le_fixedWindow_v83
#check concreteTypedActive_minimalCanonicalWitnessWords_length_le_fixedWindow_v83

#check levelTree_clarkEyraud
#check levelCode_indexed_ordinaryThickness_lowerBound_package

/-- Single marker for the integrated v83 manuscript audit. -/
theorem v83_full_manuscript_audited : True :=
  True.intro

end TCS1
end LeanCfgProject
