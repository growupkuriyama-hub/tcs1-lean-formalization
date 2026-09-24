import LeanCfgProject.TCS1.LinearRegularIntersection
import LeanCfgProject.TCS1.FixedWindowExactEquivalence
import LeanCfgProject.TCS1.FixedWindowCounterexampleCriterion
import LeanCfgProject.TCS1.FixedHFiniteObstructions
import LeanCfgProject.TCS1.FiniteMonoidObstructionKernel
import LeanCfgProject.TCS1.UncappedCounterObstruction
import LeanCfgProject.TCS1.CappedCounterFixedWindow
import LeanCfgProject.TCS1.CappedCounterFiniteState
import LeanCfgProject.TCS1.CappedCounterPaperWitness
import LeanCfgProject.TCS1.CappedCounterProposition
import LeanCfgProject.TCS1.DeltaStarFixedWindow
import LeanCfgProject.TCS1.DeltaStarTyping
import LeanCfgProject.TCS1.DeltaStarFixedH
import LeanCfgProject.TCS1.DeltaStarFixedHSubstitutability
import LeanCfgProject.TCS1.DeltaStarNonregular
import LeanCfgProject.TCS1.DeltaStarDisplayedGrammar
import LeanCfgProject.TCS1.DeltaStarBinaryGrammar
import LeanCfgProject.TCS1.DeltaStarNonlinearityBridge
import LeanCfgProject.TCS1.DeltaStarFourBlockDFA
import LeanCfgProject.TCS1.DeltaStarNonlinearityReduction
import LeanCfgProject.TCS1.DeltaStarProposition
import LeanCfgProject.TCS1.DyckOneBracketKernel
import LeanCfgProject.TCS1.DyckOneBracketGrammar
import LeanCfgProject.TCS1.LukasiewiczBoundary
import LeanCfgProject.TCS1.LukasiewiczGrammar
import LeanCfgProject.TCS1.FixedHRightQuotient
import LeanCfgProject.TCS1.LinearSeparatorExample
import LeanCfgProject.TCS1.LinearSeparatorTyping
import LeanCfgProject.TCS1.LinearSeparatorDistribution
import LeanCfgProject.TCS1.LinearSeparatorPowerContexts
import LeanCfgProject.TCS1.LinearSeparatorFactorSlices
import LeanCfgProject.TCS1.LinearSeparatorContextShape
import LeanCfgProject.TCS1.LinearSeparatorBoundaryFactors
import LeanCfgProject.TCS1.LinearSeparatorBalance
import LeanCfgProject.TCS1.LinearSeparatorFixedH
import LeanCfgProject.TCS1.LinearSeparatorProposition86
import LeanCfgProject.TCS1.LinearSeparatorDisplayedGrammar
import LeanCfgProject.TCS1.LinearSeparatorNonregular
import LeanCfgProject.TCS1.LinearSeparatorPreparedGrammar
import LeanCfgProject.TCS1.ClarkCongruentialKernel
import LeanCfgProject.TCS1.ClarkCongruentialPackaging
import LeanCfgProject.TCS1.ClarkCongruentialIndexedFacade
import LeanCfgProject.TCS1.ClarkCongruentialEndpoints
import LeanCfgProject.TCS1.ClarkCongruentialComparison

/-!
# TCS #1 v79 delta verification facade

This lightweight facade collects theorem-facing modules added specifically
while synchronizing the Lean experiment with the v79 manuscript, including the Section 9 boundary work.  It is used
by a fast CI job during development; the full `TCS1.All` facade remains the
final integration check; both facades track the current v78 theorem surface.
-/

namespace LeanCfgProject
namespace TCS1

theorem v77_delta_facade_loaded : True :=
  True.intro

theorem v78_delta_facade_loaded : True :=
  True.intro

/-- Current manuscript marker; v79 keeps the v78 mathematical content. -/
theorem v79_delta_facade_loaded : True :=
  True.intro

end TCS1
end LeanCfgProject
