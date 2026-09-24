import LeanCfgProject.TCS1.IndexedLinearNormalizationTheorem
import LeanCfgProject.TCS1.ClarkEyraudSpecialCase
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.LinearTypedShapeBridge

/-!
# TCS #1 v79: reducedness bridge for the arbitrary linear normalization

The paper-facing linear normalization proposition asks for an equivalent
reduced linear-spine SSBNF grammar.  The finite construction verified in
IndexedLinearNormalizationTheorem already supplies exact language
preservation, the one-wrapper-child linear-spine shape, and a source-polynomial
size bound.

This module closes the structural reduced clause without adding a second
normalization algorithm.  We instantiate the already verified
productive/reachable typed trim with the one-element monoid.  Because the
typing is trivial, this is just a proof-relevant copy of ordinary usefulness
trimming:

* its start language is exactly the untyped normalized language;
* every surviving symbol is productive and has a terminal reaching context;
* the linear-spine shape survives the trim.

Thus the repository now has a machine-checked reduced semantic presentation
for the output of the arbitrary linear-CFG normalization.  The explicit
polynomial size envelope remains the one proved for the pre-trim finite
construction; trimming only discards symbols/rules and is used here for the
reducedness obligation.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedLinearReducedNormalization

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]

/--
Semantic reducedness package for the normalized arbitrary linear CFG, using
the trivial finite typing so that productive/reachable typed trimming is
ordinary grammar trimming up to a singleton type annotation.
-/
theorem indexedLinear_reduced_normalization_semantic_package
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    let Gp := G.linearPreparedGrammar hlinear
    let H := trivialFiniteMonoidHom α
    let Active :=
      ConcreteTypedActive
        H
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearConstructedStartRule Gp S)
    ReducedTypedLanguage
        H
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearConstructedStartRule Gp S)
        (G.linearKeepEmpty hlinear S)
        Active
      =
    LeastClosedLanguage G.toMixedRules S
    ∧
    QualitativeReducedness
      H
      (LinearConstructedTerminalRule Gp)
      (LinearConstructedBinaryRule Gp)
      (linearConstructedStartRule Gp S)
      (G.linearKeepEmpty hlinear S)
      Active
    ∧
    LinearSpineShape
      (ActiveTypedTerminalRule
        H
        (LinearConstructedTerminalRule Gp)
        Active)
      (ActiveTypedBinaryRule
        (LinearConstructedBinaryRule Gp)
        Active)
      (typedWrapper
        (M := Unit)
        (LinearConstructedWrapper Gp)) := by
  dsimp
  let Gp := G.linearPreparedGrammar hlinear
  let H := trivialFiniteMonoidHom α
  let Active :=
    ConcreteTypedActive
      H
      (LinearConstructedTerminalRule Gp)
      (LinearConstructedBinaryRule Gp)
      (linearConstructedStartRule Gp S)

  have hlang0 :
      ReducedTypedLanguage
          H
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S)
          Active
        =
      UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S) := by
    simpa [Active] using
      concreteTypedActive_language_eq_untyped
        H
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearConstructedStartRule Gp S)
        (G.linearKeepEmpty hlinear S)

  have hsource :
      UntypedStartLanguage
          (LinearConstructedTerminalRule Gp)
          (LinearConstructedBinaryRule Gp)
          (linearConstructedStartRule Gp S)
          (G.linearKeepEmpty hlinear S)
        =
      LeastClosedLanguage G.toMixedRules S := by
    simpa [Gp] using
      indexedLinear_normalization_language_eq
        G hlinear S

  have hred :
      QualitativeReducedness
        H
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearConstructedStartRule Gp S)
        (G.linearKeepEmpty hlinear S)
        Active := by
    simpa [Active] using
      concreteTypedActive_qualitativeReducedness
        H
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearConstructedStartRule Gp S)
        (G.linearKeepEmpty hlinear S)

  have hshape0 :
      UntypedLinearSpineShape
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (LinearConstructedWrapper Gp) := by
    simpa [Gp] using
      indexedLinear_normalization_shape
        G hlinear

  have hshape :
      LinearSpineShape
        (ActiveTypedTerminalRule
          H
          (LinearConstructedTerminalRule Gp)
          Active)
        (ActiveTypedBinaryRule
          (LinearConstructedBinaryRule Gp)
          Active)
        (typedWrapper
          (M := Unit)
          (LinearConstructedWrapper Gp)) := by
    simpa [Active] using
      concreteTypedActive_linearSpineShape_of_untyped
        H
        (LinearConstructedTerminalRule Gp)
        (LinearConstructedBinaryRule Gp)
        (linearConstructedStartRule Gp S)
        (LinearConstructedWrapper Gp)
        hshape0

  refine ⟨?_, hred, hshape⟩
  exact hlang0.trans hsource

end IndexedLinearReducedNormalization

end TCS1
end LeanCfgProject
