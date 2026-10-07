import LeanCfgProject.TCS1.V121ProductiveLinearFilter
import LeanCfgProject.TCS1.IndexedLinearNormalizationFacade

/-!
# TCS #1 v121: arbitrary finite linear CFG, regular filtering preserves linearity

Compose the already verified arbitrary indexed-linear normalization with
the productive DFA-product closure for normalized single-spine SSBNF.

The explicit witness is a *finite* grammar whose non-start states are
productive triples (A,p,q), whose start accepts exactly the recognized
regular filter (including epsilon), and whose wrapper-spine shape certifies
linearity. No generic unproved CFL closure hypothesis is used.

This establishes the *grammatical* half of the v121 line
  L in C_lin(h), Q = g^-1(F) => L ∩ Q in C_lin(h × g).
The fixed-h substitutability half is a separate, already proven
regular-intersection/product-typing theorem.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section V121IndexedLinearRegularClosure

variable {N : Type u} {α : Type v} {P : Type w} {Q : Type z}
variable [Fintype N] [Fintype α] [Fintype P] [Fintype Q]

/--
Given a finite indexed *linear* CFG and a finite-state regular filter,
an explicit finite productive filtered SSBNF recognizes their
intersection and retains the linear-spine structure.
-/
theorem v121_indexedLinear_regularIntersection_package
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (δ : Q → α → Q)
    (q₀ : Q)
    (accept : Q → Prop) :
    let B := G.linearPreparedGrammar hlinear
    let t := LinearConstructedTerminalRule B
    let b := LinearConstructedBinaryRule B
    let s := linearConstructedStartRule B S
    let eps := G.linearKeepEmpty hlinear S
    let Wrapper := LinearConstructedWrapper B
    UntypedStartLanguage
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (v121ProductiveFilterStart δ t b s q₀ accept)
      (eps ∧ accept q₀) =
      LeastClosedLanguage G.toMixedRules S
        ∩ {word : Word α | accept (v115AutomatonRead δ q₀ word)}
    ∧
    UntypedLinearSpineShape
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (fun X => Wrapper X.val.1)
    ∧
    Finite (V121ProductiveFilterState δ t b) := by
  let B := G.linearPreparedGrammar hlinear
  let t := LinearConstructedTerminalRule B
  let b := LinearConstructedBinaryRule B
  let s := linearConstructedStartRule B S
  let eps := G.linearKeepEmpty hlinear S
  let Wrapper := LinearConstructedWrapper B
  have hshape :
      UntypedLinearSpineShape t b Wrapper :=
    linearConstructed_untypedLinearSpineShape B
  have hpkg :=
    v121_productiveFilter_linear_package
      δ q₀ accept t b s eps Wrapper hshape
  have hlang :
      UntypedStartLanguage t b s eps =
      LeastClosedLanguage G.toMixedRules S :=
    indexedLinear_constructedStartLanguage_eq_source
      G hlinear S
  dsimp only
  refine ⟨?_, hpkg.2, ?_⟩
  · calc
      UntypedStartLanguage
        (v121ProductiveFilterTerminal δ t b)
        (v121ProductiveFilterBinary δ t b)
        (v121ProductiveFilterStart δ t b s q₀ accept)
        (eps ∧ accept q₀) =
          UntypedStartLanguage t b s eps
          ∩ {word : Word α |
              accept (v115AutomatonRead δ q₀ word)} :=
        hpkg.1
      _ = LeastClosedLanguage G.toMixedRules S
            ∩ {word : Word α |
                accept (v115AutomatonRead δ q₀ word)} := by
        rw [hlang]
  · exact v121_productiveFilter_finite δ t b

end V121IndexedLinearRegularClosure

end TCS1
end LeanCfgProject
