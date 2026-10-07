import LeanCfgProject.TCS1.V121IndexedLinearRegularClosure
import LeanCfgProject.TCS1.V115FiniteInformationClosure

/-!
# TCS #1 v121: fixed-h linear languages are closed under regular filtering

This theorem packages *both* aspects of the manuscript's implication:
    L in C_lin(h), Q = g^-1(F)
          => L ∩ Q in C_lin(h × g).

The linear-language half constructs a finite productive DFA-product grammar
from an arbitrary indexed linear CFG via the verified linear normalization.
The substitutability half uses the previously proved intersection theorem
for the product typing (h,g). Nothing here asserts that an arbitrary
context-free intersection remains linear.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z q r

section V121IndexedLinearFixedHFilter

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type z} {F : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [Monoid M] [Fintype M] [Monoid F] [Fintype F]

/-- Full finite-grammar and product-typing certificate for regular filtering. -/
theorem v121_indexedLinear_regularFilter_fixedH_package
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N)
    (H : FixedFiniteMonoidHom α M)
    (g : FixedFiniteMonoidHom α F)
    (Acc : Set F)
    (hsub :
      FixedHSubstitutable H (LeastClosedLanguage G.toMixedRules S)) :
    let B := G.linearPreparedGrammar hlinear
    let t := LinearConstructedTerminalRule B
    let b := LinearConstructedBinaryRule B
    let s := linearConstructedStartRule B S
    let eps := G.linearKeepEmpty hlinear S
    let Wrapper := LinearConstructedWrapper B
    let δ := v115MonoidTransition g
    let accept := fun m : F => m ∈ Acc
    let T := V121ProductiveFilterState δ t b
    UntypedStartLanguage
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (v121ProductiveFilterStart δ t b s 1 accept)
      (eps ∧ accept (1 : F))
      =
      LeastClosedLanguage G.toMixedRules S
        ∩ RecognizedPreimage g Acc
    ∧
    UntypedLinearSpineShape
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (fun X => Wrapper X.val.1)
    ∧
    Finite T
    ∧
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H g)
      (UntypedStartLanguage
        (v121ProductiveFilterTerminal δ t b)
        (v121ProductiveFilterBinary δ t b)
        (v121ProductiveFilterStart δ t b s 1 accept)
        (eps ∧ accept (1 : F))) := by
  let B := G.linearPreparedGrammar hlinear
  let t := LinearConstructedTerminalRule B
  let b := LinearConstructedBinaryRule B
  let s := linearConstructedStartRule B S
  let eps := G.linearKeepEmpty hlinear S
  let Wrapper := LinearConstructedWrapper B
  let δ := v115MonoidTransition g
  let accept : F → Prop := fun m => m ∈ Acc
  have hpkg :=
    v121_indexedLinear_regularIntersection_package
      G hlinear S δ (1 : F) accept
  have hfilter :
      {word : Word α |
          accept (v115AutomatonRead δ (1 : F) word)} =
        RecognizedPreimage g Acc := by
    apply Set.ext
    intro word
    change v115AutomatonRead δ 1 word ∈ Acc ↔
      g.h word ∈ Acc
    rw [v115MonoidRead]
    simp
  have heq :
      UntypedStartLanguage
        (v121ProductiveFilterTerminal δ t b)
        (v121ProductiveFilterBinary δ t b)
        (v121ProductiveFilterStart δ t b s 1 accept)
        (eps ∧ accept (1 : F)) =
      LeastClosedLanguage G.toMixedRules S ∩
        RecognizedPreimage g Acc := by
    calc
      UntypedStartLanguage
        (v121ProductiveFilterTerminal δ t b)
        (v121ProductiveFilterBinary δ t b)
        (v121ProductiveFilterStart δ t b s 1 accept)
        (eps ∧ accept (1 : F)) =
        LeastClosedLanguage G.toMixedRules S ∩
          {word : Word α |
              accept (v115AutomatonRead δ (1 : F) word)} :=
        hpkg.1
      _ = LeastClosedLanguage G.toMixedRules S ∩
          RecognizedPreimage g Acc := by
        rw [hfilter]
  dsimp only
  refine ⟨heq, hpkg.2.1, hpkg.2.2, ?_⟩
  rw [heq]
  exact fixedHSubstitutable_inter_recognized_product
    H g Acc hsub

end V121IndexedLinearFixedHFilter

end TCS1
end LeanCfgProject
