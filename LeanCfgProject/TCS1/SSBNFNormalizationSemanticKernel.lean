import LeanCfgProject.TCS1.BinaryUnitElimination
import LeanCfgProject.TCS1.NormalizationLanguageBounds

/-!
# TCS #1: concrete semantic kernel for the latter SSBNF normalization stages

This file instantiates the abstract language-bound transfer theorem with the
actual binary epsilon-elimination and unit-elimination semantics proved in the
preceding modules.

Consequently, once the binarized grammar B has the appendix's uniform bound on
shortest nonempty yields, the same bound survives:

  B
    -> non-start epsilon elimination
    -> removal of symbols with no nonempty yield
    -> unit elimination
    -> final trimming.

This is the exact semantic/quantitative bridge used in Proposition
"polynomial thickness-preserving SSBNF normalization".
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section SSBNFNormalizationSemanticKernel

variable {N : Type u}
variable {α : Type v}

/--
Concrete latter-half normalization theorem, before substituting the explicit
quadratic envelope.
-/
theorem binary_epsilon_unit_trim_preserve_bound
    (G : BinaryNullableGrammar N α)
    {Nsurv : Type u}
    {Nfinal : Type u}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    {b : Nat}
    (hB :
      NonemptyYieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        b)
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives G (surv A) w})) :
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives G (surv (final A)) w})
      b := by
  apply epsilon_unit_trim_preserve_bound
    (LB := fun A => {w | BinaryNullableDerives G A w})
    (Leps := fun A => {w | EpsilonFreeDerives G A w})
    (Lunit := fun A => {w | UnitFreeDerives G A w})
    surv final hB
  · exact epsilon_elimination_sameNonemptyLanguage G
  · exact hsurv
  · intro A w
    exact unit_elimination_preserves_language G (surv A) w

/--
Instantiate the theorem with the explicit appendix envelope

  1 + cV*c1*n^2*(tau_R+1).

Thus the concrete epsilon/unit/trimming stages cannot worsen the polynomial
shortest-yield estimate proved for the binarized grammar.
-/
theorem binary_epsilon_unit_trim_preserve_ssbnfEnvelope
    (G : BinaryNullableGrammar N α)
    {Nsurv : Type u}
    {Nfinal : Type u}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    (cV c₁ n τR : Nat)
    (hB :
      NonemptyYieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        (ssbnfThicknessEnvelope cV c₁ n τR))
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives G (surv A) w})) :
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives G (surv (final A)) w})
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  exact binary_epsilon_unit_trim_preserve_bound
    G surv final hB hsurv

/--
The output of unit elimination has no empty derivations.
-/
theorem unitFreeDerives_nonempty
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (d : UnitFreeDerives G A w) :
    w ≠ [] := by
  induction d with
  | terminal _ =>
      simp
  | binary _ _ _ ihL _ihR =>
      exact append_ne_nil_of_left_ne_nil ihL

/--
Therefore every productive symbol retained after unit elimination is
automatically productive by a nonempty terminal word.
-/
theorem unitFree_allHaveNonempty_of_productive
    (G : BinaryNullableGrammar N α)
    {N' : Type u}
    (embed : N' → N)
    (hprod :
      ∀ A : N',
        ∃ w, UnitFreeDerives G (embed A) w) :
    AllHaveNonemptyYield
      (fun A : N' => {w | UnitFreeDerives G (embed A) w}) := by
  intro A
  obtain ⟨w, dw⟩ := hprod A
  exact ⟨w, dw, unitFreeDerives_nonempty G dw⟩

end SSBNFNormalizationSemanticKernel

end TCS1
end LeanCfgProject
