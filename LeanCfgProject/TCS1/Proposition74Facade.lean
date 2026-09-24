import LeanCfgProject.TCS1.BinarizationKernel
import LeanCfgProject.TCS1.ShortestNonemptySpineSemantic
import LeanCfgProject.TCS1.SSBNFNormalizationSemanticKernel
import LeanCfgProject.TCS1.SSBNFNormalizationCombinatorics

/-!
# TCS #1 v65: Proposition 7.4 quantitative facade

This module composes the verified pieces of Appendix A in the same order as
the manuscript:

  start separation / terminal isolation / binarization -> B,
  shortest nonempty yield bound in B,
  binary-first non-start epsilon elimination,
  unit elimination,
  final trimming.

The front-end modules verify the local terminal-isolation and binarization
semantics and the binarized thickness arithmetic. The latter-half modules
verify exact preservation of nonempty languages under epsilon elimination and
full languages under unit elimination. Here we package the quantitative
conclusion used in Proposition 7.4.

The only semantic input not re-proved here is the manuscript's root-to-leaf
cycle-shortening lemma for B: it is represented by `hNonemptyB`. Its finite
tree-counting arithmetic is checked separately in ShortestNonemptyPathBound.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section Proposition74Facade

variable {N : Type u}
variable {α : Type v}

/-- A uniform yield bound can always be weakened to a larger numerical bound. -/
theorem yieldBound_mono
    {L : NTLang N α}
    {b₁ b₂ : Nat}
    (h₁ : YieldBound L b₁)
    (hb : b₁ ≤ b₂) :
    YieldBound L b₂ := by
  intro A
  obtain ⟨w, hw, hlen⟩ := h₁ A
  exact ⟨w, hw, le_trans hlen hb⟩

/-- A shortest-nonempty-yield bound is monotone in its numerical envelope. -/
theorem nonemptyYieldBound_mono
    {L : NTLang N α}
    {b₁ b₂ : Nat}
    (h₁ : NonemptyYieldBound L b₁)
    (hb : b₁ ≤ b₂) :
    NonemptyYieldBound L b₂ := by
  intro A hexists
  obtain ⟨w, hw, hwne, hlen⟩ := h₁ A hexists
  exact ⟨w, hw, hwne, le_trans hlen hb⟩

/--
Quantitative latter-half of Proposition 7.4.

Assume B has at most cV*n nonterminals, tau_B is at most
c1*n*(tau_R+1), and the root-to-leaf shortening argument has produced the
bound 1+|V_B|*tau_B for every nonempty-productive nonterminal of B. Then
epsilon elimination, unit elimination, and trimming preserve the explicit
quadratic envelope from the paper.
-/
theorem proposition74_thickness_facade
    [Fintype N]
    (G : BinaryNullableGrammar N α)
    {Nsurv Nfinal : Type u}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    (cV c₁ n τR τB : Nat)
    (hV : Fintype.card N ≤ cV * n)
    (hτB : τB ≤ binarizedThicknessEnvelope c₁ n τR)
    (hNonemptyB :
      NonemptyYieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        (nullableNonemptyEnvelope (Fintype.card N) τB))
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives G (surv A) w})) :
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives G (surv (final A)) w})
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  have hEnv :
      nullableNonemptyEnvelope (Fintype.card N) τB ≤
        ssbnfThicknessEnvelope cV c₁ n τR :=
    nullableNonemptyEnvelope_le_ssbnfThicknessEnvelope
      hV hτB
  have hB' :
      NonemptyYieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        (ssbnfThicknessEnvelope cV c₁ n τR) :=
    nonemptyYieldBound_mono hNonemptyB hEnv
  exact binary_epsilon_unit_trim_preserve_bound
    G surv final hB' hsurv

/--
Rule-count side of the same appendix proof. Binary-first epsilon elimination
has local factor at most three, and unit closure then has a quadratic raw
copy space.
-/
theorem proposition74_rule_count_facade
    {v p t cV cP cT n : Nat}
    (hv : v ≤ cV * n)
    (hp : p ≤ cP * n)
    (ht : t ≤ cT * n) :
    v * (t + 3 * p) ≤
      (cV * (cT + 3 * cP)) * n^2 :=
  normalization_rule_count_quadratic hv hp ht

/--
Combined paper-facing quantitative package: the raw final rule space is
quadratic in n and every surviving final nonterminal has a terminal witness
inside the explicit quadratic thickness envelope.
-/
theorem proposition74_quantitative_package
    [Fintype N]
    (G : BinaryNullableGrammar N α)
    {Nsurv Nfinal : Type u}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    (cV cP cT c₁ n τR τB v p t : Nat)
    (hVcard : Fintype.card N ≤ cV * n)
    (hτB : τB ≤ binarizedThicknessEnvelope c₁ n τR)
    (hNonemptyB :
      NonemptyYieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        (nullableNonemptyEnvelope (Fintype.card N) τB))
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives G (surv A) w}))
    (hv : v ≤ cV * n)
    (hp : p ≤ cP * n)
    (ht : t ≤ cT * n) :
    v * (t + 3 * p) ≤
        (cV * (cT + 3 * cP)) * n^2
    ∧
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives G (surv (final A)) w})
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  constructor
  · exact proposition74_rule_count_facade hv hp ht
  · exact proposition74_thickness_facade
      G surv final cV c₁ n τR τB
      hVcard hτB hNonemptyB hsurv


/--
The Appendix A root-to-leaf shortcut is now internal: a uniform terminal-yield
bound for the binary grammar B implies the shortest-nonempty bound required by
the latter half of Proposition 7.4.
-/
theorem proposition74_thickness_from_yieldBound
    [Fintype N] [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    {Nsurv Nfinal : Type u}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    (cV c₁ n τR τB : Nat)
    (hV : Fintype.card N ≤ cV * n)
    (hτB : τB ≤ binarizedThicknessEnvelope c₁ n τR)
    (hYieldB :
      YieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        τB)
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives G (surv A) w})) :
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives G (surv (final A)) w})
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  have hNonemptyB :
      NonemptyYieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        (nullableNonemptyEnvelope (Fintype.card N) τB) :=
    nonemptyYieldBound_of_yieldBound G τB hYieldB
  exact
    proposition74_thickness_facade
      G surv final cV c₁ n τR τB
      hV hτB hNonemptyB hsurv

/--
Paper-facing quantitative package with the cycle-shortening assumption fully
discharged.  The only thickness input from the front end is the ordinary
uniform terminal-yield bound on B.
-/
theorem proposition74_quantitative_package_from_yieldBound
    [Fintype N] [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    {Nsurv Nfinal : Type u}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    (cV cP cT c₁ n τR τB v p t : Nat)
    (hVcard : Fintype.card N ≤ cV * n)
    (hτB : τB ≤ binarizedThicknessEnvelope c₁ n τR)
    (hYieldB :
      YieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        τB)
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives G (surv A) w}))
    (hv : v ≤ cV * n)
    (hp : p ≤ cP * n)
    (ht : t ≤ cT * n) :
    v * (t + 3 * p) ≤
        (cV * (cT + 3 * cP)) * n^2
    ∧
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives G (surv (final A)) w})
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  constructor
  · exact proposition74_rule_count_facade hv hp ht
  · exact
      proposition74_thickness_from_yieldBound
        G surv final cV c₁ n τR τB
        hVcard hτB hYieldB hsurv

end Proposition74Facade

end TCS1
end LeanCfgProject
