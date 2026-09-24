import LeanCfgProject.TCS1.SSBNFThicknessBounds

/-!
# TCS #1: language-preservation interface for normalization thickness

The appendix uses two semantic preservation facts after the shortest-nonempty
yield bound has been established in the binary grammar B:

1. non-start epsilon elimination preserves every nonterminal's *nonempty*
   terminal language;
2. unit elimination preserves every nonterminal language.

This file formalizes exactly what those statements imply for yield-length and
thickness bounds.  It does not re-prove the standard grammar transformations;
instead it makes the semantic obligations explicit and checks that they are
sufficient for the quantitative conclusion used in Proposition
"polynomial thickness-preserving SSBNF normalization".
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section NormalizationLanguageBounds

variable {N : Type u}
variable {α : Type v}

abbrev NTLang (N : Type u) (α : Type v) :=
  N → Set (List α)

/-- One nonterminal has a nonempty terminal yield of length at most b. -/
def HasShortNonemptyYield
    (L : NTLang N α)
    (A : N)
    (b : Nat) : Prop :=
  ∃ w, w ∈ L A ∧ w ≠ [] ∧ w.length ≤ b

/--
Uniform shortest-nonempty-yield upper bound, conditional on existence of a
nonempty yield.  This is the property proved for nullable symbols of the
binary grammar B in the appendix.
-/
def NonemptyYieldBound
    (L : NTLang N α)
    (b : Nat) : Prop :=
  ∀ A,
    (∃ w, w ∈ L A ∧ w ≠ []) →
    HasShortNonemptyYield L A b

/--
Uniform terminal-yield upper bound on the surviving nonterminals.  For a
reduced grammar this implies the usual thickness is at most b.
-/
def YieldBound
    (L : NTLang N α)
    (b : Nat) : Prop :=
  ∀ A, ∃ w, w ∈ L A ∧ w.length ≤ b

/-- Pointwise equality of all nonempty terminal yields. -/
def SameNonemptyLanguage
    (L₁ L₂ : NTLang N α) : Prop :=
  ∀ A w, w ≠ [] → (w ∈ L₁ A ↔ w ∈ L₂ A)

/-- Pointwise equality of full terminal languages. -/
def SameLanguage
    (L₁ L₂ : NTLang N α) : Prop :=
  ∀ A w, w ∈ L₁ A ↔ w ∈ L₂ A

/-- Every surviving nonterminal of L has at least one nonempty yield. -/
def AllHaveNonemptyYield
    (L : NTLang N α) : Prop :=
  ∀ A, ∃ w, w ∈ L A ∧ w ≠ []

/--
Nonempty-language preservation transfers a uniform shortest-nonempty-yield
bound.
-/
theorem nonemptyYieldBound_transfer
    {L₁ L₂ : NTLang N α}
    {b : Nat}
    (hsame : SameNonemptyLanguage L₁ L₂)
    (hbound : NonemptyYieldBound L₁ b) :
    NonemptyYieldBound L₂ b := by
  intro A hExists₂
  obtain ⟨w₀, hw₀₂, hw₀ne⟩ := hExists₂
  have hw₀₁ : w₀ ∈ L₁ A :=
    (hsame A w₀ hw₀ne).2 hw₀₂
  obtain ⟨w, hw₁, hwne, hlen⟩ :=
    hbound A ⟨w₀, hw₀₁, hw₀ne⟩
  exact ⟨w, (hsame A w hwne).1 hw₁, hwne, hlen⟩

/--
If every surviving symbol has a nonempty yield, a shortest-nonempty bound is
already a thickness-style yield bound.
-/
theorem yieldBound_of_nonemptyYieldBound
    {L : NTLang N α}
    {b : Nat}
    (hexists : AllHaveNonemptyYield L)
    (hbound : NonemptyYieldBound L b) :
    YieldBound L b := by
  intro A
  obtain ⟨w₀, hw₀, hw₀ne⟩ := hexists A
  obtain ⟨w, hw, _hwne, hlen⟩ :=
    hbound A ⟨w₀, hw₀, hw₀ne⟩
  exact ⟨w, hw, hlen⟩

/-- Full language preservation transfers a yield bound directly. -/
theorem yieldBound_transfer_sameLanguage
    {L₁ L₂ : NTLang N α}
    {b : Nat}
    (hsame : SameLanguage L₁ L₂)
    (hbound : YieldBound L₁ b) :
    YieldBound L₂ b := by
  intro A
  obtain ⟨w, hw, hlen⟩ := hbound A
  exact ⟨w, (hsame A w).1 hw, hlen⟩

/--
Trimming to a surviving family of nonterminals does not worsen a uniform
yield bound: restriction only removes symbols from the maximum.
-/
theorem yieldBound_restrict
    {N' : Type u}
    (embed : N' → N)
    {L : NTLang N α}
    {b : Nat}
    (hbound : YieldBound L b) :
    YieldBound (fun A' => L (embed A')) b := by
  intro A'
  exact hbound (embed A')

/--
Semantic core of the latter half of the appendix normalization proof.

Start with the binary grammar B and a bound on shortest nonempty yields.
Epsilon elimination preserves nonempty languages.  After deleting symbols
with no nonempty yield, every survivor is nonempty-productive, so the same
number is a genuine yield bound.  Unit elimination preserves full languages,
and final trimming/restriction cannot increase the bound.
-/
theorem epsilon_unit_trim_preserve_bound
    {Nsurv Nfinal : Type u}
    {LB Leps Lunit : NTLang N α}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    {b : Nat}
    (hB : NonemptyYieldBound LB b)
    (heps : SameNonemptyLanguage LB Leps)
    (hsurv :
      AllHaveNonemptyYield (fun A : Nsurv => Leps (surv A)))
    (hunit :
      SameLanguage
        (fun A : Nsurv => Leps (surv A))
        (fun A : Nsurv => Lunit (surv A))) :
    YieldBound
      (fun A : Nfinal => Lunit (surv (final A))) b := by
  have hEpsAll : NonemptyYieldBound Leps b :=
    nonemptyYieldBound_transfer heps hB
  have hEpsSurv :
      NonemptyYieldBound (fun A : Nsurv => Leps (surv A)) b := by
    intro A hExists
    obtain ⟨w₀, hw₀, hw₀ne⟩ := hExists
    obtain ⟨w, hw, hwne, hlen⟩ :=
      hEpsAll (surv A) ⟨w₀, hw₀, hw₀ne⟩
    exact ⟨w, hw, hwne, hlen⟩
  have hYieldEps :
      YieldBound (fun A : Nsurv => Leps (surv A)) b :=
    yieldBound_of_nonemptyYieldBound hsurv hEpsSurv
  have hYieldUnit :
      YieldBound (fun A : Nsurv => Lunit (surv A)) b :=
    yieldBound_transfer_sameLanguage hunit hYieldEps
  exact yieldBound_restrict final hYieldUnit

/--
Plug in the appendix's explicit shortest-nonempty envelope.
-/
theorem epsilon_unit_trim_preserve_ssbnfEnvelope
    {Nsurv Nfinal : Type u}
    {LB Leps Lunit : NTLang N α}
    (surv : Nsurv → N)
    (final : Nfinal → Nsurv)
    (cV c₁ n τR : Nat)
    (hB :
      NonemptyYieldBound LB
        (ssbnfThicknessEnvelope cV c₁ n τR))
    (heps : SameNonemptyLanguage LB Leps)
    (hsurv :
      AllHaveNonemptyYield (fun A : Nsurv => Leps (surv A)))
    (hunit :
      SameLanguage
        (fun A : Nsurv => Leps (surv A))
        (fun A : Nsurv => Lunit (surv A))) :
    YieldBound
      (fun A : Nfinal => Lunit (surv (final A)))
      (ssbnfThicknessEnvelope cV c₁ n τR) := by
  exact epsilon_unit_trim_preserve_bound
    surv final hB heps hsurv hunit

end NormalizationLanguageBounds

end TCS1
end LeanCfgProject
