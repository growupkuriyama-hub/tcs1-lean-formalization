import LeanCfgProject.TCS1.ClarkCongruentialPackaging
import LeanCfgProject.TCS1.IndexedNormalizationLanguage

/-!
# TCS #1 v78: indexed finite-CFG facade for Clark congruentiality

The finite-initial-set packaging theorem is stated for a start-separated SSBNF
presentation.  This file composes it with the concrete indexed normalization
pipeline, giving the paper-facing inclusion statement directly from a finite
indexed CFG presentation whose start language contains a nonempty word.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w x

section ClarkCongruentialIndexedFacade

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {M : Type x}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]
variable [Monoid M] [Fintype M]

noncomputable section

/-- Final reduced SSBNF state type produced from a finite indexed CFG. -/
abbrev IndexedClarkReducedState
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :=
  ReducedUnitFreeState
    (indexedFiniteFrontEndGrammar G)
    (indexedProductiveUnitFreeState_of_nonempty
      G A hprod)

/-- Terminal relation of the final reduced SSBNF presentation. -/
def indexedClarkTerminalRule
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    IndexedClarkReducedState G A hprod → α → Prop :=
  reducedSSBNFTerminalRule
    (indexedFiniteFrontEndGrammar G)
    (indexedProductiveUnitFreeState_of_nonempty
      G A hprod)

/-- Binary relation of the final reduced SSBNF presentation. -/
def indexedClarkBinaryRule
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    IndexedClarkReducedState G A hprod →
      IndexedClarkReducedState G A hprod →
      IndexedClarkReducedState G A hprod → Prop :=
  reducedSSBNFBinaryRule
    (indexedFiniteFrontEndGrammar G)
    (indexedProductiveUnitFreeState_of_nonempty
      G A hprod)

/-- Start-child relation of the final reduced SSBNF presentation. -/
def indexedClarkStartRule
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    IndexedClarkReducedState G A hprod → Prop :=
  reducedSSBNFStartRule
    (indexedFiniteFrontEndGrammar G)
    (indexedProductiveUnitFreeState_of_nonempty
      G A hprod)

/-- Optional epsilon-start condition of the normalized presentation. -/
def indexedClarkEpsilonStart
    (G : IndexedMixedCFG N α P)
    (A : N) : Prop :=
  [] ∈ LeastClosedLanguage G.toMixedRules A

/-- Clark-packaged grammar obtained from the normalized typed refinement. -/
def indexedClarkPackagedGrammar
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :=
  clarkPackagedGrammar
    H
    (indexedClarkTerminalRule G A hprod)
    (indexedClarkBinaryRule G A hprod)
    (indexedClarkStartRule G A hprod)
    (indexedClarkEpsilonStart G A)

/-- Finite initial set of the normalized Clark package. -/
def indexedClarkInitial
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :=
  clarkPackagedInitial
    H
    (indexedClarkTerminalRule G A hprod)
    (indexedClarkBinaryRule G A hprod)
    (indexedClarkStartRule G A hprod)
    (indexedClarkEpsilonStart G A)

/--
The normalized learner-style SSBNF language used by the packaging theorem is
literally the source-start language.
-/
theorem indexedClark_untypedStartLanguage_eq_source
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ []) :
    UntypedStartLanguage
        (indexedClarkTerminalRule G A hprod)
        (indexedClarkBinaryRule G A hprod)
        (indexedClarkStartRule G A hprod)
        (indexedClarkEpsilonStart G A)
      =
    LeastClosedLanguage G.toMixedRules A := by
  exact
    indexedReducedSSBNF_untypedStartLanguage_eq_source
      G A hprod

/--
Fixed-h substitutability transports from the source language to the normalized
start-separated SSBNF presentation.
-/
theorem indexedClark_normalized_fixedH
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    FixedHSubstitutable H
      (UntypedStartLanguage
        (indexedClarkTerminalRule G A hprod)
        (indexedClarkBinaryRule G A hprod)
        (indexedClarkStartRule G A hprod)
        (indexedClarkEpsilonStart G A)) := by
  rw [indexedClark_untypedStartLanguage_eq_source
    G A hprod]
  exact hsub

/--
Paper-facing nontrivial-target case of Proposition 9.9.

For a finite indexed CFG presentation of a fixed-h substitutable CFL, provided
the start language contains at least one nonempty word, the concrete
normalization and typed refinement produce a finite-initial-set congruential
CFG whose language is exactly the source language.
-/
theorem indexed_fixedH_has_Clark_congruential_packaging
    (H : FixedFiniteMonoidHom α M)
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (hsub :
      FixedHSubstitutable H
        (LeastClosedLanguage G.toMixedRules A)) :
    (indexedClarkInitial H G A hprod).Finite
      ∧
    InitialSetLanguage
        (indexedClarkPackagedGrammar H G A hprod)
        (indexedClarkInitial H G A hprod)
      =
    LeastClosedLanguage G.toMixedRules A
      ∧
    ClarkCongruentialInitialSet
      (indexedClarkPackagedGrammar H G A hprod)
      (indexedClarkInitial H G A hprod) := by
  have hsubNorm :
      FixedHSubstitutable H
        (UntypedStartLanguage
          (indexedClarkTerminalRule G A hprod)
          (indexedClarkBinaryRule G A hprod)
          (indexedClarkStartRule G A hprod)
          (indexedClarkEpsilonStart G A)) :=
    indexedClark_normalized_fixedH
      H G A hprod hsub

  have hpack :=
    fixedH_has_Clark_congruential_packaging
      H
      (indexedClarkTerminalRule G A hprod)
      (indexedClarkBinaryRule G A hprod)
      (indexedClarkStartRule G A hprod)
      (indexedClarkEpsilonStart G A)
      hsubNorm

  rcases hpack with
    ⟨hfinite, hlang, hcong⟩
  refine ⟨hfinite, ?_, hcong⟩
  calc
    InitialSetLanguage
        (indexedClarkPackagedGrammar H G A hprod)
        (indexedClarkInitial H G A hprod)
      =
    UntypedStartLanguage
        (indexedClarkTerminalRule G A hprod)
        (indexedClarkBinaryRule G A hprod)
        (indexedClarkStartRule G A hprod)
        (indexedClarkEpsilonStart G A) := by
      exact hlang
    _ =
    LeastClosedLanguage G.toMixedRules A :=
      indexedClark_untypedStartLanguage_eq_source
        G A hprod

end

end ClarkCongruentialIndexedFacade

end TCS1
end LeanCfgProject
