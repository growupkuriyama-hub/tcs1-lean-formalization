import LeanCfgProject.TCS1.ReconstructionActiveGrammar
import LeanCfgProject.TCS1.BinaryUnitElimination
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage

/-!
# TCS #1 v79: unit-free reconstruction grammar and exact start-language bridge

The finite active reconstruction grammar still contains the paper's unary
rules R2 and R3.  The generic unit-elimination development already turns any
binary/terminal/unit grammar into an equivalent terminal/binary grammar via
unit closure.

This module instantiates that construction for the reconstructed hypothesis
and proves the exact bridge needed by the CYK layer:

  BatchLanguage H K
    =
  UntypedStartLanguage
    (unit-free reconstruction terminal rules)
    (unit-free reconstruction binary rules)
    (observed top-level start children)
    ([] in K).

Thus the language tested by the executable CYK interface is now connected
semantically to the actual set-driven learner, not merely to an abstract
SSBNF grammar.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionUnitFreeBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Terminal relation after unit-closing the finite active reconstruction grammar. -/
def reconstructionUnitFreeTerminalRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ActiveReconstructionNonterminal K → α → Prop :=
  UnitFreeTerminalRule
    (reconstructionActiveGrammar H K)

/-- Binary relation after unit-closing the finite active reconstruction grammar. -/
def reconstructionUnitFreeBinaryRule
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    ActiveReconstructionNonterminal K →
      ActiveReconstructionNonterminal K →
      ActiveReconstructionNonterminal K → Prop :=
  UnitFreeBinaryRule
    (reconstructionActiveGrammar H K)

/--
A reconstructed start child is exactly an observed symbol whose external
contexts are both empty.
-/
def reconstructionActiveStartRule
    (K : Finset (Word α)) :
    ActiveReconstructionNonterminal K → Prop :=
  fun A =>
    A.1.leftContext = [] ∧
    A.1.rightContext = []

/-- Unit-free derivations erase directly to the terminal/binary derivation type. -/
theorem unitFreeDerives_to_untypedDerives
    (G : BinaryNullableGrammar
      (ActiveReconstructionNonterminal K) α)
    {A : ActiveReconstructionNonterminal K}
    {w : Word α}
    (d : UnitFreeDerives G A w) :
    UntypedDerives
      (UnitFreeTerminalRule G)
      (UnitFreeBinaryRule G)
      A w := by
  induction d with
  | terminal h =>
      exact UntypedDerives.terminal h
  | binary h _ _ ihB ihC =>
      exact UntypedDerives.binary h ihB ihC

/-- Conversely every terminal/binary derivation is a unit-free derivation. -/
theorem untypedDerives_to_unitFreeDerives
    (G : BinaryNullableGrammar
      (ActiveReconstructionNonterminal K) α)
    {A : ActiveReconstructionNonterminal K}
    {w : Word α}
    (d :
      UntypedDerives
        (UnitFreeTerminalRule G)
        (UnitFreeBinaryRule G)
        A w) :
    UnitFreeDerives G A w := by
  induction d with
  | terminal h =>
      exact UnitFreeDerives.terminal h
  | binary h _ _ ihB ihC =>
      exact UnitFreeDerives.binary h ihB ihC

/--
Exact non-start bridge from the learner's R1--R4 semantics to the terminal /
binary grammar obtained by unit elimination.
-/
theorem reconstructionUnitFree_untypedDerives_iff_hypDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ActiveReconstructionNonterminal K)
    (w : Word α) :
    UntypedDerives
        (reconstructionUnitFreeTerminalRule H K)
        (reconstructionUnitFreeBinaryRule H K)
        A w
      ↔
    HypDerives H K
      A.1.factor A.1.leftContext A.1.rightContext w := by
  constructor
  · intro d
    have dUnit :
        UnitFreeDerives
          (reconstructionActiveGrammar H K)
          A w :=
      untypedDerives_to_unitFreeDerives
        (reconstructionActiveGrammar H K) d
    have dEps :
        EpsilonFreeDerives
          (reconstructionActiveGrammar H K)
          A w :=
      unitFreeDerives_to_epsilonFree
        (reconstructionActiveGrammar H K)
        dUnit
    have dBin :
        BinaryNullableDerives
          (reconstructionActiveGrammar H K)
          A w :=
      epsilonFreeDerives_to_binaryNullable
        (reconstructionActiveGrammar H K)
        dEps
    exact
      activeGrammar_to_hypDerives H K dBin
  · intro d
    have dBin :
        BinaryNullableDerives
          (reconstructionActiveGrammar H K)
          A w :=
      (activeGrammar_iff_hypDerives H K A w).2 d
    have hne : w ≠ [] :=
      hypDerives_nonempty H K d
    have dEps :
        EpsilonFreeDerives
          (reconstructionActiveGrammar H K)
          A w :=
      binaryNullableDerives_to_epsilonFree
        (reconstructionActiveGrammar H K)
        dBin hne
    have dUnit :
        UnitFreeDerives
          (reconstructionActiveGrammar H K)
          A w :=
      epsilonFreeDerives_to_unitFree
        (reconstructionActiveGrammar H K)
        dEps
    exact
      unitFreeDerives_to_untypedDerives
        (reconstructionActiveGrammar H K)
        dUnit

/--
Exact start-level equivalence between the learner's `BatchDerives` semantics
and the start-separated terminal/binary grammar produced by unit elimination.
-/
theorem reconstructionUnitFree_untypedStartDerives_iff_batchDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (w : Word α) :
    UntypedStartDerives
        (reconstructionUnitFreeTerminalRule H K)
        (reconstructionUnitFreeBinaryRule H K)
        (reconstructionActiveStartRule K)
        (([] : Word α) ∈ K)
        w
      ↔
    BatchDerives H K w := by
  constructor
  · intro d
    cases d with
    | @nonempty A _ hstart hder =>
        rcases A with ⟨⟨x, u, v⟩, hobs⟩
        change u = [] ∧ v = [] at hstart
        rcases hstart with ⟨hu, hv⟩
        subst u
        subst v
        have hxne : x ≠ [] := hobs.1
        have hxK : x ∈ K := by
          simpa using hobs.2
        have hhyp :
            HypDerives H K x [] [] w :=
          (reconstructionUnitFree_untypedDerives_iff_hypDerives
            H K ⟨⟨x, [], []⟩, hobs⟩ w).1 hder
        exact
          BatchDerives.nonempty hxK hxne hhyp
    | epsilon heps =>
        exact BatchDerives.epsilon heps
  · intro d
    cases d with
    | @nonempty s _ hs hsne hder =>
        have hobs : Observed K s [] [] := by
          constructor
          · exact hsne
          · simpa using hs
        let A : ActiveReconstructionNonterminal K :=
          ⟨⟨s, [], []⟩, hobs⟩
        have hstart :
            reconstructionActiveStartRule K A := by
          exact ⟨rfl, rfl⟩
        have hunit :
            UntypedDerives
              (reconstructionUnitFreeTerminalRule H K)
              (reconstructionUnitFreeBinaryRule H K)
              A w :=
          (reconstructionUnitFree_untypedDerives_iff_hypDerives
            H K A w).2 hder
        exact
          UntypedStartDerives.nonempty hstart hunit
    | epsilon heps =>
        exact UntypedStartDerives.epsilon heps

/-- Set-valued exact language identity consumed by the membership layer. -/
theorem reconstructionUnitFree_untypedStartLanguage_eq_batchLanguage
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    UntypedStartLanguage
        (reconstructionUnitFreeTerminalRule H K)
        (reconstructionUnitFreeBinaryRule H K)
        (reconstructionActiveStartRule K)
        (([] : Word α) ∈ K)
      =
    BatchLanguage H K := by
  apply Set.ext
  intro w
  exact
    reconstructionUnitFree_untypedStartDerives_iff_batchDerives
      H K w

end ReconstructionUnitFreeBridge

end TCS1
end LeanCfgProject
