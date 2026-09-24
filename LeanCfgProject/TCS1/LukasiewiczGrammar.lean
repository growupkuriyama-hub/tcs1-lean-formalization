import LeanCfgProject.TCS1.DyckOneBracketGrammar
import LeanCfgProject.TCS1.LukasiewiczBoundary

/-!
# TCS #1 v78: explicit CFG for the Lukasiewicz language

The manuscript uses the grammar

  S -> a S S | b

for the Lukasiewicz language and the identity L_Luk = D1 b.

This file formalizes both facts. First we give the direct recursive semantics
of the displayed grammar and prove that every derived word is exactly a
one-bracket Dyck word followed by b, and conversely. Then we binarize the
displayed grammar with terminal wrapper A and auxiliary symbol X:

  S -> b | A X
  A -> a
  X -> S S.

The resulting finite binary grammar is proved to generate exactly the
semantic language from the Lukasiewicz boundary module.
-/

namespace LeanCfgProject
namespace TCS1
namespace Lukasiewicz

open DyckOne
open DyckOne.Symbol

/-- Direct derivation semantics of S -> a S S | b. -/
inductive PaperDerives : Word DyckOne.Symbol → Prop
  | leaf :
      PaperDerives [b]
  | branch
      {x y : Word DyckOne.Symbol}
      (dx : PaperDerives x)
      (dy : PaperDerives y) :
      PaperDerives (a :: x ++ y)

/--
Every displayed-grammar derivation has the form x b with x a Dyck word.
-/
theorem paperDerives_shape
    {w : Word DyckOne.Symbol}
    (d : PaperDerives w) :
    ∃ x : Word DyckOne.Symbol,
      DyckOne.PaperDerives x ∧
      w = x ++ [b] := by
  induction d with
  | leaf =>
      exact
        ⟨[], DyckOne.PaperDerives.epsilon,
          by simp⟩
  | @branch u v du dv ihu ihv =>
      rcases ihu with
        ⟨x, hx, rfl⟩
      rcases ihv with
        ⟨y, hy, rfl⟩
      refine
        ⟨a :: x ++ b :: y,
          DyckOne.PaperDerives.branch hx hy,
          ?_⟩
      simp [List.append_assoc]

/--
Conversely, appending b to any Dyck paper derivation gives a derivation of
S -> a S S | b.
-/
theorem dyckPaperDerives_to_paper
    {x : Word DyckOne.Symbol}
    (d : DyckOne.PaperDerives x) :
    PaperDerives (x ++ [b]) := by
  induction d with
  | epsilon =>
      simpa using PaperDerives.leaf
  | @branch u v du dv ihu ihv =>
      have h :=
        PaperDerives.branch ihu ihv
      simpa [List.append_assoc] using h

/-- Exact semantic equivalence of the displayed grammar and D1 b. -/
theorem paperDerives_iff_language
    (w : Word DyckOne.Symbol) :
    PaperDerives w ↔ w ∈ Language := by
  constructor
  · intro d
    rcases paperDerives_shape d with
      ⟨x, hx, rfl⟩
    exact
      ⟨x,
        DyckOne.paperDerives_to_language hx,
        rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact
      dyckPaperDerives_to_paper
        (DyckOne.language_to_paperDerives hx)

/-- Three nonterminals for the binary presentation. -/
inductive GrammarNT where
  | s
  | ta
  | x
  deriving DecidableEq, Fintype, Repr

/-- Terminal rules S -> b and A -> a. -/
inductive GrammarTerminalRule :
    GrammarNT → DyckOne.Symbol → Prop
  | s_b :
      GrammarTerminalRule .s b
  | ta_a :
      GrammarTerminalRule .ta a

/-- Binary rules S -> A X and X -> S S. -/
inductive GrammarBinaryRule :
    GrammarNT → GrammarNT → GrammarNT → Prop
  | s_ax :
      GrammarBinaryRule .s .ta .x
  | x_ss :
      GrammarBinaryRule .x .s .s

/-- Binarized finite CFG for the Lukasiewicz language. -/
def binaryGrammar :
    BinaryNullableGrammar
      GrammarNT DyckOne.Symbol where
  terminalRule := GrammarTerminalRule
  binaryRule := GrammarBinaryRule
  epsilonRule _ := False
  unitRule _ _ := False

/-- Closed forms for all binary-grammar nonterminal languages. -/
def BinaryShape :
    GrammarNT → Word DyckOne.Symbol → Prop
  | .s, w =>
      PaperDerives w
  | .ta, w =>
      w = [a]
  | .x, w =>
      ∃ u v : Word DyckOne.Symbol,
        PaperDerives u ∧
        PaperDerives v ∧
        w = u ++ v

/-- Every binary-grammar derivation has the advertised closed form. -/
theorem binaryDerives_shape
    {A : GrammarNT}
    {w : Word DyckOne.Symbol}
    (d :
      BinaryNullableDerives binaryGrammar A w) :
    BinaryShape A w := by
  induction d with
  | terminal h =>
      change GrammarTerminalRule _ _ at h
      cases h with
      | s_b =>
          exact PaperDerives.leaf
      | ta_a =>
          rfl
  | epsilon h =>
      exact False.elim h
  | unit h d ih =>
      exact False.elim h
  | @binary A B C wB wC h dB dC ihB ihC =>
      change GrammarBinaryRule A B C at h
      cases h with
      | s_ax =>
          change wB = [a] at ihB
          change
            ∃ u v : Word DyckOne.Symbol,
              PaperDerives u ∧
              PaperDerives v ∧
              wC = u ++ v at ihC
          rcases ihC with
            ⟨u, v, hu, hv, rfl⟩
          subst wB
          change
            PaperDerives ([a] ++ (u ++ v))
          simpa [List.append_assoc] using
            PaperDerives.branch hu hv
      | x_ss =>
          change PaperDerives wB at ihB
          change PaperDerives wC at ihC
          exact
            ⟨wB, wC, ihB, ihC, rfl⟩

/-- Every displayed-grammar derivation is realized by the binary grammar. -/
theorem paperDerives_to_binary
    {w : Word DyckOne.Symbol}
    (d : PaperDerives w) :
    BinaryNullableDerives
      binaryGrammar .s w := by
  induction d with
  | leaf =>
      exact
        BinaryNullableDerives.terminal
          GrammarTerminalRule.s_b
  | @branch u v du dv ihu ihv =>
      have da :
          BinaryNullableDerives
            binaryGrammar .ta [a] :=
        BinaryNullableDerives.terminal
          GrammarTerminalRule.ta_a
      have dx :
          BinaryNullableDerives
            binaryGrammar .x (u ++ v) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.x_ss ihu ihv
      have ds :
          BinaryNullableDerives
            binaryGrammar .s
            ([a] ++ (u ++ v)) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.s_ax da dx
      simpa [List.append_assoc] using ds

/-- Single initial symbol S. -/
def initial : Set GrammarNT :=
  {A | A = .s}

theorem initial_finite :
    initial.Finite := by
  exact Set.toFinite _

/-- Exact language theorem for the binarized Lukasiewicz grammar. -/
theorem initial_language_eq :
    InitialSetLanguage binaryGrammar initial =
      Language := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨A, hA, d⟩
    have hAs : A = GrammarNT.s := hA
    subst A
    exact
      (paperDerives_iff_language w).1
        (binaryDerives_shape d)
  · intro hw
    exact
      ⟨GrammarNT.s, rfl,
        paperDerives_to_binary
          ((paperDerives_iff_language w).2 hw)⟩

/--
Explicit context-free witness for the language used in the fixed-word
quotient boundary argument.
-/
theorem finite_cfg_witness :
    initial.Finite ∧
      InitialSetLanguage
        binaryGrammar initial =
      Language := by
  exact
    ⟨initial_finite,
      initial_language_eq⟩

/--
Section 9 boundary package: the Lukasiewicz language has an explicit finite
CFG presentation but is not fixed-h substitutable for the supplied arbitrary
finite-monoid typing.
-/
theorem finite_cfg_but_not_fixedH
    {M : Type*} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom
      DyckOne.Symbol M) :
    (initial.Finite ∧
      InitialSetLanguage
        binaryGrammar initial =
      Language)
      ∧
    ¬ FixedHSubstitutable H Language := by
  exact
    ⟨finite_cfg_witness,
      Lukasiewicz.not_fixedH H⟩

end Lukasiewicz
end TCS1
end LeanCfgProject
