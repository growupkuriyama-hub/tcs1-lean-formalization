import LeanCfgProject.TCS1.DeltaStarDisplayedGrammar
import LeanCfgProject.TCS1.ClarkCongruentialPackaging

/-!
# TCS #1 v78: finite binary CFG witness for Delta-star

This file realizes the displayed grammar

  S -> T S | epsilon
  T -> a T b | epsilon

inside the repository's generic BinaryNullableGrammar semantics.  The
terminal wrappers A,B and one auxiliary state X give the finite binarization

  S -> T S | epsilon
  T -> A X | epsilon
  X -> T B
  A -> a
  B -> b.

The initial language is proved exactly equal to DeltaStar.Language.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- Five nonterminals for the finite binary presentation. -/
inductive GrammarNT where
  | s
  | t
  | ta
  | tb
  | x
  deriving DecidableEq, Fintype, Repr

/-- Terminal wrappers A -> a and B -> b. -/
inductive GrammarTerminalRule :
    GrammarNT → Symbol → Prop
  | ta_a :
      GrammarTerminalRule .ta a
  | tb_b :
      GrammarTerminalRule .tb b

/-- Binary rules S -> T S, T -> A X, and X -> T B. -/
inductive GrammarBinaryRule :
    GrammarNT → GrammarNT → GrammarNT → Prop
  | s_ts :
      GrammarBinaryRule .s .t .s
  | t_ax :
      GrammarBinaryRule .t .ta .x
  | x_tb :
      GrammarBinaryRule .x .t .tb

/-- Nullable rules S -> epsilon and T -> epsilon. -/
inductive GrammarEpsilonRule :
    GrammarNT → Prop
  | s_eps :
      GrammarEpsilonRule .s
  | t_eps :
      GrammarEpsilonRule .t

/-- Explicit finite binary CFG for Delta-star. -/
def binaryGrammar :
    BinaryNullableGrammar GrammarNT Symbol where
  terminalRule := GrammarTerminalRule
  binaryRule := GrammarBinaryRule
  epsilonRule := GrammarEpsilonRule
  unitRule _ _ := False

/-- Closed semantic description of each binary nonterminal language. -/
def BinaryShape :
    GrammarNT → Word Symbol → Prop
  | .s, w =>
      SDerives w
  | .t, w =>
      TDerives w
  | .ta, w =>
      w = [a]
  | .tb, w =>
      w = [b]
  | .x, w =>
      ∃ u : Word Symbol,
        TDerives u ∧
        w = u ++ [b]

/-- Every binary derivation has the advertised displayed-grammar shape. -/
theorem binaryDerives_shape
    {A : GrammarNT}
    {w : Word Symbol}
    (d :
      BinaryNullableDerives
        binaryGrammar A w) :
    BinaryShape A w := by
  induction d with
  | terminal h =>
      change GrammarTerminalRule _ _ at h
      cases h with
      | ta_a =>
          rfl
      | tb_b =>
          rfl
  | epsilon h =>
      change GrammarEpsilonRule _ at h
      cases h with
      | s_eps =>
          exact SDerives.epsilon
      | t_eps =>
          exact TDerives.epsilon
  | unit h d ih =>
      exact False.elim h
  | @binary A B C wB wC h dB dC ihB ihC =>
      change GrammarBinaryRule A B C at h
      cases h with
      | s_ts =>
          change TDerives wB at ihB
          change SDerives wC at ihC
          exact SDerives.concat ihB ihC
      | t_ax =>
          change wB = [a] at ihB
          change
            ∃ u : Word Symbol,
              TDerives u ∧
              wC = u ++ [b] at ihC
          rcases ihC with ⟨u, hu, rfl⟩
          subst wB
          change TDerives ([a] ++ (u ++ [b]))
          simpa [List.append_assoc] using
            TDerives.wrap hu
      | x_tb =>
          change TDerives wB at ihB
          change wC = [b] at ihC
          subst wC
          exact ⟨wB, ihB, rfl⟩

/-- Every displayed T-derivation is realized by the binary grammar. -/
theorem tDerives_to_binary
    {w : Word Symbol}
    (d : TDerives w) :
    BinaryNullableDerives
      binaryGrammar .t w := by
  induction d with
  | epsilon =>
      exact
        BinaryNullableDerives.epsilon
          GrammarEpsilonRule.t_eps
  | @wrap w d ih =>
      have da :
          BinaryNullableDerives
            binaryGrammar .ta [a] :=
        BinaryNullableDerives.terminal
          GrammarTerminalRule.ta_a
      have db :
          BinaryNullableDerives
            binaryGrammar .tb [b] :=
        BinaryNullableDerives.terminal
          GrammarTerminalRule.tb_b
      have dx :
          BinaryNullableDerives
            binaryGrammar .x (w ++ [b]) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.x_tb ih db
      have dt :
          BinaryNullableDerives
            binaryGrammar .t
            ([a] ++ (w ++ [b])) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.t_ax da dx
      simpa [List.append_assoc] using dt

/-- Every displayed S-derivation is realized by the binary grammar. -/
theorem sDerives_to_binary
    {w : Word Symbol}
    (d : SDerives w) :
    BinaryNullableDerives
      binaryGrammar .s w := by
  induction d with
  | epsilon =>
      exact
        BinaryNullableDerives.epsilon
          GrammarEpsilonRule.s_eps
  | @concat x y dx dy ih =>
      exact
        BinaryNullableDerives.binary
          GrammarBinaryRule.s_ts
          (tDerives_to_binary dx)
          ih

/-- The initial set consists only of S. -/
def initial : Set GrammarNT :=
  {A | A = .s}

theorem initial_finite :
    initial.Finite := by
  exact Set.toFinite _

/-- Exact language theorem for the finite binary CFG. -/
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
      (displayedDerives_iff_language w).1
        (binaryDerives_shape d)
  · intro hw
    exact
      ⟨GrammarNT.s, rfl,
        sDerives_to_binary
          ((displayedDerives_iff_language w).2 hw)⟩

/-- Concrete finite-CFG witness for the context-free clause of Proposition 9.1. -/
theorem finite_cfg_witness :
    initial.Finite ∧
      InitialSetLanguage
        binaryGrammar initial =
      Language := by
  exact ⟨initial_finite, initial_language_eq⟩

end DeltaStar
end TCS1
end LeanCfgProject
