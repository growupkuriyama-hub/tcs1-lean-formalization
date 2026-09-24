import LeanCfgProject.TCS1.TerminalIsolationKernel

/-!
# TCS #1 v65: general CFG derivation semantics

This module adds an explicit parse-tree semantics for arbitrary mixed
context-free right-hand sides. It is the bridge needed to lift the local
terminal-isolation and binarization equivalences to full generated-language
equivalences.

A rule derivation and the derivation of the symbols in its right-hand side
are defined mutually. Terminal symbols contribute their singleton word;
nonterminal symbols contribute the yield of a recursively derived subtree.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section GeneralCFGDerivation

variable {N : Type u}
variable {α : Type v}

mutual

/-- Successful derivation of a terminal word from one nonterminal. -/
inductive MixedDerives
    (R : MixedRules N α) :
    N → List α → Prop
  | rule
      {A : N}
      {rhs : List (MixedSymbol N α)}
      {pieces : List (List α)}
      (hR : R A rhs)
      (hpieces : MixedSymbolsDerive R rhs pieces) :
      MixedDerives R A pieces.flatten

/-- Aligned successful derivations of all symbols in one right-hand side. -/
inductive MixedSymbolsDerive
    (R : MixedRules N α) :
    List (MixedSymbol N α) →
      List (List α) → Prop
  | nil :
      MixedSymbolsDerive R [] []
  | terminal
      {a : α}
      {rhs : List (MixedSymbol N α)}
      {pieces : List (List α)}
      (tail : MixedSymbolsDerive R rhs pieces) :
      MixedSymbolsDerive R
        (Sum.inr a :: rhs)
        ([a] :: pieces)
  | nonterminal
      {A : N}
      {rhs : List (MixedSymbol N α)}
      {w : List α}
      {pieces : List (List α)}
      (head : MixedDerives R A w)
      (tail : MixedSymbolsDerive R rhs pieces) :
      MixedSymbolsDerive R
        (Sum.inl A :: rhs)
        (w :: pieces)

end

/-- A literal epsilon rule derives epsilon. -/
theorem mixedDerives_epsilon
    (R : MixedRules N α)
    {A : N}
    (h : R A []) :
    MixedDerives R A [] := by
  simpa using
    (MixedDerives.rule h (MixedSymbolsDerive.nil (R := R)))

/-- A literal terminal rule derives its one-letter word. -/
theorem mixedDerives_terminal
    (R : MixedRules N α)
    {A : N} {a : α}
    (h : R A [Sum.inr a]) :
    MixedDerives R A [a] := by
  have hs :
      MixedSymbolsDerive R [Sum.inr a] [[a]] :=
    MixedSymbolsDerive.terminal
      (MixedSymbolsDerive.nil (R := R))
  simpa using MixedDerives.rule h hs

/-- A unit rule transports a successful child derivation unchanged. -/
theorem mixedDerives_unit
    (R : MixedRules N α)
    {A B : N} {w : List α}
    (h : R A [Sum.inl B])
    (d : MixedDerives R B w) :
    MixedDerives R A w := by
  have hs :
      MixedSymbolsDerive R [Sum.inl B] [w] :=
    MixedSymbolsDerive.nonterminal d
      (MixedSymbolsDerive.nil (R := R))
  simpa using MixedDerives.rule h hs

/-- A binary nonterminal rule concatenates its two child yields. -/
theorem mixedDerives_binary
    (R : MixedRules N α)
    {A B C : N}
    {u v : List α}
    (h : R A [Sum.inl B, Sum.inl C])
    (dB : MixedDerives R B u)
    (dC : MixedDerives R C v) :
    MixedDerives R A (u ++ v) := by
  have hs :
      MixedSymbolsDerive R
        [Sum.inl B, Sum.inl C]
        [u, v] :=
    MixedSymbolsDerive.nonterminal dB
      (MixedSymbolsDerive.nonterminal dC
        (MixedSymbolsDerive.nil (R := R)))
  simpa using MixedDerives.rule h hs

/-- Generated terminal language of one nonterminal. -/
def MixedNonterminalLanguage
    (R : MixedRules N α)
    (A : N) :
    Set (List α) :=
  {w | MixedDerives R A w}

end GeneralCFGDerivation

end TCS1
end LeanCfgProject
