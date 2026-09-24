import Mathlib.Combinatorics.Enumerative.DyckWord
import LeanCfgProject.TCS1.DyckOneBracketKernel
import LeanCfgProject.TCS1.ClarkCongruentialPackaging

/-!
# TCS #1 v78: one-bracket Dyck congruential grammar

This module completes the properness witness in Proposition 9.9.  The paper
uses the one-nonterminal grammar S -> a S b S | epsilon.  Our generic Clark
packaging interface is binary, so we give the standard finite binarization
with terminal wrappers A,B and two auxiliary states X,Y.

The proof has three layers:

* the deterministic scan language is converted to Mathlib's DyckWord, whose
  first-return decomposition supplies the usual S -> a S b S recursion;
* the recursive one-nonterminal semantics is shown equivalent to the finite
  binary grammar; and
* every binary-grammar nonterminal language is shown to lie in one syntactic
  congruence class of D1.

Together with DyckOne.not_fixedH, this gives the two sides of the strictness
example: D1 is congruential but outside every fixed finite-monoid
substitutability class.
-/

namespace LeanCfgProject
namespace TCS1
namespace DyckOne

open Symbol
open DyckStep

/-- Encode the paper alphabet into Mathlib's U/D alphabet. -/
def encodeStep : Symbol → DyckStep
  | a => U
  | b => D

/-- Decode Mathlib's U/D alphabet back to the paper alphabet. -/
def decodeStep : DyckStep → Symbol
  | U => a
  | D => b

@[simp] theorem decode_encode (s : Symbol) :
    decodeStep (encodeStep s) = s := by
  cases s <;> rfl

@[simp] theorem encode_decode (s : DyckStep) :
    encodeStep (decodeStep s) = s := by
  cases s <;> rfl

@[simp] theorem count_U_encode
    (w : Word Symbol) :
    (w.map encodeStep).count U = w.count a := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s <;> simp [encodeStep, ih]

@[simp] theorem count_D_encode
    (w : Word Symbol) :
    (w.map encodeStep).count D = w.count b := by
  induction w with
  | nil =>
      simp
  | cons s w ih =>
      cases s <;> simp [encodeStep, ih]

theorem take_map_encode
    (w : Word Symbol)
    (i : Nat) :
    (w.map encodeStep).take i =
      (w.take i).map encodeStep := by
  induction w generalizing i with
  | nil =>
      simp
  | cons s w ih =>
      cases i with
      | zero =>
          rfl
      | succ i =>
          change
            encodeStep s :: (w.map encodeStep).take i =
              encodeStep s :: (w.take i).map encodeStep
          rw [ih]

/-- Successful scanning gives the expected global balance equation. -/
theorem scan_count_balance
    {h k : Nat}
    {w : Word Symbol}
    (hw : scan h w = some k) :
    k + w.count b = h + w.count a := by
  induction w generalizing h k with
  | nil =>
      simp [scan] at hw
      subst k
      simp
  | cons s w ih =>
      cases s with
      | a =>
          simp only [scan] at hw
          have hi :=
            ih (h := h + 1) (k := k) hw
          simp at hi ⊢
          omega
      | b =>
          cases h with
          | zero =>
              simp [scan] at hw
          | succ h =>
              simp only [scan] at hw
              have hi :=
                ih (h := h) (k := k) hw
              simp at hi ⊢
              omega

/--
Successful scanning also gives the prefix inequality at every cut position.
-/
theorem scan_prefix_safe
    {h k : Nat}
    {w : Word Symbol}
    (hw : scan h w = some k) :
    ∀ i : Nat,
      (w.take i).count b ≤
        h + (w.take i).count a := by
  induction w generalizing h k with
  | nil =>
      intro i
      simp
  | cons s w ih =>
      intro i
      cases i with
      | zero =>
          simp
      | succ i =>
          cases s with
          | a =>
              simp only [scan] at hw
              have hi :=
                ih (h := h + 1) (k := k) hw i
              simp at hi ⊢
              omega
          | b =>
              cases h with
              | zero =>
                  simp [scan] at hw
              | succ h =>
                  simp only [scan] at hw
                  have hi :=
                    ih (h := h) (k := k) hw i
                  simp at hi ⊢
                  omega

/--
Every word accepted by the deterministic scanner canonically determines a
Mathlib DyckWord.
-/
def asMathlibDyckWord
    {w : Word Symbol}
    (hw : w ∈ Language) :
    DyckWord where
  toList := w.map encodeStep
  count_U_eq_count_D := by
    have hb :=
      scan_count_balance
        (show scan 0 w = some 0 from hw)
    simpa using hb.symm
  count_D_le_count_U i := by
    have hp :=
      scan_prefix_safe
        (show scan 0 w = some 0 from hw)
        i
    rw [take_map_encode w i]
    simpa only [count_D_encode, count_U_encode,
      Nat.zero_add] using hp

/-- Decode a Mathlib Dyck word to the paper alphabet. -/
def decodeWord (p : DyckWord) : Word Symbol :=
  p.toList.map decodeStep

@[simp] theorem decodeWord_zero :
    decodeWord (0 : DyckWord) = [] := by
  rfl

@[simp] theorem decodeWord_add
    (p q : DyckWord) :
    decodeWord (p + q) =
      decodeWord p ++ decodeWord q := by
  change
    (p.toList ++ q.toList).map decodeStep =
      p.toList.map decodeStep ++
        q.toList.map decodeStep
  simp only [List.map_append]

@[simp] theorem decodeWord_nest
    (p : DyckWord) :
    decodeWord p.nest =
      a :: decodeWord p ++ [b] := by
  simp [decodeWord, DyckWord.nest,
    List.map_append, decodeStep,
    List.append_assoc]

@[simp] theorem decode_asMathlibDyckWord
    {w : Word Symbol}
    (hw : w ∈ Language) :
    decodeWord (asMathlibDyckWord hw) = w := by
  simp [decodeWord, asMathlibDyckWord,
    List.map_map, Function.comp_def]

/--
Direct semantics of the paper's one-nonterminal grammar
S -> a S b S | epsilon.
-/
inductive PaperDerives : Word Symbol → Prop
  | epsilon :
      PaperDerives []
  | branch
      {x y : Word Symbol}
      (dx : PaperDerives x)
      (dy : PaperDerives y) :
      PaperDerives (a :: x ++ b :: y)

/--
Mathlib's first-return decomposition gives a derivation in the paper grammar.
-/
theorem mathlibDyckWord_to_paperDerives
    (p : DyckWord) :
    PaperDerives (decodeWord p) := by
  by_cases hp : p = 0
  · subst p
    simpa using PaperDerives.epsilon
  · have hi :=
      mathlibDyckWord_to_paperDerives p.insidePart
    have ho :=
      mathlibDyckWord_to_paperDerives p.outsidePart
    rw [← p.nest_insidePart_add_outsidePart hp]
    simpa [List.append_assoc] using
      PaperDerives.branch hi ho
termination_by p.semilength
decreasing_by
  · exact p.semilength_insidePart_lt hp
  · exact p.semilength_outsidePart_lt hp

/-- Every scanner-accepted Dyck word has the paper-grammar derivation. -/
theorem language_to_paperDerives
    {w : Word Symbol}
    (hw : w ∈ Language) :
    PaperDerives w := by
  have hd :=
    mathlibDyckWord_to_paperDerives
      (asMathlibDyckWord hw)
  simpa using hd

/-- Every paper-grammar derivation is accepted by the deterministic scanner. -/
theorem paperDerives_to_language
    {w : Word Symbol}
    (d : PaperDerives w) :
    w ∈ Language := by
  induction d with
  | epsilon =>
      exact nil_mem
  | @branch x y dx dy ihx ihy =>
      change
        scan 1 (x ++ b :: y) = some 0
      rw [scan_append,
        scan_dyck_at_height ihx 1]
      simpa [scan] using ihy

theorem paperDerives_iff_language
    (w : Word Symbol) :
    PaperDerives w ↔ w ∈ Language :=
  ⟨paperDerives_to_language,
    language_to_paperDerives⟩

/-- Five nonterminals of a binary presentation of S -> a S b S | epsilon. -/
inductive GrammarNT where
  | s
  | ta
  | tb
  | x
  | y
  deriving DecidableEq, Fintype, Repr

/-- Two terminal wrapper rules. -/
inductive GrammarTerminalRule :
    GrammarNT → Symbol → Prop
  | aRule :
      GrammarTerminalRule .ta a
  | bRule :
      GrammarTerminalRule .tb b

/-- Three binary rules implementing S -> a S b S. -/
inductive GrammarBinaryRule :
    GrammarNT → GrammarNT → GrammarNT → Prop
  | sRule :
      GrammarBinaryRule .s .ta .x
  | xRule :
      GrammarBinaryRule .x .s .y
  | yRule :
      GrammarBinaryRule .y .tb .s

/-- Finite binary CFG for D1. -/
def binaryGrammar :
    BinaryNullableGrammar GrammarNT Symbol where
  terminalRule := GrammarTerminalRule
  binaryRule := GrammarBinaryRule
  epsilonRule A := A = .s
  unitRule _ _ := False

/-- Closed forms for all five nonterminal languages. -/
def BinaryShape :
    GrammarNT → Word Symbol → Prop
  | .s, w =>
      PaperDerives w
  | .ta, w =>
      w = [a]
  | .tb, w =>
      w = [b]
  | .y, w =>
      ∃ z : Word Symbol,
        PaperDerives z ∧
        w = b :: z
  | .x, w =>
      ∃ z₁ z₂ : Word Symbol,
        PaperDerives z₁ ∧
        PaperDerives z₂ ∧
        w = z₁ ++ b :: z₂

/-- Every binary-grammar derivation has its advertised closed form. -/
theorem binaryDerives_shape
    {A : GrammarNT}
    {w : Word Symbol}
    (d :
      BinaryNullableDerives binaryGrammar A w) :
    BinaryShape A w := by
  induction d with
  | terminal h =>
      change GrammarTerminalRule _ _ at h
      cases h <;> rfl
  | @epsilon A h =>
      change A = GrammarNT.s at h
      subst A
      exact PaperDerives.epsilon
  | unit h d ih =>
      exact False.elim h
  | @binary A B C wB wC h dB dC ihB ihC =>
      change GrammarBinaryRule A B C at h
      cases h with
      | sRule =>
          change wB = [a] at ihB
          change
            ∃ z₁ z₂ : Word Symbol,
              PaperDerives z₁ ∧
              PaperDerives z₂ ∧
              wC = z₁ ++ b :: z₂ at ihC
          rcases ihC with
            ⟨z₁, z₂, hz₁, hz₂, rfl⟩
          subst wB
          change
            PaperDerives
              ([a] ++ (z₁ ++ b :: z₂))
          simpa [List.append_assoc] using
            PaperDerives.branch hz₁ hz₂
      | xRule =>
          change PaperDerives wB at ihB
          change
            ∃ z : Word Symbol,
              PaperDerives z ∧
              wC = b :: z at ihC
          rcases ihC with
            ⟨z, hz, rfl⟩
          exact
            ⟨wB, z, ihB, hz, rfl⟩
      | yRule =>
          change wB = [b] at ihB
          change PaperDerives wC at ihC
          subst wB
          exact ⟨wC, ihC, rfl⟩

/-- Every paper derivation is realized from S in the finite binary grammar. -/
theorem paperDerives_to_binary
    {w : Word Symbol}
    (d : PaperDerives w) :
    BinaryNullableDerives binaryGrammar .s w := by
  induction d with
  | epsilon =>
      exact BinaryNullableDerives.epsilon rfl
  | @branch x y dx dy ihx ihy =>
      have da :
          BinaryNullableDerives
            binaryGrammar .ta [a] :=
        BinaryNullableDerives.terminal
          GrammarTerminalRule.aRule
      have db :
          BinaryNullableDerives
            binaryGrammar .tb [b] :=
        BinaryNullableDerives.terminal
          GrammarTerminalRule.bRule
      have dY :
          BinaryNullableDerives
            binaryGrammar .y ([b] ++ y) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.yRule db ihy
      have dX :
          BinaryNullableDerives
            binaryGrammar .x
            (x ++ ([b] ++ y)) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.xRule ihx dY
      have dS :
          BinaryNullableDerives
            binaryGrammar .s
            ([a] ++ (x ++ ([b] ++ y))) :=
        BinaryNullableDerives.binary
          GrammarBinaryRule.sRule da dX
      simpa [List.append_assoc] using dS

/-- Single initial symbol S. -/
def initial : Set GrammarNT :=
  {A | A = .s}

theorem initial_finite :
    initial.Finite := by
  exact Set.toFinite _

/-- The finite binary grammar generates exactly D1. -/
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
      paperDerives_to_language
        (binaryDerives_shape d)
  · intro hw
    exact
      ⟨GrammarNT.s, rfl,
        paperDerives_to_binary
          (language_to_paperDerives hw)⟩

/-- Appending a Dyck factor to a fragment does not change its distribution. -/
theorem distribution_suffix_neutral
    {x : Word Symbol}
    (hx : x ∈ Language)
    (r : Word Symbol) :
    Distribution Language (r ++ x) =
      Distribution Language r := by
  apply Set.ext
  rintro ⟨u, v⟩
  change
    (u ++ (r ++ x) ++ v ∈ Language) ↔
      (u ++ r ++ v ∈ Language)
  simpa [List.append_assoc] using
    insert_neutral hx (u ++ r) v

/-- Prepending a Dyck factor to a fragment does not change its distribution. -/
theorem distribution_prefix_neutral
    {x : Word Symbol}
    (hx : x ∈ Language)
    (r : Word Symbol) :
    Distribution Language (x ++ r) =
      Distribution Language r := by
  apply Set.ext
  rintro ⟨u, v⟩
  change
    (u ++ (x ++ r) ++ v ∈ Language) ↔
      (u ++ r ++ v ∈ Language)
  simpa [List.append_assoc] using
    insert_neutral hx u (r ++ v)

/--
The finite binary grammar is congruential in Clark's sense.
-/
theorem binaryGrammar_congruential :
    ClarkCongruentialInitialSet
      binaryGrammar initial := by
  intro A x y dx dy
  rw [initial_language_eq]
  have hxShape :=
    binaryDerives_shape dx
  have hyShape :=
    binaryDerives_shape dy
  cases A with
  | s =>
      have hxL :
          x ∈ Language :=
        paperDerives_to_language hxShape
      have hyL :
          y ∈ Language :=
        paperDerives_to_language hyShape
      calc
        Distribution Language x =
            Distribution Language
              ([] : Word Symbol) :=
          member_distribution_eq_nil hxL
        _ =
            Distribution Language y :=
          (member_distribution_eq_nil hyL).symm
  | ta =>
      change x = [a] at hxShape
      change y = [a] at hyShape
      subst x
      subst y
      rfl
  | tb =>
      change x = [b] at hxShape
      change y = [b] at hyShape
      subst x
      subst y
      rfl
  | y =>
      change
        ∃ z : Word Symbol,
          PaperDerives z ∧ x = b :: z at hxShape
      change
        ∃ z : Word Symbol,
          PaperDerives z ∧ y = b :: z at hyShape
      rcases hxShape with
        ⟨zx, hzx, rfl⟩
      rcases hyShape with
        ⟨zy, hzy, rfl⟩
      have hxL :
          zx ∈ Language :=
        paperDerives_to_language hzx
      have hyL :
          zy ∈ Language :=
        paperDerives_to_language hzy
      calc
        Distribution Language (b :: zx) =
            Distribution Language [b] := by
          simpa using
            distribution_suffix_neutral hxL [b]
        _ =
            Distribution Language (b :: zy) := by
          simpa using
            (distribution_suffix_neutral hyL [b]).symm
  | x =>
      change
        ∃ z₁ z₂ : Word Symbol,
          PaperDerives z₁ ∧
          PaperDerives z₂ ∧
          x = z₁ ++ b :: z₂ at hxShape
      change
        ∃ z₁ z₂ : Word Symbol,
          PaperDerives z₁ ∧
          PaperDerives z₂ ∧
          y = z₁ ++ b :: z₂ at hyShape
      rcases hxShape with
        ⟨x₁, x₂, hx₁, hx₂, rfl⟩
      rcases hyShape with
        ⟨y₁, y₂, hy₁, hy₂, rfl⟩
      have hx₁L :
          x₁ ∈ Language :=
        paperDerives_to_language hx₁
      have hx₂L :
          x₂ ∈ Language :=
        paperDerives_to_language hx₂
      have hy₁L :
          y₁ ∈ Language :=
        paperDerives_to_language hy₁
      have hy₂L :
          y₂ ∈ Language :=
        paperDerives_to_language hy₂
      calc
        Distribution Language (x₁ ++ b :: x₂) =
            Distribution Language (x₁ ++ [b]) := by
          simpa [List.append_assoc] using
            distribution_suffix_neutral
              hx₂L (x₁ ++ [b])
        _ =
            Distribution Language [b] :=
          distribution_prefix_neutral hx₁L [b]
        _ =
            Distribution Language (y₁ ++ [b]) :=
          (distribution_prefix_neutral hy₁L [b]).symm
        _ =
            Distribution Language (y₁ ++ b :: y₂) := by
          simpa [List.append_assoc] using
            (distribution_suffix_neutral
              hy₂L (y₁ ++ [b])).symm

/--
Finite congruential witness for D1.
-/
theorem congruential_witness :
    initial.Finite
      ∧
    InitialSetLanguage binaryGrammar initial =
      Language
      ∧
    ClarkCongruentialInitialSet
      binaryGrammar initial := by
  exact
    ⟨initial_finite,
      initial_language_eq,
      binaryGrammar_congruential⟩

/--
Properness kernel used at the end of Proposition 9.9: D1 has a finite
congruential grammar, yet it is not substitutable for the supplied arbitrary
finite-monoid typing.
-/
theorem congruential_but_not_fixedH
    {M : Type*} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Symbol M) :
    (initial.Finite
      ∧
      InitialSetLanguage binaryGrammar initial =
        Language
      ∧
      ClarkCongruentialInitialSet
        binaryGrammar initial)
      ∧
    ¬ FixedHSubstitutable H Language := by
  exact
    ⟨congruential_witness,
      not_fixedH H⟩

end DyckOne
end TCS1
end LeanCfgProject
