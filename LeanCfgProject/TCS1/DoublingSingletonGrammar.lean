import LeanCfgProject.TCS1.SingletonDataLowerBound
import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1 v79: the linear-size doubling grammar lower-bound witness

Section 6 uses the family

  S₀ → Aₙ,
  A₀ → a,
  Aᵢ → Aᵢ₋₁ Aᵢ₋₁

to show that arbitrary CFG representation size alone cannot polynomially bound
positive characteristic data.  This module formalizes that witness over the
one-letter alphabet Unit.

The grammar has one start state and n+1 layer states.  Its productions consist
of one start-unit rule, one terminal rule, and n binary doubling rules.  Thus
its production-symbol count is linear in n.  Nevertheless the start language
is exactly the singleton {a^(2^n)}.  Combining this with
`SingletonDataLowerBound` forces every positive characteristic sample to
contain a word of length 2^n.
-/

namespace LeanCfgProject
namespace TCS1

section DoublingSingletonGrammar

/-- One start state plus layer states A_0,...,A_n. -/
abbrev DoublingState (n : Nat) :=
  Option (Fin (n + 1))

/-- The layer A_0. -/
def doublingZeroState (n : Nat) : DoublingState n :=
  some ⟨0, by omega⟩

/-- The top layer A_n. -/
def doublingTopState (n : Nat) : DoublingState n :=
  some ⟨n, by omega⟩

/-- Child layer A_i associated with binary-rule index i < n. -/
def doublingChildState
    {n : Nat}
    (i : Fin n) :
    DoublingState n :=
  some ⟨i.1, by omega⟩

/-- Parent layer A_(i+1) associated with binary-rule index i < n. -/
def doublingParentState
    {n : Nat}
    (i : Fin n) :
    DoublingState n :=
  some ⟨i.1 + 1, by omega⟩

/-- The concrete layer A_k for k <= n. -/
def doublingLayerState
    (n k : Nat)
    (hk : k ≤ n) :
    DoublingState n :=
  some ⟨k, by omega⟩

/--
Finite binary/unit grammar corresponding exactly to the displayed doubling
family.  None is S₀ and some i is A_i.
-/
def doublingGrammar
    (n : Nat) :
    BinaryNullableGrammar (DoublingState n) Unit where
  terminalRule A _ :=
    A = doublingZeroState n
  binaryRule A B C :=
    ∃ i : Fin n,
      A = doublingParentState i ∧
      B = doublingChildState i ∧
      C = doublingChildState i
  epsilonRule _ := False
  unitRule A B :=
    A = none ∧ B = doublingTopState n

/-- A finite index set for the one unit, one terminal, and n binary rules. -/
abbrev DoublingProductionIndex
    (n : Nat) :=
  Unit ⊕ (Unit ⊕ Fin n)

/-- The grammar has exactly n+2 productions. -/
@[simp] theorem doublingProductionIndex_card
    (n : Nat) :
    Fintype.card (DoublingProductionIndex n) = n + 2 := by
  simp [DoublingProductionIndex]
  omega

/-- The state universe has n+2 states: S₀ and A_0,...,A_n. -/
@[simp] theorem doublingState_card
    (n : Nat) :
    Fintype.card (DoublingState n) = n + 2 := by
  simp [DoublingState]

/--
Production-symbol count (one LHS plus RHS symbols):
2 for S₀→A_n, 2 for A₀→a, and 3 for each binary rule.
-/
def doublingProductionSymbolCount
    (n : Nat) : Nat :=
  4 + 3 * n

theorem doublingProductionSymbolCount_linear
    (n : Nat) :
    doublingProductionSymbolCount n ≤ 3 * (n + 2) := by
  unfold doublingProductionSymbolCount
  omega

/--
A simple explicit encoding scale consisting of the finite-state count plus
the production-symbol count.
-/
def doublingGrammarEncodingScale
    (n : Nat) : Nat :=
  Fintype.card (DoublingState n) +
    doublingProductionSymbolCount n

/-- The displayed family has a literally linear encoding scale 4n+6. -/
theorem doublingGrammarEncodingScale_eq
    (n : Nat) :
    doublingGrammarEncodingScale n = 4 * n + 6 := by
  unfold doublingGrammarEncodingScale
  rw [doublingState_card]
  unfold doublingProductionSymbolCount
  omega

/-- Intended yield length of each grammar state. -/
def doublingStateWeight
    (n : Nat) :
    DoublingState n → Nat
  | none => 2 ^ n
  | some i => 2 ^ i.1

/-- Every successful derivation has exactly the intended power-of-two length. -/
theorem doublingGrammar_derives_length
    (n : Nat)
    {A : DoublingState n}
    {w : Word Unit}
    (d : BinaryNullableDerives (doublingGrammar n) A w) :
    w.length = doublingStateWeight n A := by
  induction d with
  | @terminal A a h =>
      change A = doublingZeroState n at h
      subst A
      simp [doublingStateWeight, doublingZeroState]
  | @epsilon A h =>
      change False at h
      exact False.elim h
  | @unit A B w h d ih =>
      change A = none ∧ B = doublingTopState n at h
      rcases h with ⟨rfl, rfl⟩
      simpa [doublingStateWeight, doublingTopState] using ih
  | @binary A B C wB wC h dB dC ihB ihC =>
      change
        ∃ i : Fin n,
          A = doublingParentState i ∧
          B = doublingChildState i ∧
          C = doublingChildState i
        at h
      rcases h with ⟨i, rfl, rfl, rfl⟩
      simp only [List.length_append]
      rw [ihB, ihC]
      simp [doublingStateWeight,
        doublingParentState, doublingChildState,
        pow_succ, Nat.mul_two]

/-- A word over Unit is completely determined by its length. -/
theorem unitWord_eq_replicate_length
    (w : Word Unit) :
    w = List.replicate w.length () := by
  induction w with
  | nil =>
      rfl
  | cons a w ih =>
      cases a
      simp only [List.length_cons]
      rw [List.replicate_succ]
      exact congrArg (fun t => () :: t) ih

/-- Each layer A_k derives its intended unary word of length 2^k. -/
theorem doublingLayer_derives
    (n k : Nat)
    (hk : k ≤ n) :
    BinaryNullableDerives
      (doublingGrammar n)
      (doublingLayerState n k hk)
      (List.replicate (2 ^ k) ()) := by
  induction k with
  | zero =>
      apply BinaryNullableDerives.terminal
      simp [doublingGrammar,
        doublingLayerState, doublingZeroState]
  | succ k ih =>
      have hkprev : k ≤ n := by omega
      have hkn : k < n := by omega
      let i : Fin n := ⟨k, hkn⟩
      have dchild :=
        ih hkprev
      have hbin :
          (doublingGrammar n).binaryRule
            (doublingLayerState n (k + 1) hk)
            (doublingLayerState n k hkprev)
            (doublingLayerState n k hkprev) := by
        refine ⟨i, ?_, ?_, ?_⟩
        · exact congrArg some (Fin.ext rfl)
        · exact congrArg some (Fin.ext rfl)
        · exact congrArg some (Fin.ext rfl)
      have d :=
        BinaryNullableDerives.binary
          hbin dchild dchild
      have hpow :
          2 ^ (k + 1) =
            2 ^ k + 2 ^ k := by
        rw [pow_succ]
        omega
      rw [hpow, List.replicate_add]
      exact d

/-- The start state S₀ derives a^(2^n). -/
theorem doublingStart_derives
    (n : Nat) :
    BinaryNullableDerives
      (doublingGrammar n)
      none
      (doublingWord () n) := by
  apply BinaryNullableDerives.unit
      (B := doublingTopState n)
  · exact ⟨rfl, rfl⟩
  · simpa [doublingWord, doublingTopState,
      doublingLayerState] using
      (doublingLayer_derives n n le_rfl)

/-- Start language of the doubling grammar. -/
def doublingStartLanguage
    (n : Nat) :
    Set (Word Unit) :=
  {w |
    BinaryNullableDerives
      (doublingGrammar n) none w}

/-- The displayed grammar generates exactly the singleton {a^(2^n)}. -/
theorem doublingStartLanguage_eq_singleton
    (n : Nat) :
    doublingStartLanguage n =
      ({doublingWord () n} : Set (Word Unit)) := by
  apply Set.ext
  intro w
  constructor
  · intro dw
    have hlen :
        w.length = 2 ^ n := by
      have h :=
        doublingGrammar_derives_length
          n dw
      simpa [doublingStateWeight] using h
    have hw :
        w = doublingWord () n := by
      calc
        w = List.replicate w.length () :=
          unitWord_eq_replicate_length w
        _ = List.replicate (2 ^ n) () := by
          rw [hlen]
        _ = doublingWord () n := by
          rfl
    simpa [hw]
  · intro hw
    have hEq :
        w = doublingWord () n := by
      simpa using hw
    subst w
    exact doublingStart_derives n

/-- The doubling target lies in every fixed-h substitutable class. -/
theorem doublingStartLanguage_fixedHSubstitutable
    {M : Type*} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Unit M)
    (n : Nat) :
    FixedHSubstitutable H
      (doublingStartLanguage n) := by
  rw [doublingStartLanguage_eq_singleton]
  exact singleton_fixedHSubstitutable
    H (doublingWord () n)

/--
Any positive characteristic sample for the language of the linear-size
doubling grammar has encoded norm at least 2^n+1.
-/
theorem doublingGrammar_characteristic_norm_ge
    {M : Type*} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Unit M)
    (n : Nat)
    (C : Finset (Word Unit))
    (hpositive :
      (↑C : Set (Word Unit)) ⊆
        doublingStartLanguage n)
    (hcharacteristic :
      BatchLanguage H C =
        doublingStartLanguage n) :
    2 ^ n + 1 ≤ reconstructionSampleNorm C := by
  rw [doublingStartLanguage_eq_singleton n] at hpositive hcharacteristic
  exact
    singleton_doubling_characteristic_norm_ge
      H () n C hpositive hcharacteristic

/--
Paper-facing Section 6 obstruction package: a linear-size grammar in every
fixed-h target class whose positive characteristic data must contain an
exponentially long word.
-/
theorem grammarSizeOnlyDataBound_obstruction
    {M : Type*} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Unit M)
    (n : Nat) :
    doublingGrammarEncodingScale n = 4 * n + 6
      ∧
    doublingStartLanguage n =
      ({doublingWord () n} : Set (Word Unit))
      ∧
    FixedHSubstitutable H
      (doublingStartLanguage n)
      ∧
    ∀ C : Finset (Word Unit),
      (↑C : Set (Word Unit)) ⊆
          doublingStartLanguage n →
      BatchLanguage H C =
          doublingStartLanguage n →
      2 ^ n + 1 ≤ reconstructionSampleNorm C := by
  refine
    ⟨doublingGrammarEncodingScale_eq n,
      doublingStartLanguage_eq_singleton n,
      doublingStartLanguage_fixedHSubstitutable H n,
      ?_⟩
  intro C hpos hchar
  exact
    doublingGrammar_characteristic_norm_ge
      H n C hpos hchar

end DoublingSingletonGrammar

end TCS1
end LeanCfgProject
