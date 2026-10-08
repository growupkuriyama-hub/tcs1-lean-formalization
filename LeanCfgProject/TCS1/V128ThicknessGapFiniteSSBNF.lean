import LeanCfgProject.TCS1.V128TypedTrimSuccessfulBranch
import LeanCfgProject.TCS1.V128ThicknessGapTypedFiber

/-!
# TCS #1 v128: actual finite SSBNF source for the exponential gap

The non-start grammar uses genuinely finite states U, D, E_0,...,E_n.
Its productions exactly match the v128 manuscript:
  U -> a | c | UU | E_n D
  D -> c
  E_0 -> a
  E_(i+1) -> E_i E_i | c
and the separate start has its unique rule S_0 -> U.

The E_i source derivation is translated from the checked E-branch model,
so the exponential h_c-unit witness actually occurs in a successful
typed binary derivation under the source grammar. The theorem
gapEN_unit_retained certifies that (E_n,1) survives the *concrete*
productive/reachable trimming, rather than merely postulating activity.

A separate reverse classification of all E_n yields and a formal
typed-thickness aggregate are still needed for the full proposition.
-/

namespace LeanCfgProject
namespace TCS1

/-- A genuinely finite non-start symbol type for the indexed source grammar. -/
inductive GapNonterminal (n : Nat) where
  | universal
  | marker
  | exponent (i : Fin (n + 1))
deriving DecidableEq, Fintype

/-- Exactly the terminal rules in the manuscript's gap grammar. -/
inductive GapTerminalRule (n : Nat) : GapNonterminal n → Bool → Prop
  | universalA : GapTerminalRule n .universal false
  | universalC : GapTerminalRule n .universal true
  | markerC : GapTerminalRule n .marker true
  | exponentA :
      GapTerminalRule n (.exponent ⟨0, Nat.zero_lt_succ n⟩) false
  | exponentC {i : Fin (n + 1)} (hi : 0 < i.val) :
      GapTerminalRule n (.exponent i) true

/-- Exactly the binary rules in the manuscript's gap grammar. -/
inductive GapBinaryRule (n : Nat) :
    GapNonterminal n → GapNonterminal n → GapNonterminal n → Prop
  | universalPair :
      GapBinaryRule n .universal .universal .universal
  | universalExp :
      GapBinaryRule n .universal
        (.exponent ⟨n, Nat.lt_succ_self n⟩) .marker
  | exponentPair {i j : Fin (n + 1)}
      (hstep : i.val = j.val + 1) :
      GapBinaryRule n (.exponent i) (.exponent j) (.exponent j)

/-- The unique start child is U. -/
def GapStartRule (n : Nat) (A : GapNonterminal n) : Prop :=
  A = .universal

/-- Translate every E_i derivation into the actual finite source grammar. -/
theorem exponentialBranch_to_gapUntyped (n : Nat)
    {i : Nat} {w : List Bool}
    (d : ExponentialBranchYield i w) :
    ∀ (hi : i ≤ n),
      UntypedDerives (GapTerminalRule n) (GapBinaryRule n)
        (.exponent ⟨i, Nat.lt_succ_of_le hi⟩) w := by
  induction d with
  | base =>
      intro _hi
      exact UntypedDerives.terminal GapTerminalRule.exponentA
  | @duplicate i u v du dv ihu ihv =>
      intro hi
      have hj : i ≤ n := by omega
      have hsplit :
          GapBinaryRule n
            (.exponent ⟨i + 1, Nat.lt_succ_of_le hi⟩)
            (.exponent ⟨i, Nat.lt_succ_of_le hj⟩)
            (.exponent ⟨i, Nat.lt_succ_of_le hj⟩) :=
        GapBinaryRule.exponentPair rfl
      exact UntypedDerives.binary hsplit (ihu hj) (ihv hj)
  | @reset i =>
      intro hi
      exact UntypedDerives.terminal
        (GapTerminalRule.exponentC
          (i := ⟨i + 1, Nat.lt_succ_of_le hi⟩) (by omega))

/-- The universal symbol U genuinely derives every nonempty Boolean word. -/
theorem gapUniversal_to_untyped (n : Nat)
    {w : List Bool}
    (d : GapUniversalYield n w) :
    UntypedDerives (GapTerminalRule n) (GapBinaryRule n)
      .universal w := by
  induction d with
  | letterA =>
      exact UntypedDerives.terminal GapTerminalRule.universalA
  | letterC =>
      exact UntypedDerives.terminal GapTerminalRule.universalC
  | combine _ _ ihU ihV =>
      exact UntypedDerives.binary GapBinaryRule.universalPair ihU ihV
  | exponentialBranch de =>
      have dE := exponentialBranch_to_gapUntyped n de (Nat.le_refl n)
      have dD : UntypedDerives (GapTerminalRule n) (GapBinaryRule n)
          .marker [true] :=
        UntypedDerives.terminal GapTerminalRule.markerC
      exact UntypedDerives.binary GapBinaryRule.universalExp dE dD

/-- The actual SSBNF source start language equals {a,c}^+, for every n. -/
theorem gapSource_startLanguage_eq_nonempty (n : Nat) :
    UntypedStartLanguage (GapTerminalRule n) (GapBinaryRule n)
        (GapStartRule n) False =
      {w : List Bool | w ≠ []} := by
  ext w
  constructor
  · intro hw
    change UntypedStartDerives
      (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n) False w at hw
    cases hw with
    | nonempty _ d =>
        exact ne_of_gt (untypedDerives_length_pos
          (GapTerminalRule n) (GapBinaryRule n) d)
    | epsilon heps =>
        exact False.elim heps
  · intro hw
    exact UntypedStartDerives.nonempty rfl
      (gapUniversal_to_untyped n (gapUniversalYield_all_nonempty n w hw))

/-- Typed E_n source witness with unit h_c-type. -/
theorem gapEN_unit_typed_witness (n : Nat) :
    ∃ w : List Bool,
      TypedDerives gapCZeroTyping
        (GapTerminalRule n) (GapBinaryRule n)
        (.exponent ⟨n, Nat.lt_succ_self n⟩, (1 : ErasureFlag)) w ∧
      w.length = 2 ^ n := by
  obtain ⟨w, dE, htype, hlen, _⟩ :=
    gapExponentialBranch_unit_fibre_reachable n
  have dSource := exponentialBranch_to_gapUntyped n dE (Nat.le_refl n)
  have dLift := untypedDerives_lift gapCZeroTyping
    (GapTerminalRule n) (GapBinaryRule n) dSource
  rw [htype] at dLift
  exact ⟨w, dLift, hlen⟩

/-- In the concrete reduced yield-typed grammar, (E_n, 1) is retained. -/
theorem gapEN_unit_retained (n : Nat) :
    ConcreteTypedActive gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n)
      (.exponent ⟨n, Nat.lt_succ_self n⟩, (1 : ErasureFlag)) := by
  obtain ⟨w, dE, _hlen⟩ := gapEN_unit_typed_witness n
  have dD : TypedDerives gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n)
      (.marker, gapCZeroTyping.h [true]) [true] :=
    TypedDerives.terminal GapTerminalRule.markerC
  exact (typedStartBinary_children_survive_trim
    gapCZeroTyping (GapTerminalRule n) (GapBinaryRule n)
    (GapStartRule n) (by rfl)
    GapBinaryRule.universalExp dE dD).1

/-- The E_n-unit witness itself survives actual productive/reachable trimming. -/
theorem gapEN_unit_reduced_witness (n : Nat) :
    ∃ w : List Bool,
      ReducedTypedDerives gapCZeroTyping
        (GapTerminalRule n) (GapBinaryRule n)
        (ConcreteTypedActive gapCZeroTyping
          (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n))
        (.exponent ⟨n, Nat.lt_succ_self n⟩, (1 : ErasureFlag)) w ∧
      w.length = 2 ^ n := by
  obtain ⟨w, dE, hlen⟩ := gapEN_unit_typed_witness n
  have hactive := gapEN_unit_retained n
  have dReduced :=
    (concreteTypedActive_trimClosure gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n)
      (GapStartRule n)).restrict hactive dE
  exact ⟨w, dReduced, hlen⟩

end TCS1
end LeanCfgProject
