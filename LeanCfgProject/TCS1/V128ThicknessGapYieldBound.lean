import LeanCfgProject.TCS1.V128ThicknessGapFiniteSSBNF
import LeanCfgProject.TCS1.NormalizationLanguageBounds

/-!
# TCS #1 v128: actual finite SSBNF exponential typed-thickness lower bound

The unit-fibre lower bound is proved for the concrete finite grammar G_n
rather than just the abstract E_i derivation system.

The proof proceeds by induction on arbitrary untyped G_n derivations from
an E_i state: when the yield has h_c-type 1, the c-terminal alternative
cannot be used, and the two child derivations double the required length.

We then erase reduced typed derivations into source derivations,
recover their h_c yield types, and prove a lower bound for every uniform
reduced-typed shortest-yield envelope, using the repository's existing
YieldBound interface.

The finite source grammar's reducedness and actual encoded size O(n),
and the claimed ordinary thickness = 1, are separate obligations.
-/

namespace LeanCfgProject
namespace TCS1

/-- Forget everything except the integer index of an exponent symbol. -/
def gapExponentIndex (n : Nat) : GapNonterminal n → Nat
  | .exponent i => i.val
  | _ => 0

/-- Every c-free source derivation from E_i has length exactly 2^i. -/
theorem gapUntyped_exponent_noC_length (n : Nat)
    {A : GapNonterminal n} {w : List Bool}
    (d : UntypedDerives (GapTerminalRule n) (GapBinaryRule n) A w) :
    ∀ i : Fin (n + 1),
      A = .exponent i →
      ExponentialBranchNoC w →
      w.length = 2 ^ i.val := by
  induction d with
  | terminal hterm =>
      cases hterm with
      | universalA =>
          intro i hroot
          cases hroot
      | universalC =>
          intro i hroot
          cases hroot
      | markerC =>
          intro i hroot
          cases hroot
      | exponentA =>
          intro i hroot _hnoc
          have hval : i.val = 0 := by
            have hv := congrArg (gapExponentIndex n) hroot
            simp only [gapExponentIndex] at hv
            exact hv.symm
          simp [hval]
      | exponentC hi =>
          intro i _hroot hnoc
          exact False.elim (hnoc (by simp [ExponentialBranchNoC]))
  | @binary A B C wB wC hbin _dB _dC ihB ihC =>
      cases hbin with
      | universalPair =>
          intro i hroot
          cases hroot
      | universalExp =>
          intro i hroot
          cases hroot
      | @exponentPair i j hstep =>
          intro k hroot hnoc
          have hnoB : ExponentialBranchNoC wB := by
            intro hm
            exact hnoc (List.mem_append.mpr (Or.inl hm))
          have hnoC : ExponentialBranchNoC wC := by
            intro hm
            exact hnoc (List.mem_append.mpr (Or.inr hm))
          have hv := congrArg (gapExponentIndex n) hroot
          have hk : k.val = j.val + 1 := by
            change i.val = k.val at hv
            omega
          have hl : wB.length = 2 ^ j.val := ihB j rfl hnoB
          have hr : wC.length = 2 ^ j.val := ihC j rfl hnoC
          calc
            (wB ++ wC).length = wB.length + wC.length := by simp
            _ = 2 ^ j.val + 2 ^ j.val := by rw [hl, hr]
            _ = 2 ^ k.val := by
              rw [hk, pow_succ]
              omega

/-- Every c-free E_n source yield has the exponential length. -/
theorem gapSource_EN_unit_fibre_length
    (n : Nat) (w : List Bool)
    (d : UntypedDerives (GapTerminalRule n) (GapBinaryRule n)
      (.exponent ⟨n, Nat.lt_succ_self n⟩) w)
    (htype : gapCZeroTyping.h w = (1 : ErasureFlag)) :
    w.length = 2 ^ n := by
  exact gapUntyped_exponent_noC_length n d
    ⟨n, Nat.lt_succ_self n⟩ rfl
    ((gapCZeroTyping_one_iff_noC w).mp htype)

/-- Every trimmed E_n type-1 derivation has exponential length. -/
theorem gapReduced_EN_unit_fibre_length
    (n : Nat) (w : List Bool)
    (d : ReducedTypedDerives gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n)
      (ConcreteTypedActive gapCZeroTyping
        (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n))
      (.exponent ⟨n, Nat.lt_succ_self n⟩, (1 : ErasureFlag)) w) :
    w.length = 2 ^ n := by
  have dFull := reducedTypedDerives_to_typedDerives
    gapCZeroTyping (GapTerminalRule n) (GapBinaryRule n)
    (ConcreteTypedActive gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n)) d
  have dSource := typedDerives_erase
    gapCZeroTyping (GapTerminalRule n) (GapBinaryRule n) dFull
  have htype := typedDerives_yield_type
    gapCZeroTyping (GapTerminalRule n) (GapBinaryRule n) dFull
  exact gapSource_EN_unit_fibre_length n w dSource htype

/-- Existing repository interface for uniform typed-shortest-yield bounds. -/
def gapRetainedTypedYieldLanguage (n : Nat) :
    NTLang
      {X : GapNonterminal n × ErasureFlag //
        ConcreteTypedActive gapCZeroTyping
          (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n) X}
      Bool :=
  fun X => {w | ReducedTypedDerives gapCZeroTyping
    (GapTerminalRule n) (GapBinaryRule n)
    (ConcreteTypedActive gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n))
    X.1 w}

/-- No bound on all shortest typed yields can be smaller than 2^n. -/
theorem gapRetained_typed_YieldBound_ge_exponential
    (n bound : Nat)
    (hb : YieldBound (gapRetainedTypedYieldLanguage n) bound) :
    2 ^ n ≤ bound := by
  let en : {X : GapNonterminal n × ErasureFlag //
      ConcreteTypedActive gapCZeroTyping
        (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n) X} :=
    ⟨(.exponent ⟨n, Nat.lt_succ_self n⟩, (1 : ErasureFlag)),
      gapEN_unit_retained n⟩
  obtain ⟨w, hw, hlen⟩ := hb en
  have hd : ReducedTypedDerives gapCZeroTyping
      (GapTerminalRule n) (GapBinaryRule n)
      (ConcreteTypedActive gapCZeroTyping
        (GapTerminalRule n) (GapBinaryRule n) (GapStartRule n))
      (.exponent ⟨n, Nat.lt_succ_self n⟩, (1 : ErasureFlag)) w := hw
  exact (le_of_eq (gapReduced_EN_unit_fibre_length n w hd).symm).trans hlen

end TCS1
end LeanCfgProject
