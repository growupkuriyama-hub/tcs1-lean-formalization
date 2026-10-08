import LeanCfgProject.TCS1.V128ThicknessGapOrdinary

/-!
# TCS #1 v128: reducedness of the source exponential-gap SSBNF grammar

Every one of the finite source non-start states U, D and E_0,...,E_n
is productive (indeed has a one-letter yield) and reachable in the
actual grammar rule graph from S_0 -> U. The E_i reachability proof
descends from E_n along the rules E_(j+1) -> E_j E_j.

Combined with the ordinary YieldBound = 1 and the exponential lower
bound for the trimmed typed grammar, this closes the qualitative
reducedness part of Proposition prop:typed-thickness-gap.
The explicit encoded-size/rule-enumeration bound remains separate.
-/

namespace LeanCfgProject
namespace TCS1

/-- Reachability of source non-start symbols using actual binary rules. -/
inductive GapSourceReachable (n : Nat) : GapNonterminal n → Prop
  | start : GapSourceReachable n .universal
  | left {A B C : GapNonterminal n}
      (hparent : GapSourceReachable n A)
      (hrule : GapBinaryRule n A B C) :
      GapSourceReachable n B
  | right {A B C : GapNonterminal n}
      (hparent : GapSourceReachable n A)
      (hrule : GapBinaryRule n A B C) :
      GapSourceReachable n C

/-- E_(n-offset) is reached by offset descending binary-rule steps. -/
private theorem gapExponent_reachable_from_top (n : Nat) :
    ∀ offset : Nat, offset ≤ n →
      GapSourceReachable n
        (.exponent ⟨n - offset,
          Nat.lt_succ_of_le (Nat.sub_le n offset)⟩) := by
  intro offset
  induction offset with
  | zero =>
      intro _hle
      have htop : GapSourceReachable n
          (.exponent ⟨n, Nat.lt_succ_self n⟩) :=
        GapSourceReachable.left
          GapSourceReachable.start GapBinaryRule.universalExp
      simpa using htop
  | succ offset ih =>
      intro hle
      have hprev : offset ≤ n := by omega
      have hpar : GapSourceReachable n
          (.exponent ⟨n - offset,
            Nat.lt_succ_of_le (Nat.sub_le n offset)⟩) :=
        ih hprev
      have hrule : GapBinaryRule n
          (.exponent ⟨n - offset,
            Nat.lt_succ_of_le (Nat.sub_le n offset)⟩)
          (.exponent ⟨n - (offset + 1),
            Nat.lt_succ_of_le (Nat.sub_le n (offset + 1))⟩)
          (.exponent ⟨n - (offset + 1),
            Nat.lt_succ_of_le (Nat.sub_le n (offset + 1))⟩) :=
        GapBinaryRule.exponentPair (by
          change n - offset = n - (offset + 1) + 1
          omega)
      exact GapSourceReachable.left hpar hrule

/-- All E_i, including E_0 and E_n, are reached from the start child U. -/
theorem gapExponent_source_reachable (n : Nat)
    (i : Fin (n + 1)) :
    GapSourceReachable n (.exponent i) := by
  have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hreach := gapExponent_reachable_from_top n
    (n - i.val) (Nat.sub_le n i.val)
  have hidx : (⟨n - (n - i.val),
      Nat.lt_succ_of_le (Nat.sub_le n (n - i.val))⟩ :
      Fin (n + 1)) = i := Fin.ext (by
    change n - (n - i.val) = i.val
    omega)
  simpa only [hidx] using hreach

/-- The source grammar has no unreachable non-start symbols. -/
theorem gapSource_all_reachable (n : Nat) :
    ∀ A : GapNonterminal n, GapSourceReachable n A := by
  intro A
  cases A with
  | universal =>
      exact GapSourceReachable.start
  | marker =>
      exact GapSourceReachable.right
        GapSourceReachable.start GapBinaryRule.universalExp
  | exponent i =>
      exact gapExponent_source_reachable n i

/-- Every non-start symbol is both reachable and productive. -/
theorem gapSource_reduced (n : Nat) :
    ∀ A : GapNonterminal n,
      GapSourceReachable n A ∧
        ∃ w : List Bool,
          UntypedDerives (GapTerminalRule n) (GapBinaryRule n) A w := by
  intro A
  obtain ⟨w, hd, _⟩ := gapSource_all_short_yields n A
  exact ⟨gapSource_all_reachable n A, ⟨w, hd⟩⟩

end TCS1
end LeanCfgProject
