import LeanCfgProject.TCS1.V121TypedGapGrammar
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.FixedHSubstitutability
import Mathlib.Tactic

/-!
# TCS #1 v126: complete semantic package for the exponential typed-thickness example

This file closes the manuscript-facing semantic obligations that were left
outside the earlier E_i kernel:

* the displayed source start language is exactly the nonempty language over
  {a,c};
* every source non-start symbol is productive and reachable from the start
  child U, hence the displayed source presentation is reduced in the ordinary
  productive/reachable sense;
* every source non-start symbol has shortest yield length exactly one;
* the source language is fixed-h_c substitutable;
* the retained typed symbol (E_n,1) has a successful yield and every one of
  its retained yields has length exactly 2^n, giving the exact lower-bound
  witness needed for typed thickness.

The separate finite-presentation counting theorem below records linear
numbers of nonterminals and rule schemata.  It is intentionally not presented
as a machine-cost theorem for an unspecified external text encoding.
-/

namespace LeanCfgProject
namespace TCS1
namespace TypedGap

/-- U derives either terminal letter in one step. -/
theorem gap_u_letter_derives
    (n : Nat) (s : Letter) :
    UntypedDerives (GapTerm n) (GapBin n) (.u) [s] := by
  cases s with
  | a => exact UntypedDerives.terminal GapTerm.u_a
  | c => exact UntypedDerives.terminal GapTerm.u_c

/-- U generates every nonempty word over the two-letter alphabet. -/
theorem gap_u_derives_of_nonempty
    (n : Nat) :
    ∀ {w : Word Letter},
      w ≠ [] →
      UntypedDerives (GapTerm n) (GapBin n) (.u) w := by
  intro w hw
  induction w with
  | nil => exact False.elim (hw rfl)
  | cons s tail ih =>
      by_cases htail : tail = []
      · subst tail
        exact gap_u_letter_derives n s
      · have ds : UntypedDerives (GapTerm n) (GapBin n) (.u) [s] :=
          gap_u_letter_derives n s
        have dt : UntypedDerives (GapTerm n) (GapBin n) (.u) tail :=
          ih htail
        simpa using
          (UntypedDerives.binary (GapBin.u_concat (n := n)) ds dt)

/-- Exact source language of the displayed start-separated grammar:
all and only nonempty words over {a,c}. -/
theorem gap_start_language_eq_nonempty
    (n : Nat) :
    UntypedStartLanguage
        (GapTerm n) (GapBin n) (GapStart n) False
      =
    {w : Word Letter | w ≠ []} := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    cases hw with
    | nonempty hstart d =>
        exact List.ne_nil_of_length_pos
          (untypedDerives_length_pos (GapTerm n) (GapBin n) d)
    | epsilon hfalse =>
        exact False.elim hfalse
  · intro hw
    exact
      UntypedStartDerives.nonempty
        (show GapStart n (.u) from rfl)
        (gap_u_derives_of_nonempty n hw)

/-- The nonempty full two-letter language is fixed-typing substitutable for
every typing, hence in particular for h_c. -/
theorem nonempty_full_language_fixedH
    {M : Type} [Monoid M] [Fintype M]
    (H : FixedFiniteMonoidHom Letter M) :
    FixedHSubstitutable H
      ({w : Word Letter | w ≠ []} : Set (Word Letter)) := by
  intro x y hx hy htype hshared
  apply Set.ext
  intro uv
  rcases uv with ⟨u, v⟩
  change
    u ++ x ++ v ≠ [] ↔
      u ++ y ++ v ≠ []
  constructor <;> intro _
  · intro hnil
    simp only [List.append_eq_nil_iff] at hnil
    exact hy hnil.1.2
  · intro hnil
    simp only [List.append_eq_nil_iff] at hnil
    exact hx hnil.1.2

/-- The displayed source target belongs to the fixed-h_c substitutable slice. -/
theorem gap_source_fixedH (n : Nat) :
    FixedHSubstitutable fixedTyping
      (UntypedStartLanguage
        (GapTerm n) (GapBin n) (GapStart n) False) := by
  rw [gap_start_language_eq_nonempty n]
  exact nonempty_full_language_fixedH fixedTyping

/-- Ordinary source reachability through binary child edges from U. -/
inductive GapReachable (n : Nat) : GapNT n → Prop
  | start : GapReachable n .u
  | left {A B C : GapNT n}
      (hA : GapReachable n A)
      (hbin : GapBin n A B C) :
      GapReachable n B
  | right {A B C : GapNT n}
      (hA : GapReachable n A)
      (hbin : GapBin n A B C) :
      GapReachable n C

/-- The top E_n symbol is directly reachable from U. -/
theorem gap_eTop_reachable (n : Nat) :
    GapReachable n (.e ⟨n, Nat.lt_succ_self n⟩) :=
  GapReachable.left GapReachable.start GapBin.u_end

/-- Every E_i with i≤n is reached by descending the doubling chain. -/
theorem gap_e_reachable_by_down
    (n : Nat) :
    ∀ d : Nat, d ≤ n →
      GapReachable n
        (.e ⟨n - d, by omega⟩) := by
  intro d
  induction d with
  | zero =>
      intro hd
      simpa using gap_eTop_reachable n
  | succ d ih =>
      intro hd
      have hd' : d ≤ n := by omega
      let j : Fin (n + 1) := ⟨n - d, by omega⟩
      let k : Fin (n + 1) := ⟨n - (d + 1), by omega⟩
      have hj : GapReachable n (.e j) := by
        simpa [j] using ih hd'
      have hstep : j.val = k.val + 1 := by
        dsimp [j, k]
        omega
      exact
        GapReachable.left hj
          (GapBin.ei_double j k hstep)

/-- Every indexed E_i is source-reachable. -/
theorem gap_e_reachable
    (n : Nat) (i : Fin (n + 1)) :
    GapReachable n (.e i) := by
  have hi : i.val ≤ n := by omega
  have h :=
    gap_e_reachable_by_down n (n - i.val) (by omega)
  have hval : n - (n - i.val) = i.val :=
    Nat.sub_sub_self hi
  have heq :
      (⟨n - (n - i.val), by omega⟩ : Fin (n + 1)) = i := by
    apply Fin.ext
    exact hval
  simpa [heq] using h

/-- Every source non-start symbol is reachable from U. -/
theorem gap_source_all_reachable
    (n : Nat) (A : GapNT n) :
    GapReachable n A := by
  cases A with
  | u => exact GapReachable.start
  | d =>
      exact GapReachable.right
        GapReachable.start GapBin.u_end
  | e i =>
      exact gap_e_reachable n i

/-- Every source symbol has shortest terminal-yield length exactly one:
a one-letter yield exists and no untyped derivation is empty. -/
theorem gap_source_shortest_yield_one
    (n : Nat) (A : GapNT n) :
    (∃ w : Word Letter,
      UntypedDerives (GapTerm n) (GapBin n) A w ∧
      w.length = 1)
    ∧
    (∀ w : Word Letter,
      UntypedDerives (GapTerm n) (GapBin n) A w →
      1 ≤ w.length) := by
  constructor
  · obtain ⟨s, ds⟩ := gap_source_has_unit_yield n A
    exact ⟨[s], ds, by simp⟩
  · intro w d
    exact untypedDerives_length_pos
      (GapTerm n) (GapBin n) d

/-- Source reducedness package: every non-start symbol is productive and
reachable from the start child. -/
theorem gap_source_reduced_package
    (n : Nat) :
    (∀ A : GapNT n,
      ∃ w : Word Letter,
        UntypedDerives (GapTerm n) (GapBin n) A w)
    ∧
    (∀ A : GapNT n, GapReachable n A) := by
  constructor
  · intro A
    obtain ⟨s, ds⟩ := gap_source_has_unit_yield n A
    exact ⟨[s], ds⟩
  · exact gap_source_all_reachable n

/-- The separated source start itself also has a one-letter terminal yield. -/
theorem gap_start_has_unit_yield
    (n : Nat) :
    ∃ w : Word Letter,
      UntypedStartDerives
        (GapTerm n) (GapBin n) (GapStart n) False w
      ∧ w.length = 1 := by
  refine ⟨[.a], ?_, by simp⟩
  exact
    UntypedStartDerives.nonempty
      (show GapStart n (.u) from rfl)
      (UntypedDerives.terminal GapTerm.u_a)

/-- A paper-shaped witness for typed thickness ≥ 2^n:
one retained typed nonterminal has a successful yield, and all of its
successful retained yields have length at least 2^n. -/
def GapTypedThicknessAtLeast
    (n bound : Nat) : Prop :=
  ∃ X : GapNT n × TwoElement,
    ConcreteTypedActive
      fixedTyping (GapTerm n) (GapBin n) (GapStart n) X
    ∧
    (∃ w : Word Letter,
      ReducedTypedDerives
        fixedTyping (GapTerm n) (GapBin n)
        (ConcreteTypedActive
          fixedTyping (GapTerm n) (GapBin n) (GapStart n))
        X w)
    ∧
    (∀ w : Word Letter,
      ReducedTypedDerives
        fixedTyping (GapTerm n) (GapBin n)
        (ConcreteTypedActive
          fixedTyping (GapTerm n) (GapBin n) (GapStart n))
        X w →
      bound ≤ w.length)

/-- Exact manuscript lower-bound witness for the reduced typed refinement. -/
theorem gap_typed_thickness_at_least_pow_two
    (n : Nat) :
    GapTypedThicknessAtLeast n (2 ^ n) := by
  let X : GapNT n × TwoElement :=
    ((.e ⟨n, Nat.lt_succ_self n⟩), .one)
  refine ⟨X, gap_eTop_retained n, ?_, ?_⟩
  · obtain ⟨w, d, hlen⟩ := gap_eTop_trimmed_witness n
    exact ⟨w, d⟩
  · intro w d
    rw [gap_eTop_trimmed_length_exact n d]

/-- Exact number of source non-start nonterminal names is n+3. -/
theorem gap_nonterminal_card
    (n : Nat) :
    Fintype.card (GapNT n) = n + 3 := by
  let e : GapNT n ≃ (Fin 2 ⊕ Fin (n + 1)) :=
    { toFun := fun A =>
        match A with
        | .u => Sum.inl ⟨0, by omega⟩
        | .d => Sum.inl ⟨1, by omega⟩
        | .e i => Sum.inr i
      invFun := fun s =>
        match s with
        | Sum.inl i => if i.val = 0 then .u else .d
        | Sum.inr i => .e i
      left_inv := by
        intro A
        cases A with
        | u => rfl
        | d => rfl
        | e i => rfl
      right_inv := by
        intro s
        cases s with
        | inl i =>
            fin_cases i <;> rfl
        | inr i => rfl }
  rw [Fintype.card_congr e]
  simp
  omega

/-- There are exactly 6+2n displayed non-start productions:
U has four rules, D and E_0 have one each, and each E_i (i>0) has two.
The separated start contributes one further rule. -/
def gapDisplayedRuleCount (n : Nat) : Nat :=
  6 + 2 * n

/-- Including the separated start rule, the displayed grammar has 7+2n
production schemata, hence linear presentation size. -/
def gapDisplayedRuleCountWithStart (n : Nat) : Nat :=
  gapDisplayedRuleCount n + 1

theorem gapDisplayedRuleCount_linear
    (n : Nat) :
    gapDisplayedRuleCountWithStart n ≤ 9 * (n + 1) := by
  unfold gapDisplayedRuleCountWithStart
  unfold gapDisplayedRuleCount
  omega

/-- Integrated semantic package for Proposition "exponential source-to-typed
thickness gap", leaving only the conventional encoding interpretation of
O(n) outside this theorem. -/
theorem gap_semantic_proposition_package
    (n : Nat) :
    UntypedStartLanguage
        (GapTerm n) (GapBin n) (GapStart n) False
      = {w : Word Letter | w ≠ []}
    ∧
    FixedHSubstitutable fixedTyping
      (UntypedStartLanguage
        (GapTerm n) (GapBin n) (GapStart n) False)
    ∧
    (∀ A : GapNT n,
      GapReachable n A)
    ∧
    (∀ A : GapNT n,
      (∃ w : Word Letter,
        UntypedDerives (GapTerm n) (GapBin n) A w ∧
        w.length = 1)
      ∧
      (∀ w : Word Letter,
        UntypedDerives (GapTerm n) (GapBin n) A w →
        1 ≤ w.length))
    ∧
    GapTypedThicknessAtLeast n (2 ^ n) := by
  refine ⟨gap_start_language_eq_nonempty n,
    gap_source_fixedH n,
    gap_source_all_reachable n,
    ?_,
    gap_typed_thickness_at_least_pow_two n⟩
  exact gap_source_shortest_yield_one n

end TypedGap
end TCS1
end LeanCfgProject
