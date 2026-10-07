import LeanCfgProject.TCS1.V119GapSourceReduced
import Mathlib.Tactic

/-!
# TCS #1 v119: complete O(n) production presentation for G_n^c

The finite NT type has n+3 elements. These exact terminal/binary/start
predicates are fully covered by a finite set of 7+2n production slots:
one separated start rule; four U rules; one D rule; one E_0 rule; and
two rules (terminal/branch) per positive E_i.

Each slot is shown to be a valid source rule and every source rule has
at least one slot. This is a genuine exhaustive production-index
certificate, not merely a bound on a different candidate grammar.
-/

namespace LeanCfgProject
namespace TCS1

inductive V119GapRawRule (n : Nat) where
  | start (A : V119GapNT n)
  | terminal (A : V119GapNT n) (a : V117GapLetter)
  | binary (A B C : V119GapNT n)
  deriving DecidableEq

def v119GapRawRuleValid (n : Nat) : V119GapRawRule n → Prop
  | .start A => v119GapStart n A
  | .terminal A a => v119GapTerminal n A a
  | .binary A B C => v119GapBinary n A B C

/-- Seven constant slots and two slots for each positive E_i. -/
abbrev V119GapRuleCode (n : Nat) :=
  Fin 7 ⊕ (Fin n ⊕ Fin n)

/-- Concrete decoding from a finite production index. -/
def v119GapRuleDenote (n : Nat) :
    V119GapRuleCode n → V119GapRawRule n
  | .inl k =>
      if k.val = 0 then .start .u
      else if k.val = 1 then .terminal .u .a
      else if k.val = 2 then .terminal .u .c
      else if k.val = 3 then .terminal .d .c
      else if k.val = 4 then
        .terminal (.e (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1))) .a
      else if k.val = 5 then .binary .u .u .u
      else
        .binary .u
          (.e (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))) .d
  | .inr (.inl i) =>
      .terminal (.e (Fin.succ i)) .c
  | .inr (.inr i) =>
      .binary (.e (Fin.succ i))
        (.e (Fin.castSucc i)) (.e (Fin.castSucc i))

/-- Each enumerated rule exists in the actual source grammar. -/
theorem v119GapRuleCode_sound (n : Nat)
    (p : V119GapRuleCode n) :
    v119GapRawRuleValid n (v119GapRuleDenote n p) := by
  rcases p with k | p
  · fin_cases k <;>
      simp [v119GapRuleDenote, v119GapRawRuleValid,
        v119GapStart, v119GapTerminal, v119GapBinary]
  · rcases p with i | i
    · simp [v119GapRuleDenote, v119GapRawRuleValid,
        v119GapTerminal]
    · simp [v119GapRuleDenote, v119GapRawRuleValid,
        v119GapBinary]

/-- Every permitted source rule occurs among the linear number of slots. -/
theorem v119GapRuleCode_complete (n : Nat)
    (r : V119GapRawRule n)
    (hr : v119GapRawRuleValid n r) :
    ∃ p : V119GapRuleCode n, v119GapRuleDenote n p = r := by
  cases r with
  | start A =>
      cases A with
      | u => exact ⟨Sum.inl 0, rfl⟩
      | d => exact False.elim hr
      | e i => exact False.elim hr
  | terminal A a =>
      cases A with
      | u =>
          cases a with
          | a => exact ⟨Sum.inl 1, rfl⟩
          | c => exact ⟨Sum.inl 2, rfl⟩
      | d =>
          cases a with
          | a => exact False.elim hr
          | c => exact ⟨Sum.inl 3, rfl⟩
      | e i =>
          cases a with
          | a =>
              have hzero : i.val = 0 := hr
              have heq :
                  i = (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) :=
                Fin.ext hzero
              subst i
              exact ⟨Sum.inl 4, rfl⟩
          | c =>
              have hnonzero : i.val ≠ 0 := hr
              let j : Fin n := ⟨i.val - 1, by omega⟩
              have hj : Fin.succ j = i := by
                apply Fin.ext
                change i.val - 1 + 1 = i.val
                omega
              refine ⟨Sum.inr (Sum.inl j), ?_⟩
              simp [v119GapRuleDenote, hj]
  | binary A B C =>
      cases A with
      | u =>
          cases B with
          | u =>
              cases C with
              | u => exact ⟨Sum.inl 5, rfl⟩
              | d => exact False.elim hr
              | e i => exact False.elim hr
          | d =>
              cases C <;> exact False.elim hr
          | e i =>
              cases C with
              | u => exact False.elim hr
              | d =>
                  have htop : i.val = n := hr
                  have heq :
                      i = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) :=
                    Fin.ext htop
                  subst i
                  exact ⟨Sum.inl 6, rfl⟩
              | e j => exact False.elim hr
      | d =>
          cases B <;> cases C <;> exact False.elim hr
      | e i =>
          cases B with
          | u =>
              cases C <;> exact False.elim hr
          | d =>
              cases C <;> exact False.elim hr
          | e j =>
              cases C with
              | u => exact False.elim hr
              | d => exact False.elim hr
              | e k =>
                  have hij : i.val = j.val + 1 ∧ j.val = k.val := hr
                  have hjk : j = k := Fin.ext hij.2
                  subst k
                  let t : Fin n := ⟨j.val, by omega⟩
                  have htop : Fin.succ t = i := by
                    apply Fin.ext
                    change j.val + 1 = i.val
                    omega
                  have hchild : Fin.castSucc t = j := by
                    apply Fin.ext
                    rfl
                  refine ⟨Sum.inr (Sum.inr t), ?_⟩
                  simp [v119GapRuleDenote, htop, hchild]

/-- Source rule predicates are *exactly* represented by the index. -/
theorem v119GapRule_iff_indexed (n : Nat)
    (r : V119GapRawRule n) :
    v119GapRawRuleValid n r ↔
      ∃ p : V119GapRuleCode n,
        v119GapRuleDenote n p = r := by
  constructor
  · exact v119GapRuleCode_complete n r
  · rintro ⟨p, hp⟩
    rw [←hp]
    exact v119GapRuleCode_sound n p

/-- Linear source production bound, including the separated start. -/
theorem v119GapRuleCode_card (n : Nat) :
    Fintype.card (V119GapRuleCode n) = 2 * n + 7 := by
  simp [V119GapRuleCode]
  omega

end TCS1
end LeanCfgProject
