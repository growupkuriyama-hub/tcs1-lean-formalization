import LeanCfgProject.TCS1.YieldTypedRefinementCore
import Mathlib.Tactic

/-!
# TCS #1 v121: exponential type-one yield in the E_i subgrammar

This file verifies the new exponential-gap example's E_i *derivational core*.
It DOES NOT yet prove the complete displayed SSBNF grammar presentation,
source reducedness, its linear encoding, or survival under the full
productive/reachable typed trim. Those remain separate audit obligations.

In the grammar from Proposition "exponential source-to-typed thickness gap",
E_0 -> a and E_(i+1) -> E_i E_i | c, with h_c(a) = 1 and
h_c(c) = zero. We prove type-1 E_i yields have *exactly* length 2^i,
and exhibit a derivation at that length.
-/

namespace LeanCfgProject
namespace TCS1
namespace TypedGap

inductive Letter where
  | a | c
  deriving DecidableEq, Fintype, Repr

inductive TwoElement where
  | one | zero
  deriving DecidableEq, Fintype, Repr

def twoMul : TwoElement → TwoElement → TwoElement
  | .one, .one => .one
  | _, _ => .zero

instance : Monoid TwoElement where
  one := .one
  mul := twoMul
  one_mul x := by cases x <;> rfl
  mul_one x := by cases x <;> rfl
  mul_assoc x y z := by
    cases x <;> cases y <;> cases z <;> rfl

/-- Word type: one iff no c occurs; c is absorbing. -/
def wordType : Word Letter → TwoElement
  | [] => .one
  | .a :: tail => wordType tail
  | .c :: _ => .zero

theorem wordType_append
    (u v : Word Letter) :
    wordType (u ++ v) = wordType u * wordType v := by
  induction u with
  | nil =>
      rfl
  | cons s u ih =>
      cases s with
      | a => simpa [wordType] using ih
      | c => rfl

def fixedTyping : FixedFiniteMonoidHom Letter TwoElement where
  h := wordType
  map_nil := rfl
  map_append := wordType_append

/-- Exact source E_i fragment, with its original c shortcut. -/
inductive EDerives : Nat → Word Letter → Prop
  | base : EDerives 0 [.a]
  | shortcut (i : Nat) : EDerives (i + 1) [.c]
  | double (i : Nat) {u v : Word Letter}
      (du : EDerives i u) (dv : EDerives i v) :
      EDerives (i + 1) (u ++ v)

/-- Every type-one E_i derivation has exactly exponential length. -/
theorem EDerives_type_one_length
    {i : Nat} {w : Word Letter}
    (d : EDerives i w) :
    wordType w = .one → w.length = 2 ^ i := by
  induction d with
  | base =>
      intro _
      simp
  | shortcut i =>
      intro h
      simp [wordType] at h
  | @double i u v du dv ihU ihV =>
      intro h
      have hprod :
          wordType u * wordType v = .one := by
        rw [← wordType_append]
        exact h
      have hu : wordType u = .one := by
        cases hu : wordType u with
        | one => rfl
        | zero =>
            cases hv : wordType v <;>
              simp [twoMul, hu, hv] at hprod
      have hv : wordType v = .one := by
        cases hv : wordType v with
        | one => rfl
        | zero =>
            simp [twoMul, hu, hv] at hprod
      simp only [List.length_append, ihU hu, ihV hv]
      simp [pow_succ]
      omega

/-- The all-a expansion witnesses the lower bound sharply. -/
def pureE : Nat → Word Letter
  | 0 => [.a]
  | i + 1 => pureE i ++ pureE i

theorem pureE_derives (i : Nat) :
    EDerives i (pureE i) := by
  induction i with
  | zero =>
      exact EDerives.base
  | succ i ih =>
      exact EDerives.double i ih ih

theorem pureE_type_one (i : Nat) :
    wordType (pureE i) = .one := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      simpa [pureE, wordType_append, ih, twoMul] using
        (show wordType (pureE i) * wordType (pureE i) =
          (.one : TwoElement) by
          rw [ih]
          rfl)

theorem pureE_length (i : Nat) :
    (pureE i).length = 2 ^ i :=
  EDerives_type_one_length (pureE_derives i)
    (pureE_type_one i)

/-- Fully checked local E_i result: shortest h_c-type-one yield equals 2^i. -/
theorem type_one_minimum_length (i : Nat) :
    (∃ w : Word Letter,
      EDerives i w ∧
      wordType w = .one ∧ w.length = 2 ^ i)
    ∧
    (∀ w : Word Letter,
      EDerives i w →
      wordType w = .one →
      2 ^ i ≤ w.length) := by
  constructor
  · exact ⟨pureE i, pureE_derives i, pureE_type_one i,
      pureE_length i⟩
  · intro w d ht
    rw [EDerives_type_one_length d ht]

end TypedGap
end TCS1
end LeanCfgProject
