import LeanCfgProject.TCS1.ConcreteConservativeLearner

/-!
# TCS #1: empty and epsilon-only target endpoints

The main normalization bridge chooses a productive non-start symbol and
therefore assumes a nonempty terminal word.  The manuscript treats the two
degenerate target endpoints separately:

* the empty language is represented by the fixed empty hypothesis; and
* the nonempty language {lambda} is reconstructed from the one-word sample
  {lambda}.

This module verifies those endpoint statements directly for the set-driven
reconstruction and, for {lambda}, for the concrete conservative Gold learner.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section TrivialTargetEndpoints

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/-- Reconstructing from the empty sample generates no word. -/
theorem batchLanguage_empty_eq
    (H : FixedFiniteMonoidHom α M) :
    BatchLanguage H (∅ : Finset (Word α))
      =
    (∅ : Set (Word α)) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    cases hw with
    | nonempty hs hs_ne d =>
        simp at hs
    | epsilon heps =>
        simp at heps
  · intro hw
    simp at hw

/-- The singleton sample {lambda} reconstructs exactly {lambda}. -/
theorem batchLanguage_singleton_epsilon_eq
    (H : FixedFiniteMonoidHom α M) :
    BatchLanguage H ({[]} : Finset (Word α))
      =
    ({[]} : Set (Word α)) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    cases hw with
    | @nonempty s w hs hs_ne d =>
        have hs0 : s = [] := by
          simpa using hs
        exact False.elim (hs_ne hs0)
    | epsilon heps =>
        simp
  · intro hw
    have hw0 : w = [] := by
      simpa using hw
    subst w
    exact BatchDerives.epsilon (by simp)

/-- The epsilon-only language is fixed-h substitutable for every fixed h. -/
theorem singletonEpsilon_fixedHSubstitutable
    (H : FixedFiniteMonoidHom α M) :
    FixedHSubstitutable H
      ({[]} : Set (Word α)) := by
  intro x y hx hy htype hshared
  rcases hshared with
    ⟨u, v, hxmem, hymem⟩
  have hcat : u ++ x ++ v = ([] : Word α) := by
    simpa using hxmem
  have hlen :
      (u ++ x ++ v).length = 0 := by
    rw [hcat]
    rfl
  have hxlen : x.length = 0 := by
    simp only [List.length_append] at hlen
    omega
  have hx0 : x = [] := by
    cases x with
    | nil =>
        rfl
    | cons a xs =>
        simp at hxlen
  exact False.elim (hx hx0)

/-- {lambda} has the one-word characteristic sample {lambda}. -/
theorem singletonEpsilon_characteristic
    (H : FixedFiniteMonoidHom α M) :
    BatchLanguage H ({[]} : Finset (Word α))
      =
    ({[]} : Set (Word α)) :=
  batchLanguage_singleton_epsilon_eq H

/--
Gold identification of the epsilon-only target by the concrete conservative
learner.  This is the nonempty endpoint not covered by a normalization theorem
that chooses a nonempty non-start yield.
-/
theorem singletonEpsilon_concreteGold_identification
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (hpositive :
      ∀ n, datum n ∈ ({[]} : Set (Word α)))
    (hcoverage :
      ∀ w,
        w ∈ ({[]} : Set (Word α)) →
        ∃ n, w ∈ concreteAccumulatedSample datum n) :
    let R :=
      concreteAccumulatedConservativeRun
        H ({[]} : Set (Word α))
        datum hpositive
    ∃ n₀,
      (R.lang (R.hyp n₀) =
          ({[]} : Set (Word α)) ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) =
          ({[]} : Set (Word α)) ∧
        ∀ j,
          R.hyp ((n + 1) + j) =
            R.hyp (n + 1)) := by
  exact
    concreteConservative_gold_identification
      H
      ({[]} : Set (Word α))
      ({[]} : Finset (Word α))
      (singletonEpsilon_characteristic H)
      (singletonEpsilon_fixedHSubstitutable H)
      datum hpositive hcoverage

end TrivialTargetEndpoints

end TCS1
end LeanCfgProject
