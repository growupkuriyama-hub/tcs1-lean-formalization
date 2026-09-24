import LeanCfgProject.TCS1.CanonicalWitnessCompleteness

/-!
# TCS #1 v63: conservative Gold wrapper kernel

The batch reconstruction operator is not itself the sequential Gold learner.
The v63 manuscript wraps it conservatively: keep the current hypothesis when
the new positive datum is already generated, and rebuild from the entire
accumulated sample only when the datum is missing.

This file verifies the abstract part of that argument.  Once a characteristic
sample is contained in the accumulated data, the first later rebuild is exact;
after an exact hypothesis is reached, positivity of the text makes the run
permanently stable.  Consequently at most one further hypothesis change can
occur after the characteristic stage.
-/

namespace LeanCfgProject
namespace TCS1

universe u q

section ConservativeGold

variable {α : Type u}
variable {Hyp : Type q}

/--
Abstract data of a conservative positive-data run.
No decidability assumption is built into the structure; the two update clauses
state the behavior in the generated and missing cases.
-/
structure ConservativeRun
    (L : Set (Word α)) where
  lang : Hyp → Set (Word α)
  batch : Finset (Word α) → Hyp
  hyp : Nat → Hyp
  sample : Nat → Finset (Word α)
  datum : Nat → Word α

  sample_mono :
    Monotone sample

  positive :
    ∀ n, datum n ∈ L

  keep_if_generated :
    ∀ n,
      datum (n + 1) ∈ lang (hyp n) →
      hyp (n + 1) = hyp n

  rebuild_if_missing :
    ∀ n,
      datum (n + 1) ∉ lang (hyp n) →
      hyp (n + 1) = batch (sample (n + 1))

/--
If the characteristic sample is already present, any actual later change must
be a rebuild and that rebuilt hypothesis is exact.
-/
theorem exact_after_post_characteristic_change
    {L : Set (Word α)}
    (R : ConservativeRun (Hyp := Hyp) L)
    (C : Finset (Word α))
    (n₀ n : Nat)
    (hC : C ⊆ R.sample n₀)
    (hn : n₀ ≤ n)
    (hbatch :
      ∀ m,
        C ⊆ R.sample m →
        R.lang (R.batch (R.sample m)) = L)
    (hchange : R.hyp (n + 1) ≠ R.hyp n) :
    R.lang (R.hyp (n + 1)) = L := by
  by_cases hgen : R.datum (n + 1) ∈ R.lang (R.hyp n)
  · have hkeep := R.keep_if_generated n hgen
    exact False.elim (hchange hkeep)
  · have hrebuild := R.rebuild_if_missing n hgen
    have hn₁ : n₀ ≤ n + 1 := by omega
    have hC' : C ⊆ R.sample (n + 1) := by
      intro x hx
      exact R.sample_mono hn₁ (hC hx)
    rw [hrebuild]
    exact hbatch (n + 1) hC'

/--
Once the current hypothesis language is exactly the positive target, every
later hypothesis object is syntactically identical to it.
-/
theorem stable_from_exact
    {L : Set (Word α)}
    (R : ConservativeRun (Hyp := Hyp) L)
    (n : Nat)
    (hexact : R.lang (R.hyp n) = L) :
    ∀ k : Nat, R.hyp (n + k) = R.hyp n := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hgen :
          R.datum (n + k + 1) ∈ R.lang (R.hyp (n + k)) := by
        rw [ih, hexact]
        exact R.positive (n + k + 1)
      have hkeep :=
        R.keep_if_generated (n + k) hgen
      calc
        R.hyp (n + (k + 1)) = R.hyp (n + k + 1) := by
          rw [Nat.add_succ]
        _ = R.hyp (n + k) := hkeep
        _ = R.hyp n := ih

/--
One-change bound from the v63 Gold-identification proof:
if a change occurs at stage n+1 after the characteristic stage, then the new
hypothesis is exact and all later hypotheses are literally the same object.
-/
theorem stable_after_first_post_characteristic_change
    {L : Set (Word α)}
    (R : ConservativeRun (Hyp := Hyp) L)
    (C : Finset (Word α))
    (n₀ n : Nat)
    (hC : C ⊆ R.sample n₀)
    (hn : n₀ ≤ n)
    (hbatch :
      ∀ m,
        C ⊆ R.sample m →
        R.lang (R.batch (R.sample m)) = L)
    (hchange : R.hyp (n + 1) ≠ R.hyp n) :
    ∀ k : Nat, R.hyp ((n + 1) + k) = R.hyp (n + 1) := by
  have hexact :=
    exact_after_post_characteristic_change
      R C n₀ n hC hn hbatch hchange
  exact stable_from_exact R (n + 1) hexact

/--
Equivalent no-second-change formulation: after the first post-characteristic
change, every subsequent one-step update is a keep step.
-/
theorem no_second_change_after_characteristic
    {L : Set (Word α)}
    (R : ConservativeRun (Hyp := Hyp) L)
    (C : Finset (Word α))
    (n₀ n : Nat)
    (hC : C ⊆ R.sample n₀)
    (hn : n₀ ≤ n)
    (hbatch :
      ∀ m,
        C ⊆ R.sample m →
        R.lang (R.batch (R.sample m)) = L)
    (hchange : R.hyp (n + 1) ≠ R.hyp n) :
    ∀ k : Nat,
      R.hyp ((n + 1) + (k + 1)) =
        R.hyp ((n + 1) + k) := by
  intro k
  have hstable :=
    stable_after_first_post_characteristic_change
      R C n₀ n hC hn hbatch hchange
  calc
    R.hyp ((n + 1) + (k + 1)) = R.hyp (n + 1) :=
      hstable (k + 1)
    _ = R.hyp ((n + 1) + k) :=
      (hstable k).symm

end ConservativeGold

end TCS1
end LeanCfgProject
