import LeanCfgProject.TCS1.BatchLanguageMonotonicity
import LeanCfgProject.TCS1.GoldConvergenceClosure

/-!
# TCS #1: characteristic samples imply conservative Gold convergence

The abstract Gold kernel asks for exactness of every rebuilt hypothesis after a
characteristic stage.  The set-driven reconstruction theorem supplies this
automatically: accumulated samples are positive, reconstruction is monotone in
the sample, and every positive super-sample of a characteristic sample is
exact.

This module packages that last bridge without referring to any particular
fixed-window monoid.
-/

namespace LeanCfgProject
namespace TCS1

universe u v q

section GoldCharacteristicBridge

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {Hyp : Type q}

/-- Every accumulated sample in a positive-data run is contained in the target. -/
theorem accumulated_sample_positive
    [DecidableEq α]
    {L : Set (Word α)}
    (R : AccumulatedConservativeRun (α := α) (Hyp := Hyp) L) :
    ∀ n, (↑(R.sample n) : Set (Word α)) ⊆ L := by
  intro n
  induction n with
  | zero =>
      intro w hw
      have hempty : w ∈ (∅ : Finset (Word α)) := by
        simpa [R.sample_zero] using hw
      simpa using hempty
  | succ n ih =>
      intro w hw
      have hwInsert :
          w ∈ insert (R.datum (n + 1)) (R.sample n) := by
        simpa [R.sample_succ n] using hw
      rcases Finset.mem_insert.mp hwInsert with hdatum | hold
      · subst w
        exact R.positive (n + 1)
      · exact ih hold

/--
If the run's batch object denotes the set-driven reconstruction language, then
a characteristic sample discharges the rebuilt-hypothesis premise of the
abstract one-change Gold theorem.
-/
theorem gold_one_change_dichotomy_of_characteristic_sample
    [DecidableEq α]
    {L : Set (Word α)}
    (H : FixedFiniteMonoidHom α M)
    (R : AccumulatedConservativeRun (α := α) (Hyp := Hyp) L)
    (C : Finset (Word α))
    (n₀ : Nat)
    (hC : C ⊆ R.sample n₀)
    (hchar : BatchLanguage H C = L)
    (hsub : FixedHSubstitutable H L)
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) = BatchLanguage H K)
    (hsound : R.lang (R.hyp n₀) ⊆ L)
    (hcoverage :
      ∀ w, w ∈ L → ∃ n, w ∈ R.sample n) :
    (R.lang (R.hyp n₀) = L ∧
      ∀ k, R.hyp (n₀ + k) = R.hyp n₀)
    ∨
    (∃ n,
      n₀ ≤ n ∧
      R.hyp (n + 1) ≠ R.hyp n ∧
      R.lang (R.hyp (n + 1)) = L ∧
      ∀ k, R.hyp ((n + 1) + k) = R.hyp (n + 1)) := by
  have hpositive :
      ∀ m, (↑(R.sample m) : Set (Word α)) ⊆ L :=
    accumulated_sample_positive R
  have hbatch :
      ∀ m,
        C ⊆ R.sample m →
        R.lang (R.batch (R.sample m)) = L := by
    intro m hCm
    rw [hbatchSem]
    exact
      batchLanguage_exact_of_characteristic_subset
        H C (R.sample m) L
        hCm (hpositive m) hsub hchar
  exact
    gold_one_change_dichotomy
      R C n₀ hC hbatch hsound hcoverage


/--
Finite text coverage implies that every finite positive characteristic sample
is contained in one accumulated sample.
-/
theorem finite_characteristic_sample_eventually_covered
    [DecidableEq α]
    {L : Set (Word α)}
    (R : AccumulatedConservativeRun (α := α) (Hyp := Hyp) L)
    (C : Finset (Word α))
    (hCL : (↑C : Set (Word α)) ⊆ L)
    (hcoverage :
      ∀ w, w ∈ L → ∃ n, w ∈ R.sample n) :
    ∃ n₀, C ⊆ R.sample n₀ := by
  classical
  induction C using Finset.induction_on with
  | empty =>
      exact ⟨0, by simp⟩
  | @insert a C ha ih =>
      have haL : a ∈ L :=
        hCL (Finset.mem_insert_self a C)
      have hCL' : (↑C : Set (Word α)) ⊆ L := by
        intro w hw
        exact hCL (Finset.mem_insert_of_mem hw)
      obtain ⟨na, haSample⟩ := hcoverage a haL
      obtain ⟨nC, hCSample⟩ := ih hCL'
      refine ⟨max na nC, ?_⟩
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hwC
      · exact
          R.sample_mono
            (Nat.le_max_left na nC)
            haSample
      · exact
          R.sample_mono
            (Nat.le_max_right na nC)
            (hCSample hwC)

/--
Soundness of the initial conservative hypothesis propagates to every stage
when each rebuild denotes the set-driven reconstruction of the positive
accumulated sample.
-/
theorem accumulated_conservative_run_all_sound
    [DecidableEq α]
    {L : Set (Word α)}
    (H : FixedFiniteMonoidHom α M)
    (R : AccumulatedConservativeRun (α := α) (Hyp := Hyp) L)
    (hsub : FixedHSubstitutable H L)
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) = BatchLanguage H K)
    (hsound0 : R.lang (R.hyp 0) ⊆ L) :
    ∀ n, R.lang (R.hyp n) ⊆ L := by
  intro n
  induction n with
  | zero =>
      exact hsound0
  | succ n ih =>
      by_cases hgen :
          R.datum (n + 1) ∈ R.lang (R.hyp n)
      · have hkeep :
            R.hyp (n + 1) = R.hyp n :=
          R.keep_if_generated n hgen
        simpa [hkeep] using ih
      · have hrebuild :
            R.hyp (n + 1) =
              R.batch (R.sample (n + 1)) :=
          R.rebuild_if_missing n hgen
        rw [hrebuild, hbatchSem]
        exact
          batchLanguage_sound
            H
            (R.sample (n + 1))
            L
            (accumulated_sample_positive R (n + 1))
            hsub

/--
Full characteristic-sample form of conservative Gold identification.

No characteristic stage is supplied externally: finiteness of C and text
coverage construct one.  From that stage onward there is either no further
change and the current hypothesis is exact, or the first later change is exact
and is the last change.
-/
theorem gold_identification_of_characteristic_sample
    [DecidableEq α]
    {L : Set (Word α)}
    (H : FixedFiniteMonoidHom α M)
    (R : AccumulatedConservativeRun (α := α) (Hyp := Hyp) L)
    (C : Finset (Word α))
    (hchar : BatchLanguage H C = L)
    (hsub : FixedHSubstitutable H L)
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) = BatchLanguage H K)
    (hsound0 : R.lang (R.hyp 0) ⊆ L)
    (hcoverage :
      ∀ w, w ∈ L → ∃ n, w ∈ R.sample n) :
    ∃ n₀,
      (R.lang (R.hyp n₀) = L ∧
        ∀ k, R.hyp (n₀ + k) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) = L ∧
        ∀ k, R.hyp ((n + 1) + k) = R.hyp (n + 1)) := by
  have hCL : (↑C : Set (Word α)) ⊆ L := by
    rw [← hchar]
    exact sample_consistency H C
  obtain ⟨n₀, hC⟩ :=
    finite_characteristic_sample_eventually_covered
      R C hCL hcoverage
  have hallSound :
      ∀ n, R.lang (R.hyp n) ⊆ L :=
    accumulated_conservative_run_all_sound
      H R hsub hbatchSem hsound0
  refine ⟨n₀, ?_⟩
  exact
    gold_one_change_dichotomy_of_characteristic_sample
      H R C n₀ hC hchar hsub hbatchSem
      (hallSound n₀) hcoverage

end GoldCharacteristicBridge

end TCS1
end LeanCfgProject
