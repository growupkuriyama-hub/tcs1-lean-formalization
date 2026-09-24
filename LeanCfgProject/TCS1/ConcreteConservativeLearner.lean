import LeanCfgProject.TCS1.GoldCharacteristicBridge

/-!
# TCS #1: concrete conservative positive-data learner

The previous Gold development is phrased for an abstract accumulated
conservative run.  Here we instantiate that interface by the reconstruction
operator itself.

A hypothesis object is simply the finite positive sample from which the
set-driven grammar is rebuilt.  Its semantics is `BatchLanguage H K`.
At stage n+1 the learner keeps the current hypothesis when the new datum is
already generated, and otherwise replaces it by the full accumulated sample.

The definition is noncomputable because membership in `BatchLanguage` is
chosen classically at this layer.  This file therefore closes the semantic
Gold-identification interface; an effective parser/decision procedure can be
verified separately without changing the convergence proof.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ConcreteConservativeLearner

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable [DecidableEq α]

/-- Finite positive data accumulated through stage n. -/
def concreteAccumulatedSample
    (datum : Nat → Word α) :
    Nat → Finset (Word α)
  | 0 => ∅
  | n + 1 =>
      insert (datum (n + 1))
        (concreteAccumulatedSample datum n)

@[simp] theorem concreteAccumulatedSample_zero
    (datum : Nat → Word α) :
    concreteAccumulatedSample datum 0 = ∅ :=
  rfl

@[simp] theorem concreteAccumulatedSample_succ
    (datum : Nat → Word α)
    (n : Nat) :
    concreteAccumulatedSample datum (n + 1) =
      insert (datum (n + 1))
        (concreteAccumulatedSample datum n) :=
  rfl

/-- Accumulated positive samples are monotone. -/
theorem concreteAccumulatedSample_mono
    (datum : Nat → Word α) :
    Monotone (concreteAccumulatedSample datum) := by
  intro m n hmn
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      subst m
      exact Finset.Subset.rfl
  | succ n ih =>
      by_cases hm : m ≤ n
      · exact
          Finset.Subset.trans
            (ih hm)
            (Finset.subset_insert
              (datum (n + 1))
              (concreteAccumulatedSample datum n))
      · have hmEq : m = n + 1 := by omega
        subst m
        exact Finset.Subset.rfl

/-- One conservative update of the current hypothesis code. -/
noncomputable def concreteConservativeUpdate
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α) :
    Finset (Word α) := by
  classical
  exact
    if word ∈ BatchLanguage H current then
      current
    else
      accumulated

/-- A generated datum leaves the current hypothesis code unchanged. -/
theorem concreteConservativeUpdate_keep
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α)
    (hgen : word ∈ BatchLanguage H current) :
    concreteConservativeUpdate
        H current accumulated word
      =
    current := by
  classical
  simp [concreteConservativeUpdate, hgen]

/-- A missing datum replaces the hypothesis code by the accumulated sample. -/
theorem concreteConservativeUpdate_rebuild
    (H : FixedFiniteMonoidHom α M)
    (current accumulated : Finset (Word α))
    (word : Word α)
    (hmiss : word ∉ BatchLanguage H current) :
    concreteConservativeUpdate
        H current accumulated word
      =
    accumulated := by
  classical
  simp [concreteConservativeUpdate, hmiss]

/--
The actual conservative hypothesis sequence.  The hypothesis object is the
finite sample used by the reconstruction operator.
-/
noncomputable def concreteConservativeHypothesis
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α) :
    Nat → Finset (Word α)
  | 0 => ∅
  | n + 1 =>
      concreteConservativeUpdate
        H
        (concreteConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))

/-- Generated data cause a literal keep step. -/
theorem concreteConservativeHypothesis_keep
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat)
    (hgen :
      datum (n + 1) ∈
        BatchLanguage H
          (concreteConservativeHypothesis H datum n)) :
    concreteConservativeHypothesis H datum (n + 1) =
      concreteConservativeHypothesis H datum n := by
  change
    concreteConservativeUpdate
        H
        (concreteConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))
      =
    concreteConservativeHypothesis H datum n
  exact
    concreteConservativeUpdate_keep
      H
      (concreteConservativeHypothesis H datum n)
      (concreteAccumulatedSample datum (n + 1))
      (datum (n + 1))
      hgen

/-- Missing data cause rebuilding from the entire accumulated sample. -/
theorem concreteConservativeHypothesis_rebuild
    (H : FixedFiniteMonoidHom α M)
    (datum : Nat → Word α)
    (n : Nat)
    (hmiss :
      datum (n + 1) ∉
        BatchLanguage H
          (concreteConservativeHypothesis H datum n)) :
    concreteConservativeHypothesis H datum (n + 1) =
      concreteAccumulatedSample datum (n + 1) := by
  change
    concreteConservativeUpdate
        H
        (concreteConservativeHypothesis H datum n)
        (concreteAccumulatedSample datum (n + 1))
        (datum (n + 1))
      =
    concreteAccumulatedSample datum (n + 1)
  exact
    concreteConservativeUpdate_rebuild
      H
      (concreteConservativeHypothesis H datum n)
      (concreteAccumulatedSample datum (n + 1))
      (datum (n + 1))
      hmiss

/-- The empty initial reconstruction is sound for every target language. -/
theorem emptyBatchLanguage_subset
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α)) :
    BatchLanguage H (∅ : Finset (Word α)) ⊆ L := by
  intro w hw
  cases hw with
  | nonempty hs hs_ne d =>
      simp at hs
  | epsilon heps =>
      simp at heps

/--
Concrete accumulated conservative run whose batch semantics is definitionally
the set-driven reconstruction language.
-/
noncomputable def concreteAccumulatedConservativeRun
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (datum : Nat → Word α)
    (hpositive : ∀ n, datum n ∈ L) :
    AccumulatedConservativeRun
      (α := α) (Hyp := Finset (Word α)) L where
  lang := BatchLanguage H
  batch := fun K => K
  hyp := concreteConservativeHypothesis H datum
  sample := concreteAccumulatedSample datum
  datum := datum
  sample_mono :=
    concreteAccumulatedSample_mono datum
  positive := hpositive
  keep_if_generated := by
    intro n hgen
    exact
      concreteConservativeHypothesis_keep
        H datum n hgen
  rebuild_if_missing := by
    intro n hmiss
    exact
      concreteConservativeHypothesis_rebuild
        H datum n hmiss
  sample_zero := rfl
  sample_succ := by
    intro n
    rfl
  batch_sample_consistent := by
    intro K
    exact sample_consistency H K

/-- Batch semantics of the concrete run needs no external representation lemma. -/
theorem concreteAccumulatedConservativeRun_batchSem
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (datum : Nat → Word α)
    (hpositive : ∀ n, datum n ∈ L) :
    ∀ K : Finset (Word α),
      (concreteAccumulatedConservativeRun
        H L datum hpositive).lang
        ((concreteAccumulatedConservativeRun
          H L datum hpositive).batch K)
        =
      BatchLanguage H K := by
  intro K
  rfl

/-- The concrete run starts from a sound empty hypothesis automatically. -/
theorem concreteAccumulatedConservativeRun_initial_sound
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (datum : Nat → Word α)
    (hpositive : ∀ n, datum n ∈ L) :
    (concreteAccumulatedConservativeRun
      H L datum hpositive).lang
      ((concreteAccumulatedConservativeRun
        H L datum hpositive).hyp 0)
      ⊆ L := by
  simpa [concreteAccumulatedConservativeRun,
    concreteConservativeHypothesis] using
    emptyBatchLanguage_subset H L

/--
Generic full Gold identification for the concrete conservative learner.

The only text assumptions left are positivity and coverage.  The batch
semantics and initial soundness hypotheses of the abstract Gold theorem are
discharged by construction.
-/
theorem concreteConservative_gold_identification
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (C : Finset (Word α))
    (hchar : BatchLanguage H C = L)
    (hsub : FixedHSubstitutable H L)
    (datum : Nat → Word α)
    (hpositive : ∀ n, datum n ∈ L)
    (hcoverage :
      ∀ w, w ∈ L →
        ∃ n, w ∈ concreteAccumulatedSample datum n) :
    let R :=
      concreteAccumulatedConservativeRun
        H L datum hpositive
    ∃ n₀,
      (R.lang (R.hyp n₀) = L ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) = L ∧
        ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  dsimp
  exact
    gold_identification_of_characteristic_sample
      H
      (concreteAccumulatedConservativeRun
        H L datum hpositive)
      C hchar hsub
      (concreteAccumulatedConservativeRun_batchSem
        H L datum hpositive)
      (concreteAccumulatedConservativeRun_initial_sound
        H L datum hpositive)
      hcoverage


/--
Projection-free form of the concrete Gold theorem.

This states convergence directly in terms of the finite hypothesis code and
its reconstructed language, so the conclusion no longer depends on proof
fields stored in `AccumulatedConservativeRun`.
-/
theorem concreteConservative_gold_identification_explicit
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (C : Finset (Word α))
    (hchar : BatchLanguage H C = L)
    (hsub : FixedHSubstitutable H L)
    (datum : Nat → Word α)
    (hpositive : ∀ n, datum n ∈ L)
    (hcoverage :
      ∀ w, w ∈ L →
        ∃ n, w ∈ concreteAccumulatedSample datum n) :
    ∃ n₀,
      (BatchLanguage H
          (concreteConservativeHypothesis H datum n₀) = L
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum (n₀ + j) =
            concreteConservativeHypothesis H datum n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        concreteConservativeHypothesis H datum (n + 1) ≠
          concreteConservativeHypothesis H datum n ∧
        BatchLanguage H
          (concreteConservativeHypothesis H datum (n + 1)) = L
        ∧
        ∀ j,
          concreteConservativeHypothesis H datum ((n + 1) + j) =
            concreteConservativeHypothesis H datum (n + 1)) := by
  have h :=
    concreteConservative_gold_identification
      H L C hchar hsub datum hpositive hcoverage
  simpa [concreteAccumulatedConservativeRun] using h

end ConcreteConservativeLearner

end TCS1
end LeanCfgProject
