import LeanCfgProject.TCS1.V158CostedLearner
import LeanCfgProject.TCS1.ConservativeGoldKernel
import LeanCfgProject.TCS1.BatchLanguageMonotonicity

/-!
# TCS #1 v158: `cor:ilt`'s precise clause for the costed learner

`cor:ilt`: "*once `WitnessSet(G̃) ⊆ K_{n₀}`, among stages `n ≥ n₀` at most one
hypothesis change can occur.*"

The abstract kernel `ConservativeGoldKernel` proves this for every
`ConservativeRun`.  Here the executable learner of `V158CostedLearner` is
packaged as such a run (hypothesis = language of the written grammar), and the
conclusion is transferred to the **written grammar codes**: after the first
change following the characteristic stage, the written code never changes
again (`costedLearner_at_most_one_change`).  The characteristic sample `C` is
any finite `C ⊆ L` with `BatchLanguage H C = L` (for example the witness set of
`thm:reconstruction-fixed-h`).
-/

namespace LeanCfgProject
namespace TCS1
namespace CostedLearner

open PolyBuild CodeCYK

universe v q

section Characteristic

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M] [DecidableEq M]
variable (H : FixedFiniteMonoidHom α M)

theorem accumulated_subset {L : Set (Word α)} (datum : Nat → Word α)
    (hpos : ∀ n, datum n ∈ L) :
    ∀ m, (↑(concreteAccumulatedSample datum m) : Set (Word α)) ⊆ L
  | 0 => by intro x hx; simp at hx
  | m + 1 => by
      intro x hx
      have hx' : x ∈ insert (datum (m + 1)) (concreteAccumulatedSample datum m) := hx
      rcases Finset.mem_insert.mp hx' with rfl | hx'
      · exact hpos _
      · exact accumulated_subset datum hpos m hx'

/-- The costed learner as an abstract conservative run (hypothesis = written language). -/
def costedRun {L : Set (Word α)} (datum : Nat → Word α) (hpos : ∀ n, datum n ∈ L) :
    ConservativeRun (Hyp := Set (Word α)) L where
  lang := id
  batch K := BatchLanguage H K
  hyp n := codeLanguage (stateAt H datum n).code
  sample := concreteAccumulatedSample datum
  datum := datum
  sample_mono := concreteAccumulatedSample_mono datum
  positive := hpos
  keep_if_generated n h := by
    show codeLanguage (stateAt H datum (n + 1)).code = codeLanguage (stateAt H datum n).code
    rw [show stateAt H datum (n + 1) = (updateC H (stateAt H datum n) (datum (n + 1))).1 from rfl,
      (updateC_conservative H _ _ h).1]
  rebuild_if_missing n h := by
    show codeLanguage (stateAt H datum (n + 1)).code =
      BatchLanguage H (concreteAccumulatedSample datum (n + 1))
    have h' : datum (n + 1) ∉ BatchLanguage H (materializedConservativeHypothesis H datum n) := by
      rw [← code_language]; exact h
    rw [code_language]
    exact congrArg (BatchLanguage H) (materializedConservativeUpdate_rebuild H _ _ _ h')

/-- A change of the written code is a change of its language. -/
theorem code_change_iff (datum : Nat → Word α) (n : Nat) :
    (stateAt H datum (n + 1)).code ≠ (stateAt H datum n).code →
      codeLanguage (stateAt H datum (n + 1)).code ≠ codeLanguage (stateAt H datum n).code := by
  intro hne heq
  have hstep : stateAt H datum (n + 1) = (updateC H (stateAt H datum n) (datum (n + 1))).1 := rfl
  by_cases hmem : datum (n + 1) ∈ codeLanguage (stateAt H datum n).code
  · exact hne (by rw [hstep]; exact (updateC_conservative H _ _ hmem).1)
  · apply hmem
    have h' : datum (n + 1) ∉ BatchLanguage H (materializedConservativeHypothesis H datum n) := by
      rw [← code_language]; exact hmem
    have hK : materializedConservativeHypothesis H datum (n + 1) =
        concreteAccumulatedSample datum (n + 1) :=
      materializedConservativeUpdate_rebuild H _ _ _ h'
    rw [← heq, code_language, hK]
    exact sample_consistency H _ (Finset.mem_insert_self _ _)

/--
**`cor:ilt`, precise form, for the executable learner.**  Let `C ⊆ L` be a
characteristic sample (`BatchLanguage H C = L`) for an `H`-substitutable target
`L`, presented by positive data.  If `C` is contained in the data seen by stage
`n₀`, then after the first change of the written grammar at a stage `n + 1`
with `n ≥ n₀`, the written grammar never changes again.
-/
theorem costedLearner_at_most_one_change {L : Set (Word α)}
    (hsub : FixedHSubstitutable H L) (C : Finset (Word α))
    (hCL : (↑C : Set (Word α)) ⊆ L) (hchar : BatchLanguage H C = L)
    (datum : Nat → Word α) (hpos : ∀ n, datum n ∈ L)
    (n₀ n : Nat) (hC : C ⊆ concreteAccumulatedSample datum n₀) (hn : n₀ ≤ n)
    (hchange : (stateAt H datum (n + 1)).code ≠ (stateAt H datum n).code) :
    ∀ k, (stateAt H datum ((n + 1) + k)).code = (stateAt H datum (n + 1)).code := by
  have hbatch : ∀ m, C ⊆ concreteAccumulatedSample datum m →
      BatchLanguage H (concreteAccumulatedSample datum m) = L := by
    intro m hm
    apply Set.Subset.antisymm
    · exact batchLanguage_sound H _ L (accumulated_subset datum hpos m) hsub
    · rw [← hchar]; exact batchLanguage_mono H hm
  have hlang := stable_after_first_post_characteristic_change (costedRun H datum hpos) C n₀ n
    hC hn hbatch (code_change_iff H datum n hchange)
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      by_contra hne
      have hne' : (stateAt H datum (n + 1 + k + 1)).code ≠ (stateAt H datum (n + 1 + k)).code := by
        intro h
        apply hne
        rw [show n + 1 + (k + 1) = n + 1 + k + 1 by omega, h, ih]
      apply code_change_iff H datum (n + 1 + k) hne'
      have a : codeLanguage (stateAt H datum (n + 1 + (k + 1))).code =
          codeLanguage (stateAt H datum (n + 1)).code := hlang (k + 1)
      have b : codeLanguage (stateAt H datum (n + 1 + k)).code =
          codeLanguage (stateAt H datum (n + 1)).code := hlang k
      rw [show n + 1 + k + 1 = n + 1 + (k + 1) by omega, a, b]

end Characteristic

end CostedLearner
end TCS1
end LeanCfgProject
