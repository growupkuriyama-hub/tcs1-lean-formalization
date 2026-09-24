import LeanCfgProject.TCS1.IndexedSection7Bridge
import LeanCfgProject.TCS1.GoldCharacteristicBridge

/-!
# TCS #1: end-to-end indexed fixed-window Gold convergence

This module joins the now-concrete Section 7 characteristic sample to the
conservative positive-data Gold kernel.  Once the canonical sample has appeared
in the accumulated text, every later rebuild from a positive super-sample is
exact; hence either the current hypothesis is already exact or the first later
change is exact and is the last change.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section IndexedGoldBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {Hyp : Type q}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/--
End-to-end Gold one-change theorem from a finite indexed source CFG under the
paper's fixed-h substitutability hypothesis.
-/
theorem indexedFixedWindow_gold_one_change_dichotomy
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A))
    (R :
      AccumulatedConservativeRun
        (α := α) (Hyp := Hyp)
        (LeastClosedLanguage G.toMixedRules A))
    (n₀ : Nat)
    (hC :
      indexedFixedWindowCanonicalSample G A hprod k l
        ⊆ R.sample n₀)
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) =
          BatchLanguage
            (fixedWindowMonoidHom (α := α) k l) K)
    (hsound :
      R.lang (R.hyp n₀) ⊆
        LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n, word ∈ R.sample n) :
    (R.lang (R.hyp n₀) =
        LeastClosedLanguage G.toMixedRules A ∧
      ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
    ∨
    (∃ n,
      n₀ ≤ n ∧
      R.hyp (n + 1) ≠ R.hyp n ∧
      R.lang (R.hyp (n + 1)) =
        LeastClosedLanguage G.toMixedRules A ∧
      ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  have hpack :=
    indexedFixedWindowSection7_package
      G A hprod τR k l hn hsource hsub
  have hchar :
      BatchLanguage
          (fixedWindowMonoidHom (α := α) k l)
          (indexedFixedWindowCanonicalSample
            G A hprod k l)
        =
      LeastClosedLanguage G.toMixedRules A :=
    hpack.1
  exact
    gold_one_change_dichotomy_of_characteristic_sample
      (fixedWindowMonoidHom (α := α) k l)
      R
      (indexedFixedWindowCanonicalSample
        G A hprod k l)
      n₀ hC hchar hsub hbatchSem hsound hcoverage

/--
Classical Yoshinaka (k,l)-substitutability form of the same end-to-end Gold
statement.
-/
theorem indexedClassicalFixedWindow_gold_one_change_dichotomy
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hwin :
      FixedWindowSubstitutable
        k l
        (LeastClosedLanguage G.toMixedRules A))
    (R :
      AccumulatedConservativeRun
        (α := α) (Hyp := Hyp)
        (LeastClosedLanguage G.toMixedRules A))
    (n₀ : Nat)
    (hC :
      indexedFixedWindowCanonicalSample G A hprod k l
        ⊆ R.sample n₀)
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) =
          BatchLanguage
            (fixedWindowMonoidHom (α := α) k l) K)
    (hsound :
      R.lang (R.hyp n₀) ⊆
        LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n, word ∈ R.sample n) :
    (R.lang (R.hyp n₀) =
        LeastClosedLanguage G.toMixedRules A ∧
      ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
    ∨
    (∃ n,
      n₀ ≤ n ∧
      R.hyp (n + 1) ≠ R.hyp n ∧
      R.lang (R.hyp (n + 1)) =
        LeastClosedLanguage G.toMixedRules A ∧
      ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A) :=
    fixedHSubstitutable_of_fixedWindowSubstitutable
      k l
      (LeastClosedLanguage G.toMixedRules A)
      hwin
  exact
    indexedFixedWindow_gold_one_change_dichotomy
      G A hprod τR k l hn hsource hsub
      R n₀ hC hbatchSem hsound hcoverage

/-- The source-level Gold theorem at the explicit (0,0) endpoint. -/
theorem indexedZeroWindow_gold_one_change_dichotomy
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hzero :
      NonemptyFactorSubstitutable
        (LeastClosedLanguage G.toMixedRules A))
    (R :
      AccumulatedConservativeRun
        (α := α) (Hyp := Hyp)
        (LeastClosedLanguage G.toMixedRules A))
    (n₀ : Nat)
    (hC :
      indexedFixedWindowCanonicalSample G A hprod 0 0
        ⊆ R.sample n₀)
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) =
          BatchLanguage
            (fixedWindowMonoidHom (α := α) 0 0) K)
    (hsound :
      R.lang (R.hyp n₀) ⊆
        LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n, word ∈ R.sample n) :
    (R.lang (R.hyp n₀) =
        LeastClosedLanguage G.toMixedRules A ∧
      ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
    ∨
    (∃ n,
      n₀ ≤ n ∧
      R.hyp (n + 1) ≠ R.hyp n ∧
      R.lang (R.hyp (n + 1)) =
        LeastClosedLanguage G.toMixedRules A ∧
      ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) 0 0)
        (LeastClosedLanguage G.toMixedRules A) :=
    (fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable
      (α := α)
      (LeastClosedLanguage G.toMixedRules A)).2 hzero
  exact
    indexedFixedWindow_gold_one_change_dichotomy
      G A hprod τR 0 0 hn hsource hsub
      R n₀ hC hbatchSem hsound hcoverage


/--
Full end-to-end Gold identification from a finite indexed source CFG.

Unlike the one-change theorem above, no characteristic stage is supplied by
the caller.  Finiteness of the canonical Section 7 sample and text coverage
produce such a stage automatically.
-/
theorem indexedFixedWindow_gold_identification
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A))
    (R :
      AccumulatedConservativeRun
        (α := α) (Hyp := Hyp)
        (LeastClosedLanguage G.toMixedRules A))
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) =
          BatchLanguage
            (fixedWindowMonoidHom (α := α) k l) K)
    (hsound0 :
      R.lang (R.hyp 0) ⊆
        LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n, word ∈ R.sample n) :
    ∃ n₀,
      (R.lang (R.hyp n₀) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  have hpack :=
    indexedFixedWindowSection7_package
      G A hprod τR k l hn hsource hsub
  exact
    gold_identification_of_characteristic_sample
      (fixedWindowMonoidHom (α := α) k l)
      R
      (indexedFixedWindowCanonicalSample G A hprod k l)
      hpack.1 hsub hbatchSem hsound0 hcoverage

/-- Classical Yoshinaka (k,l)-substitutability form of full identification. -/
theorem indexedClassicalFixedWindow_gold_identification
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR k l : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hwin :
      FixedWindowSubstitutable
        k l
        (LeastClosedLanguage G.toMixedRules A))
    (R :
      AccumulatedConservativeRun
        (α := α) (Hyp := Hyp)
        (LeastClosedLanguage G.toMixedRules A))
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) =
          BatchLanguage
            (fixedWindowMonoidHom (α := α) k l) K)
    (hsound0 :
      R.lang (R.hyp 0) ⊆
        LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n, word ∈ R.sample n) :
    ∃ n₀,
      (R.lang (R.hyp n₀) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) k l)
        (LeastClosedLanguage G.toMixedRules A) :=
    fixedHSubstitutable_of_fixedWindowSubstitutable
      k l
      (LeastClosedLanguage G.toMixedRules A)
      hwin
  exact
    indexedFixedWindow_gold_identification
      G A hprod τR k l hn hsource hsub
      R hbatchSem hsound0 hcoverage

/-- Full identification at the explicit (0,0) endpoint. -/
theorem indexedZeroWindow_gold_identification
    (G : IndexedMixedCFG N α P)
    (A : N)
    (hprod :
      ∃ u : Word α,
        u ∈ LeastClosedLanguage G.toMixedRules A ∧
        u ≠ [])
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun B => LeastClosedLanguage G.toMixedRules B)
        τR)
    (hzero :
      NonemptyFactorSubstitutable
        (LeastClosedLanguage G.toMixedRules A))
    (R :
      AccumulatedConservativeRun
        (α := α) (Hyp := Hyp)
        (LeastClosedLanguage G.toMixedRules A))
    (hbatchSem :
      ∀ K : Finset (Word α),
        R.lang (R.batch K) =
          BatchLanguage
            (fixedWindowMonoidHom (α := α) 0 0) K)
    (hsound0 :
      R.lang (R.hyp 0) ⊆
        LeastClosedLanguage G.toMixedRules A)
    (hcoverage :
      ∀ word,
        word ∈ LeastClosedLanguage G.toMixedRules A →
        ∃ n, word ∈ R.sample n) :
    ∃ n₀,
      (R.lang (R.hyp n₀) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp (n₀ + j) = R.hyp n₀)
      ∨
      (∃ n,
        n₀ ≤ n ∧
        R.hyp (n + 1) ≠ R.hyp n ∧
        R.lang (R.hyp (n + 1)) =
          LeastClosedLanguage G.toMixedRules A ∧
        ∀ j, R.hyp ((n + 1) + j) = R.hyp (n + 1)) := by
  have hsub :
      FixedHSubstitutable
        (fixedWindowMonoidHom (α := α) 0 0)
        (LeastClosedLanguage G.toMixedRules A) :=
    (fixedHSubstitutable_zeroWindow_iff_nonemptyFactorSubstitutable
      (α := α)
      (LeastClosedLanguage G.toMixedRules A)).2 hzero
  exact
    indexedFixedWindow_gold_identification
      G A hprod τR 0 0 hn hsource hsub
      R hbatchSem hsound0 hcoverage

end IndexedGoldBridge

end TCS1
end LeanCfgProject
