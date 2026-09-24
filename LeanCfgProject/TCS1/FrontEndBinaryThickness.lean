import LeanCfgProject.TCS1.TerminalIsolationBinarizationBridge
import LeanCfgProject.TCS1.SequenceBinaryGrammarBridge
import LeanCfgProject.TCS1.FrontEndThicknessKernel

/-!
# TCS #1 v66: front-end thickness on explicit binary derivations

The previous front-end modules established three pieces separately:

* terminal isolation preserves least-generated languages;
* binarization preserves least-generated languages and has an explicit
  BinaryNullableGrammar presentation;
* canonical old/wrapper/suffix states have short witnesses bounded by
  n * (tau_R + 1).

This file composes those pieces. It proves that the canonical front-end
interpretation is exactly explicit BinaryNullableGrammar derivability and
therefore transfers the front-end witness bound to actual binary derivations.

The state predicate remains FrontEndActive; restricting it further to the
finite set of suffix states actually created by the input grammar is the
remaining polynomial-size bookkeeping layer.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FrontEndBinaryThickness

variable {N : Type u}
variable {α : Type v}

/--
For every isolated state, the least-generated sequence language is exactly the
canonical isolated interpretation of the source least-generated languages.
-/
theorem isolatedSequenceLeast_eq_interpretation
    (R : MixedRules N α)
    (X : N ⊕ α) :
    SequenceLeastLanguage
        (isolatedSequenceGrammar R) X
      =
    isolatedInterpretation
      (fun A => LeastClosedLanguage R A) X := by
  cases X with
  | inl A =>
      calc
        SequenceLeastLanguage
            (isolatedSequenceGrammar R)
            (Sum.inl A)
          =
        LeastClosedLanguage
            (IsolatedRule R)
            (Sum.inl A) :=
          isolated_leastLanguage_eq_sequenceLeast
            R (Sum.inl A)
        _ =
        LeastClosedLanguage R A :=
          terminalIsolation_leastClosedLanguage_eq R A
        _ =
        isolatedInterpretation
          (fun B => LeastClosedLanguage R B)
          (Sum.inl A) := by
            rfl
  | inr a =>
      calc
        SequenceLeastLanguage
            (isolatedSequenceGrammar R)
            (Sum.inr a)
          =
        LeastClosedLanguage
            (IsolatedRule R)
            (Sum.inr a) :=
          isolated_leastLanguage_eq_sequenceLeast
            R (Sum.inr a)
        _ =
        ({[a]} : Set (List α)) :=
          terminalIsolation_wrapper_leastClosed_eq_singleton
            R a
        _ =
        isolatedInterpretation
          (fun B => LeastClosedLanguage R B)
          (Sum.inr a) := by
            rfl

/-- Binary grammar obtained after terminal isolation followed by binarization. -/
def frontEndBinaryGrammar
    (R : MixedRules N α) :
    BinaryNullableGrammar
      (FrontEndState N α) α :=
  binarizedBinaryGrammar
    (isolatedSequenceGrammar R)

/--
Explicit binary derivability after the front end is exactly the canonical
front-end interpretation of the original source languages.
-/
theorem frontEndBinary_derives_iff_interpretation
    (R : MixedRules N α)
    (X : FrontEndState N α)
    (w : List α) :
    BinaryNullableDerives
        (frontEndBinaryGrammar R) X w
      ↔
    w ∈ frontEndInterpretation
      (fun A => LeastClosedLanguage R A) X := by
  have hsource :
      SequenceLeastLanguage
          (isolatedSequenceGrammar R)
        =
      isolatedInterpretation
        (fun A => LeastClosedLanguage R A) := by
    funext Y
    exact isolatedSequenceLeast_eq_interpretation R Y
  have h :=
    binarizedBinary_derives_iff_canonical
      (isolatedSequenceGrammar R) X w
  simpa [frontEndBinaryGrammar,
    frontEndInterpretation, hsource] using h

/--
Every active binary front-end state has an explicit derivation with length at
most n * (tau_R + 1), provided every source nonterminal has a terminal witness
of length at most tau_R.
-/
theorem frontEndBinary_active_short_derivation
    (R : MixedRules N α)
    (n τR : Nat)
    (hn : 0 < n)
    (hshort :
      YieldBound
        (fun A => LeastClosedLanguage R A)
        τR)
    (X : FrontEndState N α)
    (hactive :
      FrontEndActive (N := N) (α := α) n X) :
    ∃ w,
      BinaryNullableDerives
        (frontEndBinaryGrammar R) X w
      ∧ w.length ≤ n * thicknessBar τR := by
  obtain ⟨w, hw, hlen⟩ :=
    frontEnd_active_short_witness
      (fun A => LeastClosedLanguage R A)
      n τR hn hshort X hactive
  exact
    ⟨w,
      (frontEndBinary_derives_iff_interpretation
        R X w).2 hw,
      hlen⟩

/--
Same front-end derivation bound in the paper-facing binarized thickness
envelope with c1 = 1.
-/
theorem frontEndBinary_active_short_derivation_envelope
    (R : MixedRules N α)
    (n τR : Nat)
    (hn : 0 < n)
    (hshort :
      YieldBound
        (fun A => LeastClosedLanguage R A)
        τR)
    (X : FrontEndState N α)
    (hactive :
      FrontEndActive (N := N) (α := α) n X) :
    ∃ w,
      BinaryNullableDerives
        (frontEndBinaryGrammar R) X w
      ∧
      w.length ≤
        binarizedThicknessEnvelope 1 n τR := by
  obtain ⟨w, hw, hlen⟩ :=
    frontEndBinary_active_short_derivation
      R n τR hn hshort X hactive
  refine ⟨w, hw, ?_⟩
  simpa [binarizedThicknessEnvelope] using hlen

end FrontEndBinaryThickness

end TCS1
end LeanCfgProject
