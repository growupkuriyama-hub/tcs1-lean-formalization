import LeanCfgProject.TCS1.FrontEndBinaryThickness
import LeanCfgProject.TCS1.BinaryGrammarFiniteRestriction
import LeanCfgProject.TCS1.Proposition74Facade

/-!
# TCS #1 v66: finite-support facade for the normalization front end

The semantic terminal-isolation/binarization grammar uses a convenient ambient
state type containing all wrappers and all suffix lists.  A concrete finite
source grammar uses only a finite rule-closed subset of those states.

This module packages exactly the information needed from such a finite support:
all supported states satisfy the front-end length bound, rules stay inside the
support, and the support has a polynomial cardinality bound.  The ambient
grammar is then restricted to that finite subtype, giving an actual Fintype
grammar to which the verified Proposition 7.4 back end applies.

Thus the remaining front-end obligation is purely constructive bookkeeping:
build this certificate from a chosen finite encoding of the source CFG.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FrontEndFiniteSupportFacade

variable {N : Type u}
variable {α : Type v}
variable [DecidableEq N] [DecidableEq α]

/--
Certificate that a finite set contains the actual states of the front-end
binary grammar relevant to a concrete source representation.
-/
structure FrontEndSupportCertificate
    (R : MixedRules N α)
    (n : Nat) where
  support : Finset (FrontEndState N α)
  closed :
    BinaryGrammarSupportedOn
      (frontEndBinaryGrammar R)
      support
  active :
    ∀ X, X ∈ support →
      FrontEndActive (N := N) (α := α) n X

/--
The paper's front-end thickness estimate becomes a local YieldBound on every
certified supported state.
-/
theorem frontEndSupport_yieldBoundOn
    (R : MixedRules N α)
    (n τR : Nat)
    (cert : FrontEndSupportCertificate R n)
    (hn : 0 < n)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage R A)
        τR) :
    YieldBoundOn
      (fun X =>
        {w | BinaryNullableDerives
          (frontEndBinaryGrammar R) X w})
      cert.support
      (binarizedThicknessEnvelope 1 n τR) := by
  intro X hX
  have hactive :
      FrontEndActive (N := N) (α := α) n X :=
    cert.active X hX
  exact
    frontEndBinary_active_short_derivation_envelope
      R n τR hn hsource X hactive

/-- Actual finite binary grammar obtained by restricting to certified support. -/
def finiteFrontEndGrammar
    (R : MixedRules N α)
    (n : Nat)
    (cert : FrontEndSupportCertificate R n) :
    BinaryNullableGrammar
      (SupportedState cert.support) α :=
  restrictBinaryGrammar
    (frontEndBinaryGrammar R)
    cert.support

/--
The local front-end witness estimate is an ordinary global YieldBound on the
finite restricted grammar.
-/
theorem finiteFrontEnd_yieldBound
    (R : MixedRules N α)
    (n τR : Nat)
    (cert : FrontEndSupportCertificate R n)
    (hn : 0 < n)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage R A)
        τR) :
    YieldBound
      (fun X =>
        {w | BinaryNullableDerives
          (finiteFrontEndGrammar R n cert) X w})
      (binarizedThicknessEnvelope 1 n τR) := by
  exact
    yieldBound_restrictBinaryGrammar
      (frontEndBinaryGrammar R)
      cert.support
      cert.closed
      (binarizedThicknessEnvelope 1 n τR)
      (frontEndSupport_yieldBoundOn
        R n τR cert hn hsource)

/-- The finite front-end grammar has exactly as many states as its support. -/
@[simp] theorem finiteFrontEnd_card
    (R : MixedRules N α)
    (n : Nat)
    (cert : FrontEndSupportCertificate R n) :
    Fintype.card (SupportedState cert.support) =
      cert.support.card := by
  exact supportedState_card cert.support

/--
Once the support cardinality is linearly bounded, the complete verified
thickness back end of Proposition 7.4 applies to the finite front-end grammar.
-/
theorem finiteFrontEnd_proposition74_thickness
    (R : MixedRules N α)
    (n τR cV : Nat)
    (cert : FrontEndSupportCertificate R n)
    (hn : 0 < n)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage R A)
        τR)
    (hcard :
      cert.support.card ≤ cV * n)
    {Nsurv Nfinal : Type (max u v)}
    (surv :
      Nsurv → SupportedState cert.support)
    (final : Nfinal → Nsurv)
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives
            (finiteFrontEndGrammar R n cert)
            (surv A) w})) :
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives
          (finiteFrontEndGrammar R n cert)
          (surv (final A)) w})
      (ssbnfThicknessEnvelope cV 1 n τR) := by
  have hV :
      Fintype.card (SupportedState cert.support) ≤
        cV * n := by
    simpa using hcard
  have hYield :
      YieldBound
        (fun X =>
          {w | BinaryNullableDerives
            (finiteFrontEndGrammar R n cert) X w})
        (binarizedThicknessEnvelope 1 n τR) :=
    finiteFrontEnd_yieldBound
      R n τR cert hn hsource
  exact
    proposition74_thickness_from_yieldBound
      (finiteFrontEndGrammar R n cert)
      surv final
      cV 1 n τR
      (binarizedThicknessEnvelope 1 n τR)
      hV
      (le_refl _)
      hYield
      hsurv

/--
Combined rule-count/thickness package for the finite front-end grammar.  The
front-end certificate supplies the state cardinality; the standard binary-first
epsilon/unit counting hypotheses supply the polynomial rule bound.
-/
theorem finiteFrontEnd_proposition74_package
    (R : MixedRules N α)
    (n τR cV cP cT vCount pCount tCount : Nat)
    (cert : FrontEndSupportCertificate R n)
    (hn : 0 < n)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage R A)
        τR)
    (hcard :
      cert.support.card ≤ cV * n)
    {Nsurv Nfinal : Type (max u v)}
    (surv :
      Nsurv → SupportedState cert.support)
    (final : Nfinal → Nsurv)
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives
            (finiteFrontEndGrammar R n cert)
            (surv A) w}))
    (hv : vCount ≤ cV * n)
    (hp : pCount ≤ cP * n)
    (ht : tCount ≤ cT * n) :
    vCount * (tCount + 3 * pCount) ≤
        (cV * (cT + 3 * cP)) * n^2
    ∧
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives
          (finiteFrontEndGrammar R n cert)
          (surv (final A)) w})
      (ssbnfThicknessEnvelope cV 1 n τR) := by
  constructor
  · exact proposition74_rule_count_facade hv hp ht
  · exact
      finiteFrontEnd_proposition74_thickness
        R n τR cV cert hn hsource hcard
        surv final hsurv

end FrontEndFiniteSupportFacade

end TCS1
end LeanCfgProject
