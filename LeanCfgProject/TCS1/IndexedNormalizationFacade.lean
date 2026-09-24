import LeanCfgProject.TCS1.IndexedFrontRuleClosure
import LeanCfgProject.TCS1.Proposition74Facade

/-!
# TCS #1 v66: direct indexed-CFG normalization facade

The preceding modules now construct the finite front-end support from an
indexed finite CFG and prove it rule-closed.  This file removes the remaining
certificate plumbing.

We use the explicit encoding scale

  n_G = |N| + |Sigma| + |P| + totalRhsLength(G).

Every source RHS has length at most n_G, and the closed front-end support has
cardinality at most n_G.  Hence the terminal-isolation/binarization front end
has a uniform yield bound n_G * (tau_R + 1) on a genuinely finite binary
grammar.  The verified epsilon/unit-elimination back end then gives the
quadratic SSBNF thickness envelope.

Thus, modulo the later concrete trim/reducedness representation layer, the
quantitative semantic core of Proposition 7.4 is now launched directly from a
finite indexed source CFG rather than from an externally supplied support.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedNormalizationFacade

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/-- Explicit finite encoding scale used by the direct normalization facade. -/
def IndexedMixedCFG.normalizationScale
    (G : IndexedMixedCFG N α P) : Nat :=
  Fintype.card N +
    Fintype.card α +
    Fintype.card P +
    G.totalRhsLength

/-- Every individual source RHS length is bounded by the total RHS length. -/
theorem indexed_rhs_length_le_total
    (G : IndexedMixedCFG N α P)
    (p : P) :
    (G.rhs p).length ≤ G.totalRhsLength := by
  classical
  have h :
      (G.rhs p).length ≤
        ∑ q : P, (G.rhs q).length := by
    exact
      Finset.single_le_sum
        (fun q hq => Nat.zero_le ((G.rhs q).length))
        (Finset.mem_univ p)
  simpa [IndexedMixedCFG.totalRhsLength] using h

/-- Every source RHS is bounded by the full normalization scale. -/
theorem indexed_rhs_length_le_normalizationScale
    (G : IndexedMixedCFG N α P)
    (p : P) :
    (G.rhs p).length ≤ G.normalizationScale := by
  have htotal := indexed_rhs_length_le_total G p
  unfold IndexedMixedCFG.normalizationScale
  omega

/-- The closed front-end support is bounded by the same encoding scale. -/
theorem indexedClosedFrontSupport_card_le_normalizationScale
    (G : IndexedMixedCFG N α P) :
    (indexedClosedFrontSupport G).card ≤
      G.normalizationScale := by
  have hcard :=
    indexedClosedFrontSupport_card_le G
  unfold IndexedMixedCFG.normalizationScale
  omega

/--
The support certificate is now constructed automatically from the finite
indexed CFG.
-/
def indexedNormalizationSupportCertificate
    (G : IndexedMixedCFG N α P) :
    FrontEndSupportCertificate
      G.toMixedRules
      G.normalizationScale :=
  indexedFrontSupportCertificate
    G
    G.normalizationScale
    (indexed_rhs_length_le_normalizationScale G)

/-- The genuinely finite binary grammar produced by the semantic front end. -/
def indexedFiniteFrontEndGrammar
    (G : IndexedMixedCFG N α P) :
    BinaryNullableGrammar
      (SupportedState
        (indexedNormalizationSupportCertificate G).support) α :=
  finiteFrontEndGrammar
    G.toMixedRules
    G.normalizationScale
    (indexedNormalizationSupportCertificate G)

/--
The finite front-end grammar inherits the linear terminal-yield bound directly
from the source thickness assumption.
-/
theorem indexedFiniteFrontEnd_yieldBound
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR) :
    YieldBound
      (fun X =>
        {w | BinaryNullableDerives
          (indexedFiniteFrontEndGrammar G) X w})
      (binarizedThicknessEnvelope
        1 G.normalizationScale τR) := by
  exact
    finiteFrontEnd_yieldBound
      G.toMixedRules
      G.normalizationScale
      τR
      (indexedNormalizationSupportCertificate G)
      hn
      hsource

/-- The finite front-end state count is at most one copy of the encoding scale. -/
theorem indexedFiniteFrontEnd_card_le_scale
    (G : IndexedMixedCFG N α P) :
    Fintype.card
        (SupportedState
          (indexedNormalizationSupportCertificate G).support)
      ≤
    G.normalizationScale := by
  calc
    Fintype.card
        (SupportedState
          (indexedNormalizationSupportCertificate G).support)
      =
    (indexedNormalizationSupportCertificate G).support.card :=
      supportedState_card
        (indexedNormalizationSupportCertificate G).support
    _ =
    (indexedClosedFrontSupport G).card := by
      rfl
    _ ≤ G.normalizationScale :=
      indexedClosedFrontSupport_card_le_normalizationScale G

/--
Direct paper-facing thickness theorem from a finite indexed source CFG.

No external finite-support or cycle-shortening assumption remains.
-/
theorem indexed_proposition74_thickness
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR)
    {Nsurv Nfinal : Type (max u v)}
    (surv :
      Nsurv →
        SupportedState
          (indexedNormalizationSupportCertificate G).support)
    (final : Nfinal → Nsurv)
    (hsurv :
      AllHaveNonemptyYield
        (fun A : Nsurv =>
          {w | EpsilonFreeDerives
            (indexedFiniteFrontEndGrammar G)
            (surv A) w})) :
    YieldBound
      (fun A : Nfinal =>
        {w | UnitFreeDerives
          (indexedFiniteFrontEndGrammar G)
          (surv (final A)) w})
      (ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR) := by
  have hV :
      Fintype.card
          (SupportedState
            (indexedNormalizationSupportCertificate G).support)
        ≤
      1 * G.normalizationScale := by
    simpa using indexedFiniteFrontEnd_card_le_scale G
  have hYield :
      YieldBound
        (fun X =>
          {w | BinaryNullableDerives
            (indexedFiniteFrontEndGrammar G) X w})
        (binarizedThicknessEnvelope
          1 G.normalizationScale τR) :=
    indexedFiniteFrontEnd_yieldBound
      G τR hn hsource
  exact
    proposition74_thickness_from_yieldBound
      (indexedFiniteFrontEndGrammar G)
      surv final
      1 1
      G.normalizationScale
      τR
      (binarizedThicknessEnvelope
        1 G.normalizationScale τR)
      hV
      (le_refl _)
      hYield
      hsurv

/--
Explicit arithmetic form of the direct thickness theorem:
the final witness bound is at most 1 + n_G^2 * (tau_R + 1).
-/
theorem indexed_proposition74_explicit_envelope
    (G : IndexedMixedCFG N α P)
    (τR : Nat) :
    ssbnfThicknessEnvelope
        1 1 G.normalizationScale τR
      =
    1 + G.normalizationScale^2 * thicknessBar τR := by
  unfold ssbnfThicknessEnvelope
  ring

end IndexedNormalizationFacade

end TCS1
end LeanCfgProject
