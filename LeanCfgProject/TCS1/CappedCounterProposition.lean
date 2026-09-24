import LeanCfgProject.TCS1.CappedCounterFiniteState
import LeanCfgProject.TCS1.CappedCounterPaperWitness

/-!
# TCS #1 v78: capped-counter proposition package

This file packages the two capped-counter statements from the regular
separation subsection in the same representation used elsewhere in the Lean
development.

For every cap rho the semantic language is regular and fixed-h substitutable
for the explicit transition monoid.  For rho >= 2 it fails every fixed
(k,l)-window condition, using the exact manuscript witness
(up down)^k up^(rho-1) #^l versus (up down)^k up^rho #^l.
-/

namespace LeanCfgProject
namespace TCS1
namespace CappedCounter

/-- Lean package corresponding to Proposition ctr-regular. -/
theorem proposition_ctr_regular
    (rho : Nat) :
    (FormalLanguage rho).IsRegular
      ∧
    FixedHSubstitutable
      (transitionMonoidHom rho)
      (Language rho) := by
  exact regular_and_fixedH rho

/-- Lean package corresponding to Theorem ctr-non-kl. -/
theorem theorem_ctr_non_kl
    (rho : Nat)
    (hrho : 2 ≤ rho) :
    ∀ k l : Nat,
      ¬ FixedWindowSubstitutable
          k l (Language rho) := by
  intro k l
  exact
    not_fixedWindowSubstitutable_paperWitness
      rho hrho k l

/--
Regular-separation witness, without introducing an additional Lean-level
definition of the manuscript's class union KL.
-/
theorem regular_fixedH_outside_every_fixedWindow
    (rho : Nat)
    (hrho : 2 ≤ rho) :
    (FormalLanguage rho).IsRegular
      ∧
    FixedHSubstitutable
      (transitionMonoidHom rho)
      (Language rho)
      ∧
    ∀ k l : Nat,
      ¬ FixedWindowSubstitutable
          k l (Language rho) := by
  exact
    ⟨isRegular rho,
      fixedHSubstitutable_transitionMonoid rho,
      theorem_ctr_non_kl rho hrho⟩

end CappedCounter
end TCS1
end LeanCfgProject
