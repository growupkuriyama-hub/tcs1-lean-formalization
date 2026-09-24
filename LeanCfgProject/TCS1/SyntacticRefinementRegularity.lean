import LeanCfgProject.TCS1.FixedHSubstitutability
import LeanCfgProject.TCS1.LinearSeparatorFixedH
import LeanCfgProject.TCS1.LinearSeparatorNonregular
import Mathlib.Computability.DFA

/-!
# TCS #1 v79: syntactic-refinement is strictly stronger than fixed-h substitutability

Section 3 observes that the sufficient condition

  ker(h)|_{Sigma+} refines the syntactic congruence of L

is not necessary for fixed-h substitutability.  The manuscript points to the
nonregular linear separator L_{±,e}: it is fixed-h substitutable for a
four-element typing, but its syntactic congruence has infinite index.

This module formalizes that paragraph without introducing a separate quotient
cardinality API.  We prove the equivalent finite-state consequence directly:
if equality of h-types on nonempty words always forces equality of complete
distributions, then L is regular.  A DFA with state space Option M remembers
whether the input is still empty and otherwise stores its h-value.

Applying the contrapositive to the already verified nonregular language
L_{±,e} gives the desired strictness witness.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section SyntacticRefinementRegularity

variable {α : Type u}
variable {M : Type} [Monoid M] [Fintype M]

/--
Finite DFA induced by a fixed typing when membership of nonempty words is
constant on h-fibres.  The none state is reserved for the empty input; after
the first symbol the state is some (h w).
-/
def syntacticRefinementDFA
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α)) :
    DFA α (Option M) where
  step q a :=
    match q with
    | none => some (H.h [a])
    | some m => some (m * H.h [a])
  start := none
  accept :=
    { q |
      match q with
      | none => ([] : Word α) ∈ L
      | some m =>
          ∃ w : Word α,
            w ≠ [] ∧ H.h w = m ∧ w ∈ L }

/-- From a nonempty state, reading w multiplies by h(w). -/
theorem syntacticRefinementDFA_evalFrom_some
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (m : M)
    (w : Word α) :
    (syntacticRefinementDFA H L).evalFrom
        (some m) w
      =
    some (m * H.h w) := by
  induction w generalizing m with
  | nil =>
      simp [syntacticRefinementDFA, H.map_nil]
  | cons a w ih =>
      rw [DFA.evalFrom_cons]
      change
        (syntacticRefinementDFA H L).evalFrom
            (some (m * H.h [a])) w
          =
        some (m * H.h (a :: w))
      rw [ih]
      rw [show a :: w = [a] ++ w by rfl,
        H.map_append]
      simp [mul_assoc]

/-- Every nonempty word reaches exactly the state carrying its h-value. -/
theorem syntacticRefinementDFA_eval_cons
    (H : FixedFiniteMonoidHom α M)
    (L : Set (Word α))
    (a : α)
    (w : Word α) :
    (syntacticRefinementDFA H L).eval
        (a :: w)
      =
    some (H.h (a :: w)) := by
  change
    (syntacticRefinementDFA H L).evalFrom
        none (a :: w)
      =
    some (H.h (a :: w))
  rw [DFA.evalFrom_cons]
  change
    (syntacticRefinementDFA H L).evalFrom
        (some (H.h [a])) w
      =
    some (H.h (a :: w))
  rw [syntacticRefinementDFA_evalFrom_some]
  rw [show a :: w = [a] ++ w by rfl,
    H.map_append]

/--
If the nonempty h-kernel refines full syntactic congruence, the language is
regular.

This is the formal finite-index consequence used by the manuscript's
"strictly weaker" observation.
-/
theorem isRegular_of_fixedH_type_refines_distribution
    (H : FixedFiniteMonoidHom α M)
    (L : Language α)
    (hrefines :
      ∀ x y : Word α,
        x ≠ [] →
        y ≠ [] →
        H.h x = H.h y →
        Distribution L x = Distribution L y) :
    L.IsRegular := by
  refine
    ⟨Option M, inferInstance,
      syntacticRefinementDFA H L, ?_⟩
  apply Set.ext
  intro w
  cases w with
  | nil =>
      rfl
  | cons a w =>
      have heval :=
        syntacticRefinementDFA_eval_cons
          H L a w
      change
        (syntacticRefinementDFA H L).eval
            (a :: w)
          ∈
        (syntacticRefinementDFA H L).accept
          ↔
        a :: w ∈ L
      rw [heval]
      change
        (∃ z : Word α,
            z ≠ [] ∧
            H.h z = H.h (a :: w) ∧
            z ∈ L)
          ↔
        a :: w ∈ L
      constructor
      · rintro ⟨z, hzne, hztype, hzL⟩
        have hdist :=
          hrefines z (a :: w)
            hzne (by simp) hztype
        have hzLset :
            (show Set (Word α) from L) z := by
          change L z at hzL
          exact hzL
        have hzctx :
            (([] : Word α), ([] : Word α)) ∈
              Distribution L z := by
          change
            (show Set (Word α) from L)
              (([] : Word α) ++ z ++ [])
          simpa using hzLset
        have hwctx :
            (([] : Word α), ([] : Word α)) ∈
              Distribution L (a :: w) := by
          rw [← hdist]
          exact hzctx
        have hwLset :
            (show Set (Word α) from L) (a :: w) := by
          change
            (show Set (Word α) from L)
              (([] : Word α) ++ (a :: w) ++ [])
            at hwctx
          simpa using hwctx
        change L (a :: w)
        exact hwLset
      · intro hwL
        exact
          ⟨a :: w, by simp, rfl, hwL⟩

/--
Contrapositive form: for a nonregular language, no finite typing can have its
nonempty kernel refine full syntactic congruence.
-/
theorem nonregular_has_same_type_distinct_distribution
    (H : FixedFiniteMonoidHom α M)
    (L : Language α)
    (hnonregular : ¬ L.IsRegular) :
    ¬ (∀ x y : Word α,
        x ≠ [] →
        y ≠ [] →
        H.h x = H.h y →
        Distribution L x = Distribution L y) := by
  intro hrefines
  exact
    hnonregular
      (isRegular_of_fixedH_type_refines_distribution
        H L hrefines)

/--
Paper-facing strictness witness from Section 3:
L_{±,e} is fixed-h substitutable for the explicit four-element typing, while
that typing's kernel on nonempty words does not refine the syntactic
congruence of L_{±,e}.
-/
theorem lpm_fixedH_without_syntactic_kernel_refinement :
    FixedHSubstitutable lpmTyping LpmLanguage
      ∧
    ¬ (∀ x y : Word LpmSymbol,
        x ≠ [] →
        y ≠ [] →
        lpmTyping.h x = lpmTyping.h y →
        Distribution LpmLanguage x =
          Distribution LpmLanguage y) := by
  refine ⟨lpm_fixedHSubstitutable, ?_⟩
  exact
    nonregular_has_same_type_distinct_distribution
      lpmTyping
      LpmFormalLanguage
      lpm_not_regular

end SyntacticRefinementRegularity

end TCS1
end LeanCfgProject
