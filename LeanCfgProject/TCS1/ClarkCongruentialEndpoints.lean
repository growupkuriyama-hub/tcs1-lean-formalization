import LeanCfgProject.TCS1.ClarkCongruentialPackaging

/-!
# TCS #1 v78: degenerate congruential endpoints

The proof of Proposition 9.9 treats the empty language separately before the
typed-refinement argument.  The normalization-based facade also assumes a
nonempty terminal word, so the epsilon-only target is a second endpoint at the
formalization level.

This file gives explicit one-state congruential grammars for both endpoints.
-/

namespace LeanCfgProject
namespace TCS1

universe u

section ClarkCongruentialEndpoints

variable {α : Type u}

/-- Single state used for the degenerate endpoint grammars. -/
inductive ClarkEndpointState where
  | root
  deriving DecidableEq, Fintype, Repr

/-- The unique initial state. -/
def clarkEndpointInitial :
    Set ClarkEndpointState :=
  {A | A = .root}

theorem clarkEndpointInitial_finite :
    clarkEndpointInitial.Finite := by
  exact Set.toFinite _

/-- One initial nonterminal with no productions: the empty-language witness. -/
def clarkEmptyGrammar :
    BinaryNullableGrammar ClarkEndpointState α where
  terminalRule _ _ := False
  binaryRule _ _ _ := False
  epsilonRule _ := False
  unitRule _ _ := False

theorem clarkEmptyGrammar_no_derives
    {A : ClarkEndpointState}
    {w : Word α} :
    ¬ BinaryNullableDerives clarkEmptyGrammar A w := by
  intro d
  cases d with
  | terminal h =>
      exact h.elim
  | epsilon h =>
      exact h.elim
  | unit h _ =>
      exact h.elim
  | binary h _ _ =>
      exact h.elim

/-- Exact language of the empty endpoint grammar. -/
theorem clarkEmptyGrammar_language_eq :
    InitialSetLanguage
        clarkEmptyGrammar
        clarkEndpointInitial
      =
    (∅ : Set (Word α)) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨A, hA, d⟩
    exact False.elim
      (clarkEmptyGrammar_no_derives d)
  · intro hw
    exact False.elim (by simpa using hw)

/-- The empty endpoint grammar is congruential vacuously. -/
theorem clarkEmptyGrammar_congruential :
    ClarkCongruentialInitialSet
      (clarkEmptyGrammar (α := α))
      clarkEndpointInitial := by
  intro A x y dx dy
  exact False.elim
    (clarkEmptyGrammar_no_derives (α := α) dx)

/-- Empty-language endpoint of Proposition 9.9. -/
theorem clark_empty_endpoint :
    clarkEndpointInitial.Finite
      ∧
    InitialSetLanguage
        clarkEmptyGrammar
        clarkEndpointInitial
      =
    (∅ : Set (Word α))
      ∧
    ClarkCongruentialInitialSet
      (clarkEmptyGrammar (α := α))
      clarkEndpointInitial := by
  exact
    ⟨clarkEndpointInitial_finite,
      clarkEmptyGrammar_language_eq,
      clarkEmptyGrammar_congruential⟩

/--
One initial nonterminal with only an epsilon production: the epsilon-only
endpoint witness.
-/
def clarkEpsilonGrammar :
    BinaryNullableGrammar ClarkEndpointState α where
  terminalRule _ _ := False
  binaryRule _ _ _ := False
  epsilonRule A := A = .root
  unitRule _ _ := False

/-- The epsilon endpoint state derives exactly the empty word. -/
theorem clarkEpsilonGrammar_derives_iff
    (w : Word α) :
    BinaryNullableDerives
        clarkEpsilonGrammar
        .root w
      ↔
    w = [] := by
  constructor
  · intro d
    cases d with
    | terminal h =>
        exact False.elim h
    | epsilon h =>
        rfl
    | unit h _ =>
        exact False.elim h
    | binary h _ _ =>
        exact False.elim h
  · rintro rfl
    exact BinaryNullableDerives.epsilon rfl

/-- Exact language of the epsilon-only endpoint grammar. -/
theorem clarkEpsilonGrammar_language_eq :
    InitialSetLanguage
        clarkEpsilonGrammar
        clarkEndpointInitial
      =
    ({[]} : Set (Word α)) := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨A, hA, d⟩
    have hroot : A = ClarkEndpointState.root := hA
    subst A
    have hw0 :=
      (clarkEpsilonGrammar_derives_iff w).1 d
    simpa [hw0]
  · intro hw
    have hw0 : w = [] := by
      simpa using hw
    subst w
    exact
      ⟨ClarkEndpointState.root,
        rfl,
        BinaryNullableDerives.epsilon rfl⟩

/-- The epsilon-only endpoint grammar is congruential. -/
theorem clarkEpsilonGrammar_congruential :
    ClarkCongruentialInitialSet
      (clarkEpsilonGrammar (α := α))
      clarkEndpointInitial := by
  intro A x y dx dy
  cases A with
  | root =>
      have hx :
          x = [] :=
        (clarkEpsilonGrammar_derives_iff (α := α) x).1 dx
      have hy :
          y = [] :=
        (clarkEpsilonGrammar_derives_iff (α := α) y).1 dy
      subst x
      subst y
      rfl

/-- Epsilon-only endpoint of the normalized inclusion theorem. -/
theorem clark_epsilon_endpoint :
    clarkEndpointInitial.Finite
      ∧
    InitialSetLanguage
        clarkEpsilonGrammar
        clarkEndpointInitial
      =
    ({[]} : Set (Word α))
      ∧
    ClarkCongruentialInitialSet
      (clarkEpsilonGrammar (α := α))
      clarkEndpointInitial := by
  exact
    ⟨clarkEndpointInitial_finite,
      clarkEpsilonGrammar_language_eq,
      clarkEpsilonGrammar_congruential⟩

end ClarkCongruentialEndpoints

end TCS1
end LeanCfgProject
