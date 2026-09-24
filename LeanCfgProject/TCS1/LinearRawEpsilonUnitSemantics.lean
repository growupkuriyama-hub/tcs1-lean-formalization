import LeanCfgProject.TCS1.LinearRawPreprocessing
import LeanCfgProject.TCS1.BinaryUnitElimination

/-!
# TCS #1: epsilon and unit elimination for raw linear grammars

For a genuinely linear right-hand side u B v there is only one possible
nonterminal deletion during epsilon elimination: if B is nullable, add the
terminal-only rule u v.  Because the prepared case excludes units, u v is
nonempty.  Thus epsilon elimination preserves linearity without introducing
new unit rules.

Unit elimination is then the usual unit-closure copying of the remaining
prepared rules.  This file proves both semantic equivalences directly:

  raw derivation of nonempty w  <->  epsilon-free derivation of w
  epsilon-free derivation       <->  unit-free derivation.

These are the semantic preprocessing facts needed before the verified
linear-spine factorization.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawEpsilonUnitSemantics

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Explicit derivations of the raw linear indexed grammar. -/
inductive RawLinearDerives
    (G : RawLinearIndexedCFG N α P) :
    N → List α → Prop
  | epsilon
      (p : P)
      (hrhs : G.rhs p = RawLinearRhs.epsilon) :
      RawLinearDerives G (G.lhs p) []
  | unit
      (p : P)
      (B : N)
      (hrhs : G.rhs p = RawLinearRhs.unit B)
      {word : List α}
      (child : RawLinearDerives G B word) :
      RawLinearDerives G (G.lhs p) word
  | terminals
      (p : P)
      (head : α)
      (tail : List α)
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.terminals head tail)) :
      RawLinearDerives G
        (G.lhs p) (head :: tail)
  | around
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit))
      {word : List α}
      (child : RawLinearDerives G core word) :
      RawLinearDerives G
        (G.lhs p) (left ++ word ++ right)

/-- The explicit raw derivation language is closed under every raw rule. -/
theorem rawLinearDerives_closed
    (G : RawLinearIndexedCFG N α P) :
    RawLinearGrammarClosed G
      (fun A => {word | RawLinearDerives G A word}) := by
  intro p word hreal
  cases hrhs : G.rhs p with
  | epsilon =>
      rw [hrhs] at hreal
      change word = [] at hreal
      subst word
      exact RawLinearDerives.epsilon p hrhs
  | unit B =>
      rw [hrhs] at hreal
      change RawLinearDerives G B word at hreal
      exact RawLinearDerives.unit p B hrhs hreal
  | prepared rhs =>
      cases rhs with
      | terminals head tail =>
          rw [hrhs] at hreal
          change word = head :: tail at hreal
          subst word
          exact RawLinearDerives.terminals p head tail hrhs
      | around left core right hnonunit =>
          rw [hrhs] at hreal
          change ∃ z,
            RawLinearDerives G core z ∧
            word = left ++ z ++ right at hreal
          rcases hreal with ⟨z, hz, rfl⟩
          exact
            RawLinearDerives.around
              p left core right hnonunit hrhs hz

/-- Every explicit raw derivation lies in every raw-closed family. -/
theorem rawLinearDerives_mem_of_closed
    (G : RawLinearIndexedCFG N α P)
    (L : N → Set (List α))
    (hclosed : RawLinearGrammarClosed G L)
    {A : N}
    {word : List α}
    (d : RawLinearDerives G A word) :
    word ∈ L A := by
  induction d with
  | epsilon p hrhs =>
      apply hclosed p []
      rw [hrhs]
      rfl
  | @unit p B hrhs word child ih =>
      apply hclosed p word
      rw [hrhs]
      exact ih
  | terminals p head tail hrhs =>
      apply hclosed p (head :: tail)
      rw [hrhs]
      rfl
  | @around p left core right hnonunit hrhs word child ih =>
      apply hclosed p (left ++ word ++ right)
      rw [hrhs]
      exact ⟨word, ih, rfl⟩

/-- Explicit raw derivability equals the least-closed semantics. -/
theorem rawLinearDerives_iff_least
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    RawLinearDerives G A word
      ↔
    word ∈ RawLinearLeastLanguage G A := by
  constructor
  · intro d L hclosed
    exact rawLinearDerives_mem_of_closed G L hclosed d
  · intro hleast
    exact
      hleast
        (fun B => {u | RawLinearDerives G B u})
        (rawLinearDerives_closed G)

/-- Nullability before epsilon elimination. -/
def RawLinearNullable
    (G : RawLinearIndexedCFG N α P)
    (A : N) : Prop :=
  RawLinearDerives G A []

/--
Derivations after deleting raw epsilon rules.  A nullable core of u B v may
be deleted, producing the nonempty terminal word u v.
-/
inductive RawLinearEpsilonFreeDerives
    (G : RawLinearIndexedCFG N α P) :
    N → List α → Prop
  | unit
      (p : P)
      (B : N)
      (hrhs : G.rhs p = RawLinearRhs.unit B)
      {word : List α}
      (child : RawLinearEpsilonFreeDerives G B word) :
      RawLinearEpsilonFreeDerives G (G.lhs p) word
  | terminals
      (p : P)
      (head : α)
      (tail : List α)
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.terminals head tail)) :
      RawLinearEpsilonFreeDerives G
        (G.lhs p) (head :: tail)
  | around
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit))
      {word : List α}
      (child : RawLinearEpsilonFreeDerives G core word) :
      RawLinearEpsilonFreeDerives G
        (G.lhs p) (left ++ word ++ right)
  | dropCore
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit))
      (hnullable : RawLinearNullable G core) :
      RawLinearEpsilonFreeDerives G
        (G.lhs p) (left ++ right)

/-- Every epsilon-free linear derivation yields a nonempty word. -/
theorem rawLinearEpsilonFreeDerives_nonempty
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearEpsilonFreeDerives G A word) :
    word ≠ [] := by
  induction d with
  | unit p B hrhs child ih =>
      exact ih
  | terminals p head tail hrhs =>
      simp
  | @around p left core right hnonunit hrhs word child ih =>
      intro hnil
      have houter :
          left ++ word = [] ∧ right = [] :=
        List.append_eq_nil_iff.mp hnil
      have hinner :
          left = [] ∧ word = [] :=
        List.append_eq_nil_iff.mp houter.1
      exact ih hinner.2
  | dropCore p left core right hnonunit hrhs hnullable =>
      intro hnil
      have hparts :
          left = [] ∧ right = [] :=
        List.append_eq_nil_iff.mp hnil
      exact hnonunit.elim
        (fun h => h hparts.1)
        (fun h => h hparts.2)

/-- Every nonempty raw derivation survives epsilon elimination. -/
theorem rawLinearDerives_to_epsilonFree
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearDerives G A word)
    (hne : word ≠ []) :
    RawLinearEpsilonFreeDerives G A word := by
  induction d with
  | epsilon p hrhs =>
      exact False.elim (hne rfl)
  | @unit p B hrhs word child ih =>
      exact
        RawLinearEpsilonFreeDerives.unit
          p B hrhs (ih hne)
  | terminals p head tail hrhs =>
      exact
        RawLinearEpsilonFreeDerives.terminals
          p head tail hrhs
  | @around p left core right hnonunit hrhs childWord child ih =>
      by_cases hchild : childWord = []
      · subst childWord
        simpa using
          (RawLinearEpsilonFreeDerives.dropCore
            p left core right hnonunit hrhs child)
      · exact
          RawLinearEpsilonFreeDerives.around
            p left core right hnonunit hrhs
            (ih hchild)

/-- Every epsilon-free derivation expands to a raw derivation. -/
theorem rawLinearEpsilonFreeDerives_to_raw
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearEpsilonFreeDerives G A word) :
    RawLinearDerives G A word := by
  induction d with
  | unit p B hrhs child ih =>
      exact RawLinearDerives.unit p B hrhs ih
  | terminals p head tail hrhs =>
      exact RawLinearDerives.terminals p head tail hrhs
  | around p left core right hnonunit hrhs child ih =>
      exact
        RawLinearDerives.around
          p left core right hnonunit hrhs ih
  | dropCore p left core right hnonunit hrhs hnullable =>
      simpa using
        (RawLinearDerives.around
          p left core right hnonunit hrhs hnullable)

/-- Exact nonempty-language preservation by linear epsilon elimination. -/
theorem rawLinear_epsilon_elimination_preserves_nonempty
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α)
    (hne : word ≠ []) :
    RawLinearDerives G A word
      ↔
    RawLinearEpsilonFreeDerives G A word := by
  constructor
  · intro d
    exact rawLinearDerives_to_epsilonFree G d hne
  · intro d
    exact rawLinearEpsilonFreeDerives_to_raw G d

/-- Original unit edge of the raw linear grammar. -/
def RawLinearUnitRule
    (G : RawLinearIndexedCFG N α P)
    (A B : N) : Prop :=
  ∃ p : P,
    G.lhs p = A ∧
    G.rhs p = RawLinearRhs.unit B

/-- Unit-closure reachability used by the copied unit-free grammar. -/
abbrev RawLinearUnitReach
    (G : RawLinearIndexedCFG N α P) :=
  UnitReach (RawLinearUnitRule G)

/--
Unit-free derivations after copying every non-unit epsilon-free rule to all
unit-reachable sources.
-/
inductive RawLinearUnitFreeDerives
    (G : RawLinearIndexedCFG N α P) :
    N → List α → Prop
  | terminals
      (A : N)
      (p : P)
      (head : α)
      (tail : List α)
      (hreach : RawLinearUnitReach G A (G.lhs p))
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.terminals head tail)) :
      RawLinearUnitFreeDerives G
        A (head :: tail)
  | around
      (A : N)
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hreach : RawLinearUnitReach G A (G.lhs p))
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit))
      {word : List α}
      (child : RawLinearUnitFreeDerives G core word) :
      RawLinearUnitFreeDerives G
        A (left ++ word ++ right)
  | dropCore
      (A : N)
      (p : P)
      (left : List α)
      (core : N)
      (right : List α)
      (hnonunit : left ≠ [] ∨ right ≠ [])
      (hreach : RawLinearUnitReach G A (G.lhs p))
      (hrhs :
        G.rhs p =
          RawLinearRhs.prepared
            (PreparedLinearRhs.around
              left core right hnonunit))
      (hnullable : RawLinearNullable G core) :
      RawLinearUnitFreeDerives G
        A (left ++ right)

/-- Prefixing a unit-closure path changes the root of a unit-free derivation. -/
theorem rawLinearUnitFreeDerives_of_unitReach
    (G : RawLinearIndexedCFG N α P)
    {A B : N}
    {word : List α}
    (hAB : RawLinearUnitReach G A B)
    (d : RawLinearUnitFreeDerives G B word) :
    RawLinearUnitFreeDerives G A word := by
  induction d with
  | terminals B p head tail hreach hrhs =>
      exact
        RawLinearUnitFreeDerives.terminals
          A p head tail
          (UnitReach.trans hAB hreach) hrhs
  | @around B p left core right hnonunit hreach hrhs word child ih =>
      exact
        RawLinearUnitFreeDerives.around
          A p left core right hnonunit
          (UnitReach.trans hAB hreach)
          hrhs child
  | dropCore B p left core right hnonunit hreach hrhs hnullable =>
      exact
        RawLinearUnitFreeDerives.dropCore
          A p left core right hnonunit
          (UnitReach.trans hAB hreach)
          hrhs hnullable

/-- Lift an epsilon-free derivation backward along a raw unit path. -/
theorem rawLinearEpsilonFreeDerives_of_unitReach
    (G : RawLinearIndexedCFG N α P)
    {A B : N}
    {word : List α}
    (hAB : RawLinearUnitReach G A B)
    (d : RawLinearEpsilonFreeDerives G B word) :
    RawLinearEpsilonFreeDerives G A word := by
  induction hAB with
  | refl A =>
      exact d
  | @step A B C hunit hBC ih =>
      rcases hunit with ⟨p, hlhs, hrhs⟩
      subst A
      exact
        RawLinearEpsilonFreeDerives.unit
          p B hrhs (ih d)

/-- Collapse explicit unit chains into copied non-unit root rules. -/
theorem rawLinearEpsilonFreeDerives_to_unitFree
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearEpsilonFreeDerives G A word) :
    RawLinearUnitFreeDerives G A word := by
  induction d with
  | @unit p B hrhs word child ih =>
      have hedge :
          RawLinearUnitRule G (G.lhs p) B :=
        ⟨p, rfl, hrhs⟩
      exact
        rawLinearUnitFreeDerives_of_unitReach
          G (UnitReach.single hedge) ih
  | terminals p head tail hrhs =>
      exact
        RawLinearUnitFreeDerives.terminals
          (G.lhs p) p head tail
          (UnitReach.refl _) hrhs
  | @around p left core right hnonunit hrhs word child ih =>
      exact
        RawLinearUnitFreeDerives.around
          (G.lhs p) p left core right hnonunit
          (UnitReach.refl _) hrhs ih
  | dropCore p left core right hnonunit hrhs hnullable =>
      exact
        RawLinearUnitFreeDerives.dropCore
          (G.lhs p) p left core right hnonunit
          (UnitReach.refl _) hrhs hnullable

/-- Expand copied unit-free rules back through their unit-closure prefix. -/
theorem rawLinearUnitFreeDerives_to_epsilonFree
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearUnitFreeDerives G A word) :
    RawLinearEpsilonFreeDerives G A word := by
  induction d with
  | terminals A p head tail hreach hrhs =>
      exact
        rawLinearEpsilonFreeDerives_of_unitReach
          G hreach
          (RawLinearEpsilonFreeDerives.terminals
            p head tail hrhs)
  | @around A p left core right hnonunit hreach hrhs word child ih =>
      exact
        rawLinearEpsilonFreeDerives_of_unitReach
          G hreach
          (RawLinearEpsilonFreeDerives.around
            p left core right hnonunit hrhs ih)
  | dropCore A p left core right hnonunit hreach hrhs hnullable =>
      exact
        rawLinearEpsilonFreeDerives_of_unitReach
          G hreach
          (RawLinearEpsilonFreeDerives.dropCore
            p left core right hnonunit hrhs hnullable)

/-- Unit elimination preserves the epsilon-free language exactly. -/
theorem rawLinear_unit_elimination_preserves_language
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    RawLinearEpsilonFreeDerives G A word
      ↔
    RawLinearUnitFreeDerives G A word := by
  constructor
  · exact rawLinearEpsilonFreeDerives_to_unitFree G
  · exact rawLinearUnitFreeDerives_to_epsilonFree G

/--
Combined preprocessing equivalence: on nonempty terminal words, the original
raw linear grammar and the unit-free linear grammar have exactly the same
language.
-/
theorem rawLinear_preprocessing_preserves_nonempty
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α)
    (hne : word ≠ []) :
    RawLinearDerives G A word
      ↔
    RawLinearUnitFreeDerives G A word := by
  rw [rawLinear_epsilon_elimination_preserves_nonempty
    G A word hne]
  exact rawLinear_unit_elimination_preserves_language
    G A word

end LinearRawEpsilonUnitSemantics

end TCS1
end LeanCfgProject
