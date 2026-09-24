import LeanCfgProject.TCS1.LinearRawFinitePreprocessing
import LeanCfgProject.TCS1.PreparedLinearGrammarSemantics

/-!
# TCS #1: semantic bridge from raw unit-free rules to the finite prepared CFG

LinearRawFinitePreprocessing constructs the finite prepared grammar obtained
after linear epsilon elimination and unit-closure copying. This module proves
that the construction has exactly the semantic unit-free derivation relation
from LinearRawEpsilonUnitSemantics.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section LinearRawUnitFreePreparedBridge

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable [Fintype N] [Fintype P]

/--
A prepared grammar rule whose RHS is the deterministic dropped-core rule
derives exactly the surviving terminal context.
-/
theorem preparedLinearDerives_droppedCore
    (G : RawLinearIndexedCFG N α P)
    (q : RawLinearPreparedRuleIndex G)
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ [])
    (hrhs :
      (rawLinearPreparedGrammar G).rhs q =
        droppedCorePreparedRhs
          (N := N) left right hnonunit) :
    PreparedLinearDerives
      (rawLinearPreparedGrammar G)
      ((rawLinearPreparedGrammar G).lhs q)
      (left ++ right) := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact False.elim
            (hnonunit.elim
              (fun h => h rfl)
              (fun h => h rfl))
      | cons b rest =>
          exact
            PreparedLinearDerives.terminals
              q b rest
              (by
                simpa [droppedCorePreparedRhs]
                  using hrhs)
  | cons a rest =>
      have d :=
        PreparedLinearDerives.terminals
          (G := rawLinearPreparedGrammar G)
          q a (rest ++ right)
          (by
            simpa [droppedCorePreparedRhs]
              using hrhs)
      simpa using d

/--
Every semantic unit-free derivation is reproduced by the finite prepared
grammar.
-/
theorem rawLinearUnitFreeDerives_to_prepared
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d : RawLinearUnitFreeDerives G A word) :
    PreparedLinearDerives
      (rawLinearPreparedGrammar G) A word := by
  induction d with
  | terminals A p head tail hreach hrhs =>
      have hproduce :
          RawLinearCoreVariantProduces G
            (p, false)
            (PreparedLinearRhs.terminals
              head tail) :=
        RawLinearCoreVariantProduces.keep
          p _ hrhs
      have hvalid :
          RawLinearCoreVariantValid G (p, false) :=
        ⟨_, hproduce⟩
      let coreq : RawLinearCoreRuleIndex G :=
        ⟨(p, false), hvalid⟩
      let q : RawLinearPreparedRuleIndex G :=
        ⟨(A, coreq), hreach⟩
      have hcore :
          rawLinearCorePreparedRhs G coreq =
            PreparedLinearRhs.terminals
              head tail := by
        exact
          rawLinearCorePreparedRhs_eq_of_produces
            G coreq hproduce
      have dq :
          PreparedLinearDerives
            (rawLinearPreparedGrammar G)
            ((rawLinearPreparedGrammar G).lhs q)
            (head :: tail) :=
        PreparedLinearDerives.terminals
          q head tail
          (by
            change
              rawLinearCorePreparedRhs G coreq =
                PreparedLinearRhs.terminals head tail
            exact hcore)
      simpa [rawLinearPreparedGrammar, q, coreq]
        using dq

  | @around A p left core right hnonunit hreach hrhs word child ih =>
      have hproduce :
          RawLinearCoreVariantProduces G
            (p, false)
            (PreparedLinearRhs.around
              left core right hnonunit) :=
        RawLinearCoreVariantProduces.keep
          p _ hrhs
      have hvalid :
          RawLinearCoreVariantValid G (p, false) :=
        ⟨_, hproduce⟩
      let coreq : RawLinearCoreRuleIndex G :=
        ⟨(p, false), hvalid⟩
      let q : RawLinearPreparedRuleIndex G :=
        ⟨(A, coreq), hreach⟩
      have hcore :
          rawLinearCorePreparedRhs G coreq =
            PreparedLinearRhs.around
              left core right hnonunit := by
        exact
          rawLinearCorePreparedRhs_eq_of_produces
            G coreq hproduce
      have dq :
          PreparedLinearDerives
            (rawLinearPreparedGrammar G)
            ((rawLinearPreparedGrammar G).lhs q)
            (left ++ word ++ right) :=
        PreparedLinearDerives.around
          q left core right hnonunit
          (by
            change
              rawLinearCorePreparedRhs G coreq =
                PreparedLinearRhs.around
                  left core right hnonunit
            exact hcore)
          ih
      simpa [rawLinearPreparedGrammar, q, coreq]
        using dq

  | dropCore A p left core right hnonunit hreach hrhs hnullable =>
      have hproduce :
          RawLinearCoreVariantProduces G
            (p, true)
            (droppedCorePreparedRhs
              (N := N) left right hnonunit) :=
        RawLinearCoreVariantProduces.drop
          p left core right hnonunit
          hrhs hnullable
      have hvalid :
          RawLinearCoreVariantValid G (p, true) :=
        ⟨_, hproduce⟩
      let coreq : RawLinearCoreRuleIndex G :=
        ⟨(p, true), hvalid⟩
      let q : RawLinearPreparedRuleIndex G :=
        ⟨(A, coreq), hreach⟩
      have hcore :
          rawLinearCorePreparedRhs G coreq =
            droppedCorePreparedRhs
              (N := N) left right hnonunit := by
        exact
          rawLinearCorePreparedRhs_eq_of_produces
            G coreq hproduce
      have dq :=
        preparedLinearDerives_droppedCore
          G q left right hnonunit
          (by
            change
              rawLinearCorePreparedRhs G coreq =
                droppedCorePreparedRhs
                  (N := N) left right hnonunit
            exact hcore)
      simpa [rawLinearPreparedGrammar, q, coreq]
        using dq

/-- The dropped-core prepared RHS realizes exactly the surviving context. -/
theorem droppedCorePreparedRhs_realizes_iff
    (L : N → Set (List α))
    (left right : List α)
    (hnonunit : left ≠ [] ∨ right ≠ [])
    (word : List α) :
    PreparedLinearRhs.realizes L
        (droppedCorePreparedRhs
          (N := N) left right hnonunit)
        word
      ↔
    word = left ++ right := by
  cases left with
  | nil =>
      cases right with
      | nil =>
          exact False.elim
            (hnonunit.elim
              (fun h => h rfl)
              (fun h => h rfl))
      | cons b rest =>
          rfl
  | cons a rest =>
      rfl

/--
One produced finite core variant acts soundly on the semantic unit-free
language.  Keeping this lemma at the ambient (P × Bool) index avoids dependent
elimination on the finite subtype index.
-/
theorem rawLinearCoreVariantProduces_realizes_to_unitFree
    (G : RawLinearIndexedCFG N α P)
    {slot : P × Bool}
    {rhs : PreparedLinearRhs N α}
    (hproduce :
      RawLinearCoreVariantProduces G slot rhs)
    {A : N}
    (hreach :
      RawLinearUnitReach G A (G.lhs slot.1))
    {word : List α}
    (hreal :
      PreparedLinearRhs.realizes
        (fun B => {u | RawLinearUnitFreeDerives G B u})
        rhs word) :
    RawLinearUnitFreeDerives G A word := by
  cases hproduce with
  | keep p rhs hrhs =>
      cases rhs with
      | terminals head tail =>
          change word = head :: tail at hreal
          subst word
          exact
            RawLinearUnitFreeDerives.terminals
              A p head tail hreach hrhs
      | around left core right hnonunit =>
          change
            ∃ z,
              RawLinearUnitFreeDerives G core z
              ∧
              word = left ++ z ++ right
            at hreal
          rcases hreal with ⟨z, hz, rfl⟩
          exact
            RawLinearUnitFreeDerives.around
              A p left core right hnonunit
              hreach hrhs hz
  | drop p left core right hnonunit hrhs hnullable =>
      have hword :
          word = left ++ right :=
        (droppedCorePreparedRhs_realizes_iff
          (N := N)
          (fun B => {u | RawLinearUnitFreeDerives G B u})
          left right hnonunit word).1 hreal
      rw [hword]
      exact
        RawLinearUnitFreeDerives.dropCore
          A p left core right hnonunit
          hreach hrhs hnullable

/--
Every finite-prepared derivation expands to the semantic unit-free derivation
relation.
-/
theorem preparedDerives_to_rawLinearUnitFree
    (G : RawLinearIndexedCFG N α P)
    {A : N}
    {word : List α}
    (d :
      PreparedLinearDerives
        (rawLinearPreparedGrammar G) A word) :
    RawLinearUnitFreeDerives G A word := by
  induction d with
  | terminals q head tail hrhs =>
      rcases q with
        ⟨⟨A, coreq⟩, hreach⟩
      change RawLinearUnitFreeDerives G A (head :: tail)
      have hproduce :=
        rawLinearCorePreparedRhs_spec G coreq
      change
        rawLinearCorePreparedRhs G coreq =
          PreparedLinearRhs.terminals head tail
        at hrhs
      rw [hrhs] at hproduce
      apply
        rawLinearCoreVariantProduces_realizes_to_unitFree
          G hproduce hreach
      rfl
  | @around q left core right hnonunit hrhs word child ih =>
      rcases q with
        ⟨⟨A, coreq⟩, hreach⟩
      change
        RawLinearUnitFreeDerives G A
          (left ++ word ++ right)
      have hproduce :=
        rawLinearCorePreparedRhs_spec G coreq
      change
        rawLinearCorePreparedRhs G coreq =
          PreparedLinearRhs.around
            left core right hnonunit
        at hrhs
      rw [hrhs] at hproduce
      apply
        rawLinearCoreVariantProduces_realizes_to_unitFree
          G hproduce hreach
      exact ⟨word, ih, rfl⟩

/-- Exact derivation equivalence for the finite prepared preprocessing output. -/
theorem rawLinearUnitFreeDerives_iff_prepared
    (G : RawLinearIndexedCFG N α P)
    (A : N)
    (word : List α) :
    RawLinearUnitFreeDerives G A word
      ↔
    PreparedLinearDerives
      (rawLinearPreparedGrammar G) A word := by
  constructor
  · exact rawLinearUnitFreeDerives_to_prepared G
  · exact preparedDerives_to_rawLinearUnitFree G

end LinearRawUnitFreePreparedBridge

end TCS1
end LeanCfgProject
