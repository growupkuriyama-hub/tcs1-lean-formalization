import LeanCfgProject.TCS1.V83LevelCodedIndexedGrammarExact
import LeanCfgProject.TCS1.V83LevelCodedMinusIndexedGrammarExact
import Mathlib.Data.Nat.Init

/-!
# TCS #1 v83: reducedness and ordinary-thickness certificates

This module supplies the representation-layer facts used in the manuscript's
ordinary-thickness lower bound.  Reducedness is expressed in the standard
graph/semantic form: every nonterminal is reachable from the designated start
and has a terminal yield.  The concrete indexed grammars R_n and R_n^- satisfy
that condition, and every state has a terminal yield of the claimed linear
length.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

/-- Reachability in the nonterminal dependency graph of an indexed CFG. -/
inductive IndexedMixedReachable
    {N : Type u} {α : Type v} {P : Type w}
    (G : IndexedMixedCFG N α P)
    (S : N) : N → Prop
  | start :
      IndexedMixedReachable G S S
  | child
      {A B : N} {p : P}
      (hA : IndexedMixedReachable G S A)
      (hLhs : G.lhs p = A)
      (hmem : Sum.inl B ∈ G.rhs p) :
      IndexedMixedReachable G S B

/-- Semantic productivity of one indexed nonterminal. -/
def IndexedMixedProductive
    {N : Type u} {α : Type v} {P : Type w}
    (G : IndexedMixedCFG N α P)
    (A : N) : Prop :=
  ∃ w : List α,
    MixedDerives G.toMixedRules A w

/-- Standard reducedness certificate: all states reachable and productive. -/
def IndexedMixedReduced
    {N : Type u} {α : Type v} {P : Type w}
    (G : IndexedMixedCFG N α P)
    (S : N) : Prop :=
  (∀ A : N, IndexedMixedReachable G S A) ∧
  (∀ A : N, IndexedMixedProductive G A)

/-- Uniform upper bound on shortest productive yields of all states. -/
def IndexedMixedThicknessAtMost
    {N : Type u} {α : Type v} {P : Type w}
    (G : IndexedMixedCFG N α P)
    (B : Nat) : Prop :=
  ∀ A : N,
    ∃ w : List α,
      MixedDerives G.toMixedRules A w ∧
      w.length ≤ B

section R

/-- The top A_n state is immediately reachable from S in R_n. -/
theorem levelCodeRIndexed_topA_reachable
    (n : Nat) :
    IndexedMixedReachable
      (levelCodeRIndexedGrammar n)
      LevelCodeRNT.start
      (.a (levelCodeFinTop n)) := by
  exact
    IndexedMixedReachable.child
      (G := levelCodeRIndexedGrammar n)
      (S := LevelCodeRNT.start)
      (p := LevelCodeRProd.start)
      IndexedMixedReachable.start
      rfl
      (by simp [levelCodeRIndexedGrammar])

/-- If A_(k+1) is reachable, then A_k is reachable by the binary rule. -/
theorem levelCodeRIndexed_a_reachable_step
    (n k : Nat)
    (hk : k < n)
    (h :
      IndexedMixedReachable
        (levelCodeRIndexedGrammar n)
        LevelCodeRNT.start
        (.a (⟨k + 1, by omega⟩ :
          Fin (n + 1)))) :
    IndexedMixedReachable
      (levelCodeRIndexedGrammar n)
      LevelCodeRNT.start
      (.a (⟨k, by omega⟩ :
        Fin (n + 1))) := by
  let j : Fin n := ⟨k, hk⟩
  have hparent :
      levelCodeFinSucc j =
        (⟨k + 1, by omega⟩ :
          Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hchild :
      levelCodeFinEmbed j =
        (⟨k, by omega⟩ :
          Fin (n + 1)) := by
    apply Fin.ext
    rfl
  have hr :
      IndexedMixedReachable
        (levelCodeRIndexedGrammar n)
        LevelCodeRNT.start
        (.a (levelCodeFinEmbed j)) := by
    apply IndexedMixedReachable.child
      (G := levelCodeRIndexedGrammar n)
      (S := LevelCodeRNT.start)
      (p := LevelCodeRProd.aNode j)
      h
    · simp [levelCodeRIndexedGrammar, hparent]
    · simp [levelCodeRIndexedGrammar]
  simpa [hchild] using hr

/-- Every A_k with k<=n is reachable in R_n. -/
theorem levelCodeRIndexed_a_reachable
    (n k : Nat)
    (hk : k ≤ n) :
    IndexedMixedReachable
      (levelCodeRIndexedGrammar n)
      LevelCodeRNT.start
      (.a (⟨k, by omega⟩ :
        Fin (n + 1))) := by
  apply Nat.decreasingInduction
      (motive := fun i hi =>
        IndexedMixedReachable
          (levelCodeRIndexedGrammar n)
          LevelCodeRNT.start
          (.a (⟨i, by omega⟩ :
            Fin (n + 1))))
  · intro i hi hsucc
    exact levelCodeRIndexed_a_reachable_step
      n i hi hsucc
  · simpa [levelCodeFinTop] using
      levelCodeRIndexed_topA_reachable n
  · exact hk

/-- Every Z_k with k<=n is reachable from the reachable A_k shortcut rule. -/
theorem levelCodeRIndexed_z_reachable
    (n k : Nat)
    (hk : k ≤ n) :
    IndexedMixedReachable
      (levelCodeRIndexedGrammar n)
      LevelCodeRNT.start
      (.z (⟨k, by omega⟩ :
        Fin (n + 1))) := by
  let i : Fin (n + 1) := ⟨k, by omega⟩
  have hA :
      IndexedMixedReachable
        (levelCodeRIndexedGrammar n)
        LevelCodeRNT.start
        (.a i) := by
    simpa [i] using
      levelCodeRIndexed_a_reachable n k hk
  have hZ :
      IndexedMixedReachable
        (levelCodeRIndexedGrammar n)
        LevelCodeRNT.start
        (.z i) := by
    apply IndexedMixedReachable.child
      (G := levelCodeRIndexedGrammar n)
      (S := LevelCodeRNT.start)
      (p := LevelCodeRProd.aShortcut i)
      hA
    · rfl
    · simp [levelCodeRIndexedGrammar]
  simpa [i] using hZ

/-- Every indexed nonterminal of R_n is reachable. -/
theorem levelCodeRIndexed_all_reachable
    (n : Nat) :
    ∀ A : LevelCodeRNT n,
      IndexedMixedReachable
        (levelCodeRIndexedGrammar n)
        LevelCodeRNT.start A := by
  intro A
  cases A with
  | start =>
      exact IndexedMixedReachable.start
  | z i =>
      simpa using
        levelCodeRIndexed_z_reachable
          n i.1 (Nat.le_of_lt_succ i.2)
  | a i =>
      simpa using
        levelCodeRIndexed_a_reachable
          n i.1 (Nat.le_of_lt_succ i.2)

/-- Every state of R_n has a terminal yield of length at most n+5. -/
theorem levelCodeRIndexed_thickness_atMost
    (n : Nat) :
    IndexedMixedThicknessAtMost
      (levelCodeRIndexedGrammar n)
      (n + 5) := by
  intro A
  cases A with
  | start =>
      let w :=
        (LevelTree.shortcut n).serialize
      refine ⟨w, ?_, ?_⟩
      · exact
          levelTreeLanguage_to_indexed_start n
            ⟨LevelTree.shortcut n, rfl⟩
      · simpa [w] using
          (levelTree_shortcut_serialize_length n).le
  | z i =>
      let w :=
        List.replicate (i.1 + 1) zero
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeZDerives_to_indexed
            (levelCodeZDerives_replicate i.1)
            (Nat.le_of_lt_succ i.2)
      · simp [w]
        omega
  | a i =>
      let w :=
        (LevelTree.shortcut i.1).serialize
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeADerives_to_indexed
            (levelTree_to_levelCodeADerives
              (LevelTree.shortcut i.1))
            (Nat.le_of_lt_succ i.2)
      · rw [show w.length = i.1 + 5 by
          exact levelTree_shortcut_serialize_length i.1]
        omega

/-- The actual indexed presentation R_n is reduced. -/
theorem levelCodeRIndexed_reduced
    (n : Nat) :
    IndexedMixedReduced
      (levelCodeRIndexedGrammar n)
      LevelCodeRNT.start := by
  refine ⟨levelCodeRIndexed_all_reachable n, ?_⟩
  intro A
  obtain ⟨w, hw, _⟩ :=
    levelCodeRIndexed_thickness_atMost n A
  exact ⟨w, hw⟩

end R

section RMinus

/-- The top A^-_(m+1) is immediately reachable from S^- in R_(m+1)^-. -/
theorem levelCodeRMinusIndexed_topAM_reachable
    (m : Nat) :
    IndexedMixedReachable
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start
      (.am (levelCodeFinTop (m + 1))) := by
  exact
    IndexedMixedReachable.child
      (G := levelCodeRMinusIndexedGrammar m)
      (S := LevelCodeRMinusNT.start)
      (p := LevelCodeRMinusProd.start)
      IndexedMixedReachable.start
      rfl
      (by simp [levelCodeRMinusIndexedGrammar])

/-- Descend one level through an A^- binary rule. -/
theorem levelCodeRMinusIndexed_am_reachable_step
    (m k : Nat)
    (hk : k < m + 1)
    (h :
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start
        (.am (⟨k + 1, by omega⟩ :
          Fin (m + 2)))) :
    IndexedMixedReachable
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start
      (.am (⟨k, by omega⟩ :
        Fin (m + 2))) := by
  let j : Fin (m + 1) := ⟨k, hk⟩
  have hparent :
      levelCodeFinSucc j =
        (⟨k + 1, by omega⟩ :
          Fin (m + 2)) := by
    apply Fin.ext
    rfl
  have hchild :
      levelCodeFinEmbed j =
        (⟨k, by omega⟩ :
          Fin (m + 2)) := by
    apply Fin.ext
    rfl
  have hr :
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start
        (.am (levelCodeFinEmbed j)) := by
    apply IndexedMixedReachable.child
      (G := levelCodeRMinusIndexedGrammar m)
      (S := LevelCodeRMinusNT.start)
      (p := LevelCodeRMinusProd.amNodeLeft j)
      h
    · simp [levelCodeRMinusIndexedGrammar,
        hparent]
    · simp [levelCodeRMinusIndexedGrammar]
  simpa [hchild] using hr

/-- Every A^-_k, k<=m+1, is reachable. -/
theorem levelCodeRMinusIndexed_am_reachable
    (m k : Nat)
    (hk : k ≤ m + 1) :
    IndexedMixedReachable
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start
      (.am (⟨k, by omega⟩ :
        Fin (m + 2))) := by
  apply Nat.decreasingInduction
      (motive := fun i hi =>
        IndexedMixedReachable
          (levelCodeRMinusIndexedGrammar m)
          LevelCodeRMinusNT.start
          (.am (⟨i, by omega⟩ :
            Fin (m + 2))))
  · intro i hi hsucc
    exact
      levelCodeRMinusIndexed_am_reachable_step
        m i hi hsucc
  · simpa [levelCodeFinTop] using
      levelCodeRMinusIndexed_topAM_reachable m
  · exact hk

/-- Every retained ordinary A_k, k<=m, is reachable from A^-_(k+1). -/
theorem levelCodeRMinusIndexed_a_reachable
    (m k : Nat)
    (hk : k ≤ m) :
    IndexedMixedReachable
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start
      (.a (⟨k, by omega⟩ :
        Fin (m + 1))) := by
  let j : Fin (m + 1) := ⟨k, by omega⟩
  have hAM :
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start
        (.am (levelCodeFinSucc j)) := by
    have h :=
      levelCodeRMinusIndexed_am_reachable
        m (k + 1) (by omega)
    simpa [j, levelCodeFinSucc] using h
  have hA :
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start
        (.a j) := by
    apply IndexedMixedReachable.child
      (G := levelCodeRMinusIndexedGrammar m)
      (S := LevelCodeRMinusNT.start)
      (p := LevelCodeRMinusProd.amNodeLeft j)
      hAM
    · rfl
    · simp [levelCodeRMinusIndexedGrammar]
  simpa [j] using hA

/-- Every Z_k, k<=m+1, is reachable from the corresponding A^-_k shortcut. -/
theorem levelCodeRMinusIndexed_z_reachable
    (m k : Nat)
    (hk : k ≤ m + 1) :
    IndexedMixedReachable
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start
      (.z (⟨k, by omega⟩ :
        Fin (m + 2))) := by
  let i : Fin (m + 2) := ⟨k, by omega⟩
  have hAM :
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start
        (.am i) := by
    simpa [i] using
      levelCodeRMinusIndexed_am_reachable
        m k hk
  have hZ :
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start
        (.z i) := by
    apply IndexedMixedReachable.child
      (G := levelCodeRMinusIndexedGrammar m)
      (S := LevelCodeRMinusNT.start)
      (p := LevelCodeRMinusProd.amShortcut i)
      hAM
    · rfl
    · simp [levelCodeRMinusIndexedGrammar]
  simpa [i] using hZ

/-- Every indexed nonterminal of R_(m+1)^- is reachable. -/
theorem levelCodeRMinusIndexed_all_reachable
    (m : Nat) :
    ∀ A : LevelCodeRMinusNT m,
      IndexedMixedReachable
        (levelCodeRMinusIndexedGrammar m)
        LevelCodeRMinusNT.start A := by
  intro A
  cases A with
  | start =>
      exact IndexedMixedReachable.start
  | z i =>
      simpa using
        levelCodeRMinusIndexed_z_reachable
          m i.1 (Nat.le_of_lt_succ i.2)
  | a i =>
      simpa using
        levelCodeRMinusIndexed_a_reachable
          m i.1 (Nat.le_of_lt_succ i.2)
  | am i =>
      simpa using
        levelCodeRMinusIndexed_am_reachable
          m i.1 (Nat.le_of_lt_succ i.2)

/-- Every state of R_(m+1)^- has a terminal yield of length at most m+6. -/
theorem levelCodeRMinusIndexed_thickness_atMost
    (m : Nat) :
    IndexedMixedThicknessAtMost
      (levelCodeRMinusIndexedGrammar m)
      (m + 6) := by
  intro A
  cases A with
  | start =>
      let w :=
        (LevelTree.shortcut (m + 1)).serialize
      refine ⟨w, ?_, ?_⟩
      · exact
          levelTreeShortcutLanguage_to_minusIndexed_start
            m
            ⟨
              ⟨LevelTree.shortcut (m + 1), rfl⟩,
              by simp [LevelTree.serialize,
                levelShortcutBody]⟩
      · rw [show w.length = m + 1 + 5 by
          exact
            levelTree_shortcut_serialize_length
              (m + 1)]
        omega
  | z i =>
      let w :=
        List.replicate (i.1 + 1) zero
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeZDerives_to_minusIndexed
            (levelCodeZDerives_replicate i.1)
            (Nat.le_of_lt_succ i.2)
      · simp [w]
        omega
  | a i =>
      let w :=
        (LevelTree.shortcut i.1).serialize
      refine ⟨w, ?_, ?_⟩
      · exact
          levelCodeADerives_to_minusIndexed
            (levelTree_to_levelCodeADerives
              (LevelTree.shortcut i.1))
            (Nat.le_of_lt_succ i.2)
      · rw [show w.length = i.1 + 5 by
          exact levelTree_shortcut_serialize_length i.1]
        omega
  | am i =>
      let w :=
        (LevelTree.shortcut i.1).serialize
      refine ⟨w, ?_, ?_⟩
      · have dz :=
          levelCodeZDerives_replicate i.1
        have dm :
            LevelCodeAMinusDerives i.1 w := by
          simpa [w, LevelTree.serialize,
            levelShortcutBody, List.append_assoc] using
            (LevelCodeAMinusDerives.shortcut dz)
        exact
          levelCodeAMinusDerives_to_minusIndexed
            dm (Nat.le_of_lt_succ i.2)
      · rw [show w.length = i.1 + 5 by
          exact levelTree_shortcut_serialize_length i.1]
        omega

/-- The actual indexed presentation R_(m+1)^- is reduced. -/
theorem levelCodeRMinusIndexed_reduced
    (m : Nat) :
    IndexedMixedReduced
      (levelCodeRMinusIndexedGrammar m)
      LevelCodeRMinusNT.start := by
  refine ⟨levelCodeRMinusIndexed_all_reachable m, ?_⟩
  intro A
  obtain ⟨w, hw, _⟩ :=
    levelCodeRMinusIndexed_thickness_atMost m A
  exact ⟨w, hw⟩

end RMinus

end TCS1
end LeanCfgProject
