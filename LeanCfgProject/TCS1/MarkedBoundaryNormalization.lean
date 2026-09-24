import LeanCfgProject.TCS1.MarkedBoundaryKernel
import LeanCfgProject.TCS1.FixedWindowContextSemantic

/-!
# TCS #1 v68: cycle shortening for marked-boundary kernels

This module closes the cycle-shortening part of Lemma 7.1.

A marked-boundary kernel is decomposed into:

* one maximal unary head chain, represented as a ReachingSpine; and
* a head base, which is either a marked terminal leaf or a genuine branching
  node with two marked child kernels.

The reaching-spine normalization from FixedWindowContextSemantic removes
repeated nonterminal labels from the head chain.  At a branching base, the two
child kernels are normalized recursively.  This gives a normalized marked
kernel in which the total number of omitted sibling subtrees is bounded by

  (2r - 1) * |N|

for r marked leaves.

This is exactly the combinatorial statement used in lines 802--818 of the v68
proof of the bounded fixed-window typed-yield lemma.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryNormalization

variable {N : Type u}
variable {α : Type v}

/-- The endpoint of one maximal unary head chain. -/
inductive MarkedBoundaryBase
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    N → Type (max u v)
  | marked
      {A : N}
      (a : α)
      (hterm : terminalRule A a) :
      MarkedBoundaryBase terminalRule binaryRule A
  | branch
      {A B C : N}
      (hbin : binaryRule A B C)
      (left :
        MarkedBoundaryKernel terminalRule binaryRule B)
      (right :
        MarkedBoundaryKernel terminalRule binaryRule C) :
      MarkedBoundaryBase terminalRule binaryRule A

namespace MarkedBoundaryBase

/-- Forget the head/base distinction. -/
def toKernel
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryBase terminalRule binaryRule A →
    MarkedBoundaryKernel terminalRule binaryRule A
  | _, marked a hterm =>
      MarkedBoundaryKernel.marked a hterm
  | _, branch hbin left right =>
      MarkedBoundaryKernel.branch hbin left right

/-- Number of marked leaves below the head base. -/
def markedLeafCount
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryBase terminalRule binaryRule A →
    Nat
  | _, marked _ _ => 1
  | _, branch _ left right =>
      MarkedBoundaryKernel.markedLeafCount left +
        MarkedBoundaryKernel.markedLeafCount right

/-- Omitted siblings strictly below the current head segment. -/
def omittedBelow
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryBase terminalRule binaryRule A →
    Nat
  | _, marked _ _ => 0
  | _, branch _ left right =>
      MarkedBoundaryKernel.omittedCount left +
        MarkedBoundaryKernel.omittedCount right

/-- Marked terminal labels below the head base. -/
def markedWord
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    MarkedBoundaryBase terminalRule binaryRule A →
    Word α
  | _, marked a _ => [a]
  | _, branch _ left right =>
      MarkedBoundaryKernel.markedWord left ++
        MarkedBoundaryKernel.markedWord right

@[simp] theorem toKernel_markedLeafCount
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (base :
      MarkedBoundaryBase terminalRule binaryRule A) :
    MarkedBoundaryKernel.markedLeafCount
        (toKernel base) =
      markedLeafCount base := by
  cases base <;>
    simp [toKernel, markedLeafCount,
      MarkedBoundaryKernel.markedLeafCount]

@[simp] theorem toKernel_omittedCount
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (base :
      MarkedBoundaryBase terminalRule binaryRule A) :
    MarkedBoundaryKernel.omittedCount
        (toKernel base) =
      omittedBelow base := by
  cases base <;>
    simp [toKernel, omittedBelow,
      MarkedBoundaryKernel.omittedCount]

@[simp] theorem toKernel_markedWord
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (base :
      MarkedBoundaryBase terminalRule binaryRule A) :
    MarkedBoundaryKernel.markedWord
        (toKernel base) =
      markedWord base := by
  cases base <;>
    simp [toKernel, markedWord,
      MarkedBoundaryKernel.markedWord]

end MarkedBoundaryBase

/--
Attach a unary reaching spine above a head base.

The theorem also records the exact omitted-sibling count contributed by the
head: one omitted sibling per binary spine step.
-/
theorem exists_attachHead
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings)
    (base :
      MarkedBoundaryBase terminalRule binaryRule X) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K =
        MarkedBoundaryBase.markedLeafCount base
      ∧
      MarkedBoundaryKernel.omittedCount K =
        siblings.length +
          MarkedBoundaryBase.omittedBelow base
      ∧
      MarkedBoundaryKernel.markedWord K =
        MarkedBoundaryBase.markedWord base := by
  induction spine with
  | hole =>
      exact
        ⟨MarkedBoundaryBase.toKernel base,
          MarkedBoundaryBase.toKernel_markedLeafCount
            terminalRule binaryRule base,
          by
            simpa using
              MarkedBoundaryBase.toKernel_omittedCount
                terminalRule binaryRule base,
          MarkedBoundaryBase.toKernel_markedWord
            terminalRule binaryRule base⟩

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling ih =>
      obtain ⟨K, hmarks, homit, hword⟩ := ih base
      refine
        ⟨MarkedBoundaryKernel.unaryLeft
            hbin K z sibling,
          ?_, ?_, ?_⟩
      · simpa [MarkedBoundaryKernel.markedLeafCount]
          using hmarks
      · simp only [MarkedBoundaryKernel.omittedCount,
          List.length_cons]
        rw [homit]
        omega
      · simpa [MarkedBoundaryKernel.markedWord]
          using hword

  | @binaryRight A B C X left right y path siblings
      hbin sibling child ih =>
      obtain ⟨K, hmarks, homit, hword⟩ := ih base
      refine
        ⟨MarkedBoundaryKernel.unaryRight
            hbin y sibling K,
          ?_, ?_, ?_⟩
      · simpa [MarkedBoundaryKernel.markedLeafCount]
          using hmarks
      · simp only [MarkedBoundaryKernel.omittedCount,
          List.length_cons]
        rw [homit]
        omega
      · simpa [MarkedBoundaryKernel.markedWord]
          using hword

/--
One normalized head/base decomposition.

The head path is repetition-free.  The base-tail budget counts all omitted
siblings below the head segment and is already normalized recursively.
-/
structure NormalizedHeadData
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) where
  target : N
  left : Word α
  right : Word α
  path : List N
  siblings : List Nat
  spine :
    ReachingSpine terminalRule binaryRule
      A target left right path siblings
  base :
    MarkedBoundaryBase terminalRule binaryRule target
  path_nodup : path.Nodup
  marks_eq :
    MarkedBoundaryBase.markedLeafCount base =
      MarkedBoundaryKernel.markedLeafCount K
  word_eq :
    MarkedBoundaryBase.markedWord base =
      MarkedBoundaryKernel.markedWord K
  tail_bound :
    MarkedBoundaryBase.omittedBelow base ≤
      (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
        Fintype.card N

/--
A normalized head contains at most |N| omitted siblings.
-/
theorem normalizedHead_siblings_le_card
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {K : MarkedBoundaryKernel terminalRule binaryRule A}
    (D :
      NormalizedHeadData terminalRule binaryRule K) :
    D.siblings.length ≤ Fintype.card N := by
  have hpath :
      D.path.length ≤ Fintype.card N :=
    dependency_path_vertices_le
      D.path D.path_nodup
  have hstep :
      D.siblings.length + 1 = D.path.length :=
    reachingSpine_siblings_length_add_one_eq_path
      terminalRule binaryRule D.spine
  omega

/--
Attaching normalized head data gives the exact manuscript omitted-sibling
bound (2r-1)|N|.
-/
theorem normalizedHead_attach_bound
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {K : MarkedBoundaryKernel terminalRule binaryRule A}
    (D :
      NormalizedHeadData terminalRule binaryRule K) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K' =
        MarkedBoundaryKernel.markedLeafCount K
      ∧
      MarkedBoundaryKernel.markedWord K' =
        MarkedBoundaryKernel.markedWord K
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N := by
  obtain ⟨K', hmarks, homit, hword⟩ :=
    exists_attachHead
      terminalRule binaryRule D.spine D.base
  have hhead :
      D.siblings.length ≤ Fintype.card N :=
    normalizedHead_siblings_le_card
      terminalRule binaryRule D
  have hsum :
      D.siblings.length +
          MarkedBoundaryBase.omittedBelow D.base
        ≤
      Fintype.card N +
        (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
          Fintype.card N :=
    Nat.add_le_add hhead D.tail_bound
  have hpos :
      0 < MarkedBoundaryKernel.markedLeafCount K :=
    MarkedBoundaryKernel.markedLeafCount_pos
      terminalRule binaryRule K
  have hcoeff :
      1 + (2 * MarkedBoundaryKernel.markedLeafCount K - 2) =
        2 * MarkedBoundaryKernel.markedLeafCount K - 1 := by
    omega
  have hfactor :
      Fintype.card N +
          (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
            Fintype.card N
        =
      (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
        Fintype.card N := by
    calc
      Fintype.card N +
          (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
            Fintype.card N
          =
        (1 +
          (2 * MarkedBoundaryKernel.markedLeafCount K - 2)) *
            Fintype.card N := by
              simp [Nat.add_mul]
      _ =
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N := by
            rw [hcoeff]
  refine
    ⟨K', ?_, ?_, ?_⟩
  · rw [hmarks, D.marks_eq]
  · rw [hword, D.word_eq]
  · rw [homit]
    exact le_trans hsum (le_of_eq hfactor)

/--
Existence of a normalized head/base decomposition for every marked kernel.

Unary cases extend the already-normalized child head by one step and then use
reaching-spine cycle elimination.  Branching cases recursively normalize both
children, attach them, and make the current branch the new base.
-/
theorem exists_normalizedHeadData
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    Nonempty
      (NormalizedHeadData terminalRule binaryRule K) := by
  induction K with
  | @marked A a hterm =>
      refine ⟨{
        target := A
        left := []
        right := []
        path := [A]
        siblings := []
        spine := ReachingSpine.hole
        base := MarkedBoundaryBase.marked a hterm
        path_nodup := by simp
        marks_eq := by
          simp [MarkedBoundaryBase.markedLeafCount,
            MarkedBoundaryKernel.markedLeafCount]
        word_eq := by
          simp [MarkedBoundaryBase.markedWord,
            MarkedBoundaryKernel.markedWord]
        tail_bound := by
          simp [MarkedBoundaryBase.omittedBelow,
            MarkedBoundaryKernel.markedLeafCount]
      }⟩

  | @unaryLeft A B C hbin child siblingWord sibling ih =>
      obtain ⟨D⟩ := ih
      let preSpine :
          ReachingSpine terminalRule binaryRule
            A D.target
            D.left (D.right ++ siblingWord)
            (A :: D.path)
            (siblingWord.length :: D.siblings) :=
        ReachingSpine.binaryLeft hbin D.spine sibling
      obtain ⟨left', right', path', siblings',
          spine', hnodup'⟩ :=
        normalize_reachingSpine_to_nodup_unbounded
          terminalRule binaryRule preSpine
      refine ⟨{
        target := D.target
        left := left'
        right := right'
        path := path'
        siblings := siblings'
        spine := spine'
        base := D.base
        path_nodup := hnodup'
        marks_eq := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.marks_eq
        word_eq := by
          simpa [MarkedBoundaryKernel.markedWord]
            using D.word_eq
        tail_bound := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.tail_bound
      }⟩

  | @unaryRight A B C hbin siblingWord sibling child ih =>
      obtain ⟨D⟩ := ih
      let preSpine :
          ReachingSpine terminalRule binaryRule
            A D.target
            (siblingWord ++ D.left) D.right
            (A :: D.path)
            (siblingWord.length :: D.siblings) :=
        ReachingSpine.binaryRight hbin sibling D.spine
      obtain ⟨left', right', path', siblings',
          spine', hnodup'⟩ :=
        normalize_reachingSpine_to_nodup_unbounded
          terminalRule binaryRule preSpine
      refine ⟨{
        target := D.target
        left := left'
        right := right'
        path := path'
        siblings := siblings'
        spine := spine'
        base := D.base
        path_nodup := hnodup'
        marks_eq := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.marks_eq
        word_eq := by
          simpa [MarkedBoundaryKernel.markedWord]
            using D.word_eq
        tail_bound := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.tail_bound
      }⟩

  | @branch A B C hbin left right ihL ihR =>
      obtain ⟨DL⟩ := ihL
      obtain ⟨DR⟩ := ihR
      obtain ⟨left', hleftMarks, hleftWord, hleftBound⟩ :=
        normalizedHead_attach_bound
          terminalRule binaryRule DL
      obtain ⟨right', hrightMarks, hrightWord, hrightBound⟩ :=
        normalizedHead_attach_bound
          terminalRule binaryRule DR
      let base :
          MarkedBoundaryBase terminalRule binaryRule A :=
        MarkedBoundaryBase.branch hbin left' right'
      have hleftPos :
          0 < MarkedBoundaryKernel.markedLeafCount left :=
        MarkedBoundaryKernel.markedLeafCount_pos
          terminalRule binaryRule left
      have hrightPos :
          0 < MarkedBoundaryKernel.markedLeafCount right :=
        MarkedBoundaryKernel.markedLeafCount_pos
          terminalRule binaryRule right
      have htail :
          MarkedBoundaryBase.omittedBelow base ≤
            (2 * MarkedBoundaryKernel.markedLeafCount
                  (MarkedBoundaryKernel.branch hbin left right) - 2) *
              Fintype.card N := by
        dsimp [base, MarkedBoundaryBase.omittedBelow]
        have hsum :=
          Nat.add_le_add hleftBound hrightBound
        have hcoeff :
            (2 * MarkedBoundaryKernel.markedLeafCount left - 1) +
              (2 * MarkedBoundaryKernel.markedLeafCount right - 1)
              =
            2 *
                (MarkedBoundaryKernel.markedLeafCount left +
                  MarkedBoundaryKernel.markedLeafCount right) -
              2 := by
          omega
        have hfactor :
            (2 * MarkedBoundaryKernel.markedLeafCount left - 1) *
                Fintype.card N +
              (2 * MarkedBoundaryKernel.markedLeafCount right - 1) *
                Fintype.card N
              =
            (2 *
                (MarkedBoundaryKernel.markedLeafCount left +
                  MarkedBoundaryKernel.markedLeafCount right) -
              2) * Fintype.card N := by
          rw [← Nat.add_mul, hcoeff]
        rw [hfactor] at hsum
        simpa [MarkedBoundaryKernel.markedLeafCount] using hsum
      refine ⟨{
        target := A
        left := []
        right := []
        path := [A]
        siblings := []
        spine := ReachingSpine.hole
        base := base
        path_nodup := by simp
        marks_eq := by
          dsimp [base, MarkedBoundaryBase.markedLeafCount]
          rw [hleftMarks, hrightMarks]
          simp [MarkedBoundaryKernel.markedLeafCount]
        word_eq := by
          dsimp [base, MarkedBoundaryBase.markedWord]
          rw [hleftWord, hrightWord]
          simp [MarkedBoundaryKernel.markedWord]
        tail_bound := htail
      }⟩

/--
Cycle-shortened marked kernel.

The new kernel has the same marked boundary terminals as the original, and at
most (2r-1)|N| omitted sibling subtrees.
-/
theorem exists_cycle_shortened_kernel
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K' =
        MarkedBoundaryKernel.markedLeafCount K
      ∧
      MarkedBoundaryKernel.markedWord K' =
        MarkedBoundaryKernel.markedWord K
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N := by
  obtain ⟨D⟩ :=
    exists_normalizedHeadData
      terminalRule binaryRule K
  exact
    normalizedHead_attach_bound
      terminalRule binaryRule D

end MarkedBoundaryNormalization

end TCS1
end LeanCfgProject
