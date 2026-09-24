import LeanCfgProject.TCS1.MarkedBoundaryKernel

/-!
# TCS #1 v68: marked-leaf selection and pruning

This module formalizes the first half of the tree surgery in Lemma 7.1.

A successful non-start SSBNF derivation is represented as an explicit full
binary derivation tree.  A Boolean mark is then attached to every terminal
leaf.  Whenever at least one leaf is marked, the marked tree can be pruned to
the union of root-to-marked-leaf paths:

* if only the left child contains marks, the right child becomes an omitted
  sibling subtree;
* if only the right child contains marks, the left child becomes omitted;
* if both children contain marks, the binary node remains a branching node.

The resulting object is exactly MarkedBoundaryKernel.  The pruning theorem
preserves the original terminal yield, the left-to-right marked word, and the
number of marked leaves.

The next layer instantiates the Boolean marking with the first k and last l
terminal leaves.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundarySelection

variable {N : Type u}
variable {α : Type v}

/-- Explicit successful derivation tree for the terminal/binary SSBNF fragment. -/
inductive BinaryDerivationTree
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    N → Type (max u v)
  | terminal
      {A : N}
      (a : α)
      (hterm : terminalRule A a) :
      BinaryDerivationTree terminalRule binaryRule A
  | binary
      {A B C : N}
      (hbin : binaryRule A B C)
      (left :
        BinaryDerivationTree terminalRule binaryRule B)
      (right :
        BinaryDerivationTree terminalRule binaryRule C) :
      BinaryDerivationTree terminalRule binaryRule A

namespace BinaryDerivationTree

/-- Terminal yield of the derivation tree. -/
def yield
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    BinaryDerivationTree terminalRule binaryRule A →
    Word α
  | _, terminal a _ => [a]
  | _, binary _ left right =>
      yield left ++ yield right

/-- Number of terminal leaves. -/
def leafCount
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    BinaryDerivationTree terminalRule binaryRule A →
    Nat
  | _, terminal _ _ => 1
  | _, binary _ left right =>
      leafCount left + leafCount right

/-- Tree yield is an ordinary untyped derivation. -/
theorem yield_derives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A) :
    UntypedDerives terminalRule binaryRule
      A (yield T) := by
  induction T with
  | terminal a hterm =>
      exact UntypedDerives.terminal hterm
  | binary hbin left right ihL ihR =>
      exact UntypedDerives.binary hbin ihL ihR

/-- The number of leaves equals the terminal-yield length. -/
theorem yield_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A) :
    (yield T).length = leafCount T := by
  induction T with
  | terminal =>
      simp [yield, leafCount]
  | binary hbin left right ihL ihR =>
      simp [yield, leafCount, ihL, ihR]

/-- Every ordinary derivation has an explicit derivation-tree representative. -/
theorem exists_of_derivation
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w) :
    ∃ T : BinaryDerivationTree terminalRule binaryRule A,
      yield T = w := by
  induction d with
  | terminal hterm =>
      exact ⟨BinaryDerivationTree.terminal _ hterm, rfl⟩
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      obtain ⟨TB, hTB⟩ := ihB
      obtain ⟨TC, hTC⟩ := ihC
      refine
        ⟨BinaryDerivationTree.binary hbin TB TC, ?_⟩
      simp [yield, hTB, hTC]

end BinaryDerivationTree

/-- A full derivation tree with a Boolean mark on every terminal leaf. -/
inductive LeafMarkedTree
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop) :
    N → Type (max u v)
  | terminal
      {A : N}
      (a : α)
      (hterm : terminalRule A a)
      (marked : Bool) :
      LeafMarkedTree terminalRule binaryRule A
  | binary
      {A B C : N}
      (hbin : binaryRule A B C)
      (left :
        LeafMarkedTree terminalRule binaryRule B)
      (right :
        LeafMarkedTree terminalRule binaryRule C) :
      LeafMarkedTree terminalRule binaryRule A

namespace LeafMarkedTree

/-- Full terminal yield, ignoring marks. -/
def yield
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    LeafMarkedTree terminalRule binaryRule A →
    Word α
  | _, terminal a _ _ => [a]
  | _, binary _ left right =>
      yield left ++ yield right

/-- Marked terminal labels in left-to-right order. -/
def markedWord
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    LeafMarkedTree terminalRule binaryRule A →
    Word α
  | _, terminal a _ true => [a]
  | _, terminal _ _ false => []
  | _, binary _ left right =>
      markedWord left ++ markedWord right

/-- Number of marked terminal leaves. -/
def markedCount
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    LeafMarkedTree terminalRule binaryRule A →
    Nat
  | _, terminal _ _ true => 1
  | _, terminal _ _ false => 0
  | _, binary _ left right =>
      markedCount left + markedCount right

/-- Forget marks to obtain an explicit derivation tree. -/
def forget
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    LeafMarkedTree terminalRule binaryRule A →
    BinaryDerivationTree terminalRule binaryRule A
  | _, terminal a hterm _ =>
      BinaryDerivationTree.terminal a hterm
  | _, binary hbin left right =>
      BinaryDerivationTree.binary hbin
        (forget left) (forget right)

/-- Forgetting marks preserves the terminal yield. -/
@[simp] theorem forget_yield
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A) :
    BinaryDerivationTree.yield (forget T) = yield T := by
  induction T with
  | terminal a hterm marked =>
      rfl
  | binary hbin left right ihL ihR =>
      simp [forget, yield,
        BinaryDerivationTree.yield, ihL, ihR]

/-- The marked word has exactly one symbol per marked leaf. -/
theorem markedWord_length
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A) :
    (markedWord T).length = markedCount T := by
  induction T with
  | terminal a hterm marked =>
      cases marked <;>
        simp [markedWord, markedCount]
  | binary hbin left right ihL ihR =>
      simp [markedWord, markedCount, ihL, ihR]

/-- Full yield of a marked tree is still a genuine derivation. -/
theorem yield_derives
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A) :
    UntypedDerives terminalRule binaryRule
      A (yield T) := by
  simpa [forget_yield terminalRule binaryRule T] using
    BinaryDerivationTree.yield_derives
      terminalRule binaryRule (forget T)

/-- Boolean mark sequence of the terminal leaves, left to right. -/
def leafMarks
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    LeafMarkedTree terminalRule binaryRule A →
    List Bool
  | _, terminal _ _ marked => [marked]
  | _, binary _ left right =>
      leafMarks left ++ leafMarks right

/-- Number of true entries in a Boolean list. -/
def trueCount : List Bool → Nat
  | [] => 0
  | true :: bs => 1 + trueCount bs
  | false :: bs => trueCount bs

@[simp] theorem trueCount_append
    (xs ys : List Bool) :
    trueCount (xs ++ ys) =
      trueCount xs + trueCount ys := by
  induction xs with
  | nil =>
      simp [trueCount]
  | cons b xs ih =>
      cases b <;>
        simp [trueCount, ih, Nat.add_assoc]

/--
For every unmarked leaf, record the number of marked leaves preceding it.
-/
def unmarkedRanksAux
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop}
    (offset : Nat) :
    {A : N} →
    LeafMarkedTree terminalRule binaryRule A →
    List Nat
  | _, terminal _ _ true => []
  | _, terminal _ _ false => [offset]
  | _, binary _ left right =>
      unmarkedRanksAux offset left ++
        unmarkedRanksAux
          (offset + markedCount left) right

/-- Same rank scan performed directly on a Boolean mark list. -/
def falseRanksAux : Nat → List Bool → List Nat
  | _, [] => []
  | offset, true :: bs =>
      falseRanksAux (offset + 1) bs
  | offset, false :: bs =>
      offset :: falseRanksAux offset bs

/-- Rank scanning distributes over concatenation with the expected offset. -/
theorem falseRanksAux_append
    (offset : Nat)
    (xs ys : List Bool) :
    falseRanksAux offset (xs ++ ys) =
      falseRanksAux offset xs ++
        falseRanksAux (offset + trueCount xs) ys := by
  induction xs generalizing offset with
  | nil =>
      simp [falseRanksAux, trueCount]
  | cons b xs ih =>
      cases b <;>
        simp [falseRanksAux, trueCount, ih,
          Nat.add_assoc]

/-- Tree marked count equals the true-count of its leaf mark sequence. -/
theorem markedCount_eq_trueCount_leafMarks
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A) :
    markedCount T = trueCount (leafMarks T) := by
  induction T with
  | terminal a hterm marked =>
      cases marked <;>
        simp [markedCount, leafMarks, trueCount]
  | binary hbin left right ihL ihR =>
      simp [markedCount, leafMarks,
        trueCount_append, ihL, ihR]

/-- Unmarked-leaf ranks depend only on the left-to-right Boolean mark list. -/
theorem unmarkedRanksAux_eq_falseRanksAux
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset : Nat)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A) :
    unmarkedRanksAux offset T =
      falseRanksAux offset (leafMarks T) := by
  induction T generalizing offset with
  | terminal a hterm marked =>
      cases marked <;>
        simp [unmarkedRanksAux, falseRanksAux, leafMarks]
  | binary hbin left right ihL ihR =>
      simp only [unmarkedRanksAux, leafMarks,
        falseRanksAux_append]
      rw [ihL offset]
      rw [ihR (offset + markedCount left)]
      rw [markedCount_eq_trueCount_leafMarks
        terminalRule binaryRule left]

/--
A completely unmarked nonempty derivation tree contributes an unmarked leaf at
the current marked-leaf rank.
-/
theorem offset_mem_unmarkedRanksAux_of_markedCount_zero
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset : Nat)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A)
    (hzero : markedCount T = 0) :
    offset ∈ unmarkedRanksAux offset T := by
  induction T generalizing offset with
  | terminal a hterm marked =>
      cases marked with
      | false =>
          simp [unmarkedRanksAux]
      | true =>
          simp [markedCount] at hzero
  | binary hbin left right ihL ihR =>
      have hLzero : markedCount left = 0 := by
        simp only [markedCount] at hzero
        omega
      have hmem :=
        ihL offset hLzero
      exact List.mem_append_left _ hmem

/--
Rank-aware pruning.

Every omission rank in the pruned kernel is the rank of some unmarked terminal
leaf of the original marked tree.  Therefore any common-gap property of all
unmarked leaves is inherited by the omitted sibling subtrees.
-/
theorem exists_pruned_kernel_with_rank_subset
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A)
    (hpos : 0 < markedCount T)
    (offset : Nat) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.originalYield K = yield T
      ∧
      MarkedBoundaryKernel.markedWord K = markedWord T
      ∧
      MarkedBoundaryKernel.markedLeafCount K = markedCount T
      ∧
      (∀ j ∈
          MarkedBoundaryKernel.omissionRanksAux offset K,
        j ∈ unmarkedRanksAux offset T) := by
  induction T generalizing offset with
  | terminal a hterm marked =>
      cases marked with
      | false =>
          simp [markedCount] at hpos
      | true =>
          exact
            ⟨MarkedBoundaryKernel.marked a hterm,
              rfl, rfl, rfl,
              by
                intro j hj
                simp [MarkedBoundaryKernel.omissionRanksAux] at hj⟩

  | @binary A B C hbin left right ihL ihR =>
      by_cases hL : 0 < markedCount left
      · by_cases hR : 0 < markedCount right
        · obtain ⟨KL, hYieldL, hWordL, hCountL, hRankL⟩ :=
            ihL hL offset
          obtain ⟨KR, hYieldR, hWordR, hCountR, hRankR⟩ :=
            ihR hR (offset + markedCount left)
          refine
            ⟨MarkedBoundaryKernel.branch hbin KL KR,
              ?_, ?_, ?_, ?_⟩
          · simp [MarkedBoundaryKernel.originalYield,
              yield, hYieldL, hYieldR]
          · simp [MarkedBoundaryKernel.markedWord,
              markedWord, hWordL, hWordR]
          · simp [MarkedBoundaryKernel.markedLeafCount,
              markedCount, hCountL, hCountR]
          · intro j hj
            simp only [MarkedBoundaryKernel.omissionRanksAux,
              List.mem_append] at hj
            simp only [unmarkedRanksAux, List.mem_append]
            rcases hj with hj | hj
            · exact Or.inl (hRankL j hj)
            · rw [hCountL] at hj
              exact Or.inr (hRankR j hj)

        · have hRzero : markedCount right = 0 := by
            omega
          obtain ⟨KL, hYieldL, hWordL, hCountL, hRankL⟩ :=
            ihL hL offset
          refine
            ⟨MarkedBoundaryKernel.unaryLeft
                hbin KL (yield right)
                (yield_derives terminalRule binaryRule right),
              ?_, ?_, ?_, ?_⟩
          · simp [MarkedBoundaryKernel.originalYield,
              yield, hYieldL]
          · have hWordR : markedWord right = [] := by
              have hlen :
                  (markedWord right).length = 0 := by
                rw [markedWord_length
                  terminalRule binaryRule right, hRzero]
              cases hword : markedWord right with
              | nil =>
                  rfl
              | cons a xs =>
                  rw [hword] at hlen
                  simp at hlen
            simp [MarkedBoundaryKernel.markedWord,
              markedWord, hWordL, hWordR]
          · simp [MarkedBoundaryKernel.markedLeafCount,
              markedCount, hCountL, hRzero]
          · intro j hj
            simp only [MarkedBoundaryKernel.omissionRanksAux,
              List.mem_append, List.mem_singleton] at hj
            simp only [unmarkedRanksAux, List.mem_append]
            rcases hj with hj | hj
            · exact Or.inl (hRankL j hj)
            · subst j
              right
              rw [hCountL]
              exact
                offset_mem_unmarkedRanksAux_of_markedCount_zero
                  terminalRule binaryRule
                  (offset + markedCount left)
                  right hRzero

      · have hLzero : markedCount left = 0 := by
          omega
        have hR : 0 < markedCount right := by
          simp only [markedCount] at hpos
          omega
        obtain ⟨KR, hYieldR, hWordR, hCountR, hRankR⟩ :=
          ihR hR (offset + markedCount left)
        refine
          ⟨MarkedBoundaryKernel.unaryRight
              hbin (yield left)
              (yield_derives terminalRule binaryRule left)
              KR,
            ?_, ?_, ?_, ?_⟩
        · simp [MarkedBoundaryKernel.originalYield,
            yield, hYieldR]
        · have hWordL : markedWord left = [] := by
            have hlen :
                (markedWord left).length = 0 := by
              rw [markedWord_length
                terminalRule binaryRule left, hLzero]
            cases hword : markedWord left with
              | nil =>
                  rfl
              | cons a xs =>
                  rw [hword] at hlen
                  simp at hlen
          simp [MarkedBoundaryKernel.markedWord,
            markedWord, hWordL, hWordR]
        · simp [MarkedBoundaryKernel.markedLeafCount,
            markedCount, hCountR, hLzero]
        · intro j hj
          simp only [MarkedBoundaryKernel.omissionRanksAux,
            List.mem_cons] at hj
          simp only [unmarkedRanksAux, List.mem_append]
          rcases hj with hj0 | hj
          · left
            rw [hj0]
            exact
              offset_mem_unmarkedRanksAux_of_markedCount_zero
                terminalRule binaryRule
                offset left hLzero
          · right
            have hj' :
                j ∈ MarkedBoundaryKernel.omissionRanksAux
                  (offset + markedCount left) KR := by
              simpa [hLzero] using hj
            exact hRankR j hj'

/--
Prune an arbitrary nonempty leaf marking to the union of root-to-marked-leaf
paths.

The returned marked-boundary kernel preserves:
* the complete original yield;
* the marked terminal word; and
* the number of marked leaves.
-/
theorem exists_pruned_kernel
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : LeafMarkedTree terminalRule binaryRule A)
    (hpos : 0 < markedCount T) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.originalYield K = yield T
      ∧
      MarkedBoundaryKernel.markedWord K = markedWord T
      ∧
      MarkedBoundaryKernel.markedLeafCount K = markedCount T := by
  induction T with
  | terminal a hterm marked =>
      cases marked with
      | false =>
          simp [markedCount] at hpos
      | true =>
          exact
            ⟨MarkedBoundaryKernel.marked a hterm,
              rfl, rfl, rfl⟩

  | @binary A B C hbin left right ihL ihR =>
      by_cases hL : 0 < markedCount left
      · by_cases hR : 0 < markedCount right
        · obtain ⟨KL, hYieldL, hWordL, hCountL⟩ :=
            ihL hL
          obtain ⟨KR, hYieldR, hWordR, hCountR⟩ :=
            ihR hR
          refine
            ⟨MarkedBoundaryKernel.branch hbin KL KR,
              ?_, ?_, ?_⟩
          · simp [MarkedBoundaryKernel.originalYield,
              yield, hYieldL, hYieldR]
          · simp [MarkedBoundaryKernel.markedWord,
              markedWord, hWordL, hWordR]
          · simp [MarkedBoundaryKernel.markedLeafCount,
              markedCount, hCountL, hCountR]

        · have hRzero : markedCount right = 0 := by
            omega
          obtain ⟨KL, hYieldL, hWordL, hCountL⟩ :=
            ihL hL
          refine
            ⟨MarkedBoundaryKernel.unaryLeft
                hbin KL (yield right)
                (yield_derives terminalRule binaryRule right),
              ?_, ?_, ?_⟩
          · simp [MarkedBoundaryKernel.originalYield,
              yield, hYieldL]
          · have hWordR : markedWord right = [] := by
              have hlen :
                  (markedWord right).length = 0 := by
                rw [markedWord_length
                  terminalRule binaryRule right, hRzero]
              cases hword : markedWord right with
              | nil =>
                  rfl
              | cons a xs =>
                  rw [hword] at hlen
                  simp at hlen
            simp [MarkedBoundaryKernel.markedWord,
              markedWord, hWordL, hWordR]
          · simp [MarkedBoundaryKernel.markedLeafCount,
              markedCount, hCountL, hRzero]

      · have hLzero : markedCount left = 0 := by
          omega
        have hR : 0 < markedCount right := by
          simp only [markedCount] at hpos
          omega
        obtain ⟨KR, hYieldR, hWordR, hCountR⟩ :=
          ihR hR
        refine
          ⟨MarkedBoundaryKernel.unaryRight
              hbin (yield left)
              (yield_derives terminalRule binaryRule left)
              KR,
            ?_, ?_, ?_⟩
        · simp [MarkedBoundaryKernel.originalYield,
            yield, hYieldR]
        · have hWordL : markedWord left = [] := by
            have hlen :
                (markedWord left).length = 0 := by
              rw [markedWord_length
                terminalRule binaryRule left, hLzero]
            cases hword : markedWord left with
              | nil =>
                  rfl
              | cons a xs =>
                  rw [hword] at hlen
                  simp at hlen
          simp [MarkedBoundaryKernel.markedWord,
            markedWord, hWordL, hWordR]
        · simp [MarkedBoundaryKernel.markedLeafCount,
            markedCount, hCountR, hLzero]

end LeafMarkedTree

end MarkedBoundarySelection

end TCS1
end LeanCfgProject
