import LeanCfgProject.TCS1.MarkedBoundarySelection

/-!
# TCS #1 v68: first-k / last-l boundary marking

This module instantiates the generic marked-leaf pruning construction with the
actual marking used in Lemma 7.1: mark the first k terminal leaves and the last
l terminal leaves of a successful derivation.

A Boolean mask of length n is

  true^k ++ false^(n-k-l) ++ true^l

when k+l <= n.  Applying the mask to the left-to-right terminal leaves and
then pruning gives a MarkedBoundaryKernel with:

* exactly k+l marked leaves;
* marked word equal to the length-k prefix followed by the length-l suffix;
* original full yield unchanged.

This closes the boundary-selection part of the long-word tree surgery.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FixedWindowBoundaryMarking

variable {N : Type u}
variable {α : Type v}

/-- Select letters whose aligned Boolean mask entry is true. -/
def selectByMask : List Bool → Word α → Word α
  | true :: bs, a :: w =>
      a :: selectByMask bs w
  | false :: bs, _ :: w =>
      selectByMask bs w
  | _, _ => []

/--
Aligned concatenations may be selected independently on the two sides.
-/
theorem selectByMask_append_aligned
    (m₁ m₂ : List Bool)
    (u v : Word α)
    (hlen : m₁.length = u.length) :
    selectByMask (m₁ ++ m₂) (u ++ v) =
      selectByMask m₁ u ++ selectByMask m₂ v := by
  induction u generalizing m₁ with
  | nil =>
      cases m₁ with
      | nil =>
          simp [selectByMask]
      | cons b bs =>
          simp at hlen
  | cons a u ih =>
      cases m₁ with
      | nil =>
          simp at hlen
      | cons b bs =>
          have htail : bs.length = u.length := by
            simpa using Nat.succ.inj hlen
          cases b <;>
            simp [selectByMask, ih bs htail]

@[simp] theorem selectByMask_replicate_true
    (w : Word α) :
    selectByMask (List.replicate w.length true) w = w := by
  induction w with
  | nil =>
      rfl
  | cons a w ih =>
      change
        selectByMask (true :: List.replicate w.length true)
          (a :: w) = a :: w
      simp only [selectByMask]
      rw [ih]

@[simp] theorem selectByMask_replicate_false
    (w : Word α) :
    selectByMask (List.replicate w.length false) w = [] := by
  induction w with
  | nil =>
      rfl
  | cons a w ih =>
      change
        selectByMask (false :: List.replicate w.length false)
          (a :: w) = []
      simp only [selectByMask]
      exact ih

/--
Mark the leaves of an explicit derivation tree by a Boolean list.  Extra mask
bits are ignored and a missing bit defaults to false; the main theorem below
uses an exactly aligned mask.
-/
def markWithMask
    {terminalRule : N → α → Prop}
    {binaryRule : N → N → N → Prop} :
    {A : N} →
    BinaryDerivationTree terminalRule binaryRule A →
    List Bool →
    LeafMarkedTree terminalRule binaryRule A
  | _, BinaryDerivationTree.terminal a hterm, mask =>
      LeafMarkedTree.terminal a hterm (mask.headD false)
  | _, BinaryDerivationTree.binary hbin left right, mask =>
      LeafMarkedTree.binary hbin
        (markWithMask left
          (mask.take (BinaryDerivationTree.leafCount left)))
        (markWithMask right
          (mask.drop (BinaryDerivationTree.leafCount left)))

/-- Marking does not change the underlying terminal yield. -/
theorem markWithMask_yield
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A)
    (mask : List Bool) :
    LeafMarkedTree.yield (markWithMask T mask) =
      BinaryDerivationTree.yield T := by
  induction T generalizing mask with
  | terminal a hterm =>
      simp [markWithMask, LeafMarkedTree.yield,
        BinaryDerivationTree.yield]
  | binary hbin left right ihL ihR =>
      simp [markWithMask, LeafMarkedTree.yield,
        BinaryDerivationTree.yield, ihL, ihR]

/-- For an exactly aligned mask, the leaf Boolean sequence is the mask itself. -/
theorem leafMarks_markWithMask
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A)
    (mask : List Bool)
    (hlen :
      mask.length =
        BinaryDerivationTree.leafCount T) :
    LeafMarkedTree.leafMarks (markWithMask T mask) = mask := by
  induction T generalizing mask with
  | terminal a hterm =>
      cases mask with
      | nil =>
          simp [BinaryDerivationTree.leafCount] at hlen
      | cons b bs =>
          cases bs with
          | nil =>
              simp [markWithMask, LeafMarkedTree.leafMarks]
          | cons c cs =>
              simp [BinaryDerivationTree.leafCount] at hlen
  | binary hbin left right ihL ihR =>
      have hleft :
          (mask.take
              (BinaryDerivationTree.leafCount left)).length =
            BinaryDerivationTree.leafCount left := by
        have hle :
            BinaryDerivationTree.leafCount left ≤ mask.length := by
          simp only [BinaryDerivationTree.leafCount] at hlen
          omega
        simp [List.length_take, hle]
      have hright :
          (mask.drop
              (BinaryDerivationTree.leafCount left)).length =
            BinaryDerivationTree.leafCount right := by
        simp only [BinaryDerivationTree.leafCount] at hlen
        simp [List.length_drop, hlen]
      simp only [markWithMask, LeafMarkedTree.leafMarks]
      rw [ihL _ hleft, ihR _ hright]
      exact List.take_append_drop
        (BinaryDerivationTree.leafCount left) mask

/--
For an exactly aligned mask, the marked terminal word is exactly the
mask-selected terminal yield.
-/
theorem markWithMask_markedWord
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A)
    (mask : List Bool)
    (hlen :
      mask.length =
        BinaryDerivationTree.leafCount T) :
    LeafMarkedTree.markedWord (markWithMask T mask) =
      selectByMask mask (BinaryDerivationTree.yield T) := by
  induction T generalizing mask with
  | terminal a hterm =>
      cases mask with
      | nil =>
          simp [BinaryDerivationTree.leafCount] at hlen
      | cons b bs =>
          cases bs with
          | nil =>
              cases b <;>
                simp [markWithMask, LeafMarkedTree.markedWord,
                  BinaryDerivationTree.yield, selectByMask]
          | cons c cs =>
              simp [BinaryDerivationTree.leafCount] at hlen
  | binary hbin left right ihL ihR =>
      have hleft :
          (mask.take
              (BinaryDerivationTree.leafCount left)).length =
            BinaryDerivationTree.leafCount left := by
        have hle :
            BinaryDerivationTree.leafCount left ≤ mask.length := by
          simp only [BinaryDerivationTree.leafCount] at hlen
          omega
        simp [List.length_take, hle]
      have hright :
          (mask.drop
              (BinaryDerivationTree.leafCount left)).length =
            BinaryDerivationTree.leafCount right := by
        simp only [BinaryDerivationTree.leafCount] at hlen
        simp [List.length_drop, hlen]
      simp only [markWithMask, LeafMarkedTree.markedWord]
      rw [ihL _ hleft, ihR _ hright]
      have hyieldLeft :
          (BinaryDerivationTree.yield left).length =
            BinaryDerivationTree.leafCount left :=
        BinaryDerivationTree.yield_length
          terminalRule binaryRule left
      rw [BinaryDerivationTree.yield]
      symm
      have hsplit :=
        selectByMask_append_aligned
          (mask.take (BinaryDerivationTree.leafCount left))
          (mask.drop (BinaryDerivationTree.leafCount left))
          (BinaryDerivationTree.yield left)
          (BinaryDerivationTree.yield right)
          (by rw [hleft, hyieldLeft])
      rw [List.take_append_drop
        (BinaryDerivationTree.leafCount left) mask] at hsplit
      exact hsplit

@[simp] theorem trueCount_replicate_true
    (n : Nat) :
    LeafMarkedTree.trueCount (List.replicate n true) = n := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        LeafMarkedTree.trueCount
          (true :: List.replicate n true) = Nat.succ n
      simp only [LeafMarkedTree.trueCount]
      rw [ih]
      omega

@[simp] theorem trueCount_replicate_false
    (n : Nat) :
    LeafMarkedTree.trueCount (List.replicate n false) = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        LeafMarkedTree.trueCount
          (false :: List.replicate n false) = 0
      simp only [LeafMarkedTree.trueCount]
      exact ih

@[simp] theorem falseRanksAux_replicate_true
    (offset n : Nat) :
    LeafMarkedTree.falseRanksAux offset
        (List.replicate n true) =
      [] := by
  induction n generalizing offset with
  | zero =>
      rfl
  | succ n ih =>
      change
        LeafMarkedTree.falseRanksAux
          (offset + 1) (List.replicate n true) = []
      exact ih (offset + 1)

@[simp] theorem falseRanksAux_replicate_false
    (offset n : Nat) :
    LeafMarkedTree.falseRanksAux offset
        (List.replicate n false) =
      List.replicate n offset := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      change
        offset ::
          LeafMarkedTree.falseRanksAux offset
            (List.replicate n false)
          =
        offset :: List.replicate n offset
      rw [ih]

/-- Boolean mask marking the first k and last l leaves among n leaves. -/
def boundaryMask (k l n : Nat) : List Bool :=
  List.replicate k true ++
    List.replicate (n - k - l) false ++
    List.replicate l true

/-- Every false boundary-mask entry occurs after exactly k true entries. -/
theorem falseRanksAux_boundaryMask
    (offset k l n : Nat) :
    LeafMarkedTree.falseRanksAux offset
        (boundaryMask k l n) =
      List.replicate (n - k - l) (offset + k) := by
  unfold boundaryMask
  rw [LeafMarkedTree.falseRanksAux_append]
  rw [LeafMarkedTree.falseRanksAux_append]
  simp [Nat.add_assoc]

/-- The boundary mask contains exactly k+l marked positions. -/
theorem boundaryMask_trueCount
    (k l n : Nat) :
    LeafMarkedTree.trueCount (boundaryMask k l n) =
      k + l := by
  unfold boundaryMask
  rw [LeafMarkedTree.trueCount_append]
  rw [LeafMarkedTree.trueCount_append]
  simp

/-- The boundary mask has the expected total length when k+l <= n. -/
theorem boundaryMask_length
    {k l n : Nat}
    (hfit : k + l ≤ n) :
    (boundaryMask k l n).length = n := by
  simp [boundaryMask]
  omega

/--
Selecting by the boundary mask gives exactly the length-k prefix followed by
the length-l suffix.
-/
theorem selectByMask_boundaryMask
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    selectByMask
        (boundaryMask k l w.length) w
      =
    w.take k ++ w.drop (w.length - l) := by
  let m := w.length - k - l
  let p := w.take k
  let rest := w.drop k
  let mid := rest.take m
  let q := rest.drop m

  have hk : k ≤ w.length := by
    omega
  have hp : p.length = k := by
    dsimp [p]
    simp [List.length_take, hk]
  have hrestLen : rest.length = w.length - k := by
    dsimp [rest]
    simp [List.length_drop]
  have hmle : m ≤ rest.length := by
    dsimp [m]
    rw [hrestLen]
    omega
  have hmid : mid.length = m := by
    dsimp [mid]
    simp [List.length_take, hmle]
  have hw : w = p ++ (mid ++ q) := by
    have h₁ : w = p ++ rest := by
      dsimp [p, rest]
      exact (List.take_append_drop k w).symm
    have h₂ : rest = mid ++ q := by
      dsimp [mid, q]
      exact (List.take_append_drop m rest).symm
    calc
      w = p ++ rest := h₁
      _ = p ++ (mid ++ q) := by rw [h₂]
  have hmask :
      boundaryMask k l w.length =
        List.replicate k true ++
          (List.replicate m false ++
            List.replicate l true) := by
    unfold boundaryMask
    dsimp [m]
    simp [List.append_assoc]

  have hsel :
      selectByMask
          (boundaryMask k l w.length) w =
        p ++ q := by
    calc
      selectByMask
          (boundaryMask k l w.length) w
          =
        selectByMask
          (List.replicate k true ++
            (List.replicate m false ++
              List.replicate l true))
          (p ++ (mid ++ q)) := by
            rw [hmask, hw]
      _ =
        selectByMask (List.replicate k true) p ++
          selectByMask
            (List.replicate m false ++
              List.replicate l true)
            (mid ++ q) :=
          selectByMask_append_aligned
            (List.replicate k true)
            (List.replicate m false ++
              List.replicate l true)
            p (mid ++ q)
            (by simp [hp])
      _ =
        p ++
          (selectByMask (List.replicate m false) mid ++
            selectByMask (List.replicate l true) q) := by
          have hpTrue :
              selectByMask (List.replicate k true) p = p := by
            rw [← hp]
            exact selectByMask_replicate_true p
          rw [hpTrue]
          rw [selectByMask_append_aligned
            (List.replicate m false)
            (List.replicate l true)
            mid q
            (by simp [hmid])]
      _ = p ++ q := by
          have hmidFalse :
              selectByMask (List.replicate m false) mid = [] := by
            rw [← hmid]
            exact selectByMask_replicate_false mid
          have hqLen : q.length = l := by
            dsimp [q]
            rw [List.length_drop, hrestLen]
            dsimp [m]
            omega
          have hqTrue :
              selectByMask (List.replicate l true) q = q := by
            rw [← hqLen]
            exact selectByMask_replicate_true q
          rw [hmidFalse, hqTrue]
          simp

  have hq :
      q = w.drop (w.length - l) := by
    dsimp [q, rest, m]
    rw [List.drop_drop]
    congr 1
    omega

  calc
    selectByMask
        (boundaryMask k l w.length) w
        = p ++ q := hsel
    _ = w.take k ++ w.drop (w.length - l) := by
        dsimp [p]
        rw [hq]

/--
The selected boundary word has exactly k+l letters.
-/
theorem boundary_selected_length
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    (w.take k ++ w.drop (w.length - l)).length =
      k + l := by
  have hk : k ≤ w.length := by omega
  simp only [List.length_append]
  rw [List.length_take, Nat.min_eq_left hk]
  rw [List.length_drop]
  omega

/-- Taking exactly the length of a left concatenand recovers it. -/
theorem take_append_of_prefix_length
    (p q : Word α)
    (k : Nat)
    (hp : p.length = k) :
    (p ++ q).take k = p := by
  subst k
  induction p with
  | nil =>
      rfl
  | cons a p ih =>
      simp [ih]

/-- Dropping exactly the length of a left concatenand removes it. -/
theorem drop_append_of_prefix_length
    (p q : Word α)
    (k : Nat)
    (hp : p.length = k) :
    (p ++ q).drop k = q := by
  subst k
  induction p with
  | nil =>
      rfl
  | cons a p ih =>
      simp [ih]

/-- Length of the fixed-window prefix. -/
theorem fixedWindow_prefix_length
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    (w.take k).length = k := by
  have hk : k ≤ w.length := by
    omega
  simp [List.length_take, hk]

/-- Length of the fixed-window suffix. -/
theorem fixedWindow_suffix_length
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    (w.drop (w.length - l)).length = l := by
  rw [List.length_drop]
  omega

/--
Every long-enough word decomposes into its length-k prefix, an arbitrary
middle, and its length-l suffix.
-/
theorem exists_fixedWindow_middle
    (w : Word α)
    (k l : Nat)
    (hfit : k + l ≤ w.length) :
    ∃ middle : Word α,
      w =
        w.take k ++ middle ++
          w.drop (w.length - l) := by
  let rest := w.drop k
  let middle := rest.take (w.length - k - l)
  let q := rest.drop (w.length - k - l)
  have h₁ :
      w = w.take k ++ rest := by
    dsimp [rest]
    exact (List.take_append_drop k w).symm
  have h₂ :
      rest = middle ++ q := by
    dsimp [middle, q]
    exact
      (List.take_append_drop
        (w.length - k - l) rest).symm
  have hq :
      q = w.drop (w.length - l) := by
    dsimp [q, rest]
    rw [List.drop_drop]
    congr 1
    omega
  refine ⟨middle, ?_⟩
  calc
    w = w.take k ++ rest := h₁
    _ = w.take k ++ (middle ++ q) := by
      rw [h₂]
    _ = w.take k ++ middle ++ q := by
      rw [List.append_assoc]
    _ = w.take k ++ middle ++
          w.drop (w.length - l) := by
      rw [hq]

/--
For the aligned boundary marking, every unmarked leaf lies after exactly k
marked leaves.
-/
theorem boundary_markedTree_all_unmarked_at
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (T : BinaryDerivationTree terminalRule binaryRule A)
    (k l : Nat)
    (hfit :
      k + l ≤
        BinaryDerivationTree.leafCount T) :
    ∀ j ∈
      LeafMarkedTree.unmarkedRanksAux 0
        (markWithMask T
          (boundaryMask k l
            (BinaryDerivationTree.leafCount T))),
      j = k := by
  let mask :=
    boundaryMask k l
      (BinaryDerivationTree.leafCount T)
  have hmask :
      mask.length =
        BinaryDerivationTree.leafCount T := by
    dsimp [mask]
    exact boundaryMask_length hfit
  have hranks :
      LeafMarkedTree.unmarkedRanksAux 0
          (markWithMask T mask)
        =
      List.replicate
        (BinaryDerivationTree.leafCount T - k - l) k := by
    rw [LeafMarkedTree.unmarkedRanksAux_eq_falseRanksAux
      terminalRule binaryRule]
    rw [leafMarks_markWithMask
      terminalRule binaryRule T mask hmask]
    dsimp [mask]
    simpa using
      falseRanksAux_boundaryMask 0 k l
        (BinaryDerivationTree.leafCount T)
  intro j hj
  rw [hranks] at hj
  simp only [List.mem_replicate] at hj
  exact hj.2

/--
Tree-surgery input for Lemma 7.1.

From any successful derivation whose yield has at least k+l terminals, with
k+l>0, we obtain the pruned union of root paths to exactly the first k and
last l terminal leaves.
-/
theorem exists_fixedWindow_boundary_kernel
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.originalYield K = w
      ∧
      MarkedBoundaryKernel.markedWord K =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K = k + l := by
  obtain ⟨T, hT⟩ :=
    BinaryDerivationTree.exists_of_derivation
      terminalRule binaryRule d
  let mask := boundaryMask k l w.length
  let MT := markWithMask T mask

  have hleaf :
      BinaryDerivationTree.leafCount T = w.length := by
    rw [← BinaryDerivationTree.yield_length
      terminalRule binaryRule T, hT]

  have hmaskLen :
      mask.length =
        BinaryDerivationTree.leafCount T := by
    dsimp [mask]
    rw [boundaryMask_length hfit, hleaf]

  have hmarkedWord :
      LeafMarkedTree.markedWord MT =
        w.take k ++ w.drop (w.length - l) := by
    dsimp [MT]
    rw [markWithMask_markedWord
      terminalRule binaryRule T mask hmaskLen]
    rw [hT]
    exact selectByMask_boundaryMask w k l hfit

  have hmarkedCount :
      LeafMarkedTree.markedCount MT = k + l := by
    have hlen :=
      LeafMarkedTree.markedWord_length
        terminalRule binaryRule MT
    rw [hmarkedWord,
      boundary_selected_length w k l hfit] at hlen
    exact hlen.symm

  have hpos :
      0 < LeafMarkedTree.markedCount MT := by
    rw [hmarkedCount]
    exact hr

  obtain ⟨K, hYield, hWord, hCount⟩ :=
    LeafMarkedTree.exists_pruned_kernel
      terminalRule binaryRule MT hpos

  refine ⟨K, ?_, ?_, ?_⟩
  · rw [hYield]
    dsimp [MT]
    rw [markWithMask_yield
      terminalRule binaryRule T mask, hT]
  · rw [hWord, hmarkedWord]
  · rw [hCount, hmarkedCount]


/--
Rank-aware fixed-window boundary kernel.

Besides the three basic boundary facts, every omitted sibling subtree occurs
in the single central gap after the first k marked leaves.  This positional
invariant is what is needed to show that arbitrary same-root short
replacements preserve the prefix/suffix summary.
-/
theorem exists_fixedWindow_boundary_kernel_ranked
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    {w : Word α}
    (d : UntypedDerives terminalRule binaryRule A w)
    (k l : Nat)
    (hr : 0 < k + l)
    (hfit : k + l ≤ w.length) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.originalYield K = w
      ∧
      MarkedBoundaryKernel.markedWord K =
        w.take k ++ w.drop (w.length - l)
      ∧
      MarkedBoundaryKernel.markedLeafCount K = k + l
      ∧
      MarkedBoundaryKernel.AllOmissionsAt K k := by
  obtain ⟨T, hT⟩ :=
    BinaryDerivationTree.exists_of_derivation
      terminalRule binaryRule d
  let mask := boundaryMask k l w.length
  let MT := markWithMask T mask

  have hleaf :
      BinaryDerivationTree.leafCount T = w.length := by
    rw [← BinaryDerivationTree.yield_length
      terminalRule binaryRule T, hT]

  have hmaskLen :
      mask.length =
        BinaryDerivationTree.leafCount T := by
    dsimp [mask]
    rw [boundaryMask_length hfit, hleaf]

  have hmarkedWord :
      LeafMarkedTree.markedWord MT =
        w.take k ++ w.drop (w.length - l) := by
    dsimp [MT]
    rw [markWithMask_markedWord
      terminalRule binaryRule T mask hmaskLen]
    rw [hT]
    exact selectByMask_boundaryMask w k l hfit

  have hmarkedCount :
      LeafMarkedTree.markedCount MT = k + l := by
    have hlen :=
      LeafMarkedTree.markedWord_length
        terminalRule binaryRule MT
    rw [hmarkedWord,
      boundary_selected_length w k l hfit] at hlen
    exact hlen.symm

  have hpos :
      0 < LeafMarkedTree.markedCount MT := by
    rw [hmarkedCount]
    exact hr

  have hfitT :
      k + l ≤ BinaryDerivationTree.leafCount T := by
    rw [hleaf]
    exact hfit

  have hAllUnmarked :
      ∀ j ∈ LeafMarkedTree.unmarkedRanksAux 0 MT,
        j = k := by
    dsimp [MT, mask]
    simpa [hleaf] using
      (boundary_markedTree_all_unmarked_at
        terminalRule binaryRule T k l hfitT)

  obtain ⟨K, hYield, hWord, hCount, hRankSubset⟩ :=
    LeafMarkedTree.exists_pruned_kernel_with_rank_subset
      terminalRule binaryRule MT hpos 0

  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · rw [hYield]
    dsimp [MT]
    rw [markWithMask_yield
      terminalRule binaryRule T mask, hT]
  · rw [hWord, hmarkedWord]
  · rw [hCount, hmarkedCount]
  · intro j hj
    exact hAllUnmarked j
      (hRankSubset j hj)

end FixedWindowBoundaryMarking

end TCS1
end LeanCfgProject
