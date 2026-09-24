import LeanCfgProject.TCS1.MarkedBoundaryGapSemantic

/-!
# TCS #1 v68: gap-aware marked-boundary normalization

This module lifts the central-gap invariant from individual reaching spines to
the full marked-boundary normalization used in Lemma 7.1.

The first layer below handles a normalized unary head attached to a base.  It
records that:

* every omitted sibling on the head lies in the unique global gap k; and
* every omission already contained in the base lies in that same gap.

The later recursive layer will use this attachment theorem to cycle-shorten a
whole marked-boundary kernel without losing the first-k / last-l positional
invariant.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryGapNormalization

variable {N : Type u}
variable {α : Type v}

/-- Central-gap invariant for the endpoint base of a unary head. -/
def MarkedBoundaryBaseAllOmissionsAtAux
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat) :
    {A : N} →
    MarkedBoundaryBase terminalRule binaryRule A →
    Prop
  | _, MarkedBoundaryBase.marked _ _ =>
      True
  | _, MarkedBoundaryBase.branch _ left right =>
      MarkedBoundaryKernel.AllOmissionsAtAux
          offset left k
        ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
          (offset + MarkedBoundaryKernel.markedLeafCount left)
          right k

/-- Forgetting the base wrapper preserves its central-gap invariant. -/
theorem markedBoundaryBase_toKernel_preserves_gap
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    (base :
      MarkedBoundaryBase terminalRule binaryRule A)
    (hgap :
      MarkedBoundaryBaseAllOmissionsAtAux
        terminalRule binaryRule offset k base) :
    MarkedBoundaryKernel.AllOmissionsAtAux
      offset (MarkedBoundaryBase.toKernel base) k := by
  cases base with
  | marked a hterm =>
      intro j hj
      simp [MarkedBoundaryBase.toKernel,
        MarkedBoundaryKernel.AllOmissionsAtAux,
        MarkedBoundaryKernel.omissionRanksAux] at hj
  | branch hbin left right =>
      exact
        (MarkedBoundaryKernel.allOmissionsAtAux_branch_iff
          hbin left right offset k).2 hgap

/--
Attach a gap-certified unary head above a gap-certified base.

The explicit `marks` parameter keeps the base independent of the spine
during induction; `hbaseMarks` identifies it with the number of marked leaves
carried by the base.
-/
theorem exists_attachGapHead
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset marks k : Nat)
    {A X : N}
    {left right : Word α}
    {path : List N}
    {siblings : List Nat}
    (spine :
      GapReachingSpine terminalRule binaryRule
        offset marks k
        A X left right path siblings)
    (base :
      MarkedBoundaryBase terminalRule binaryRule X)
    (hbaseMarks :
      MarkedBoundaryBase.markedLeafCount base = marks)
    (hbase :
      MarkedBoundaryBaseAllOmissionsAtAux
        terminalRule binaryRule offset k base) :
    ∃ K : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K = marks
      ∧
      MarkedBoundaryKernel.omittedCount K =
        siblings.length +
          MarkedBoundaryBase.omittedBelow base
      ∧
      MarkedBoundaryKernel.markedWord K =
        MarkedBoundaryBase.markedWord base
      ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K k := by
  induction spine with
  | hole =>
      refine
        ⟨MarkedBoundaryBase.toKernel base,
          ?_, ?_,
          MarkedBoundaryBase.toKernel_markedWord
            terminalRule binaryRule base,
          ?_⟩
      · rw [MarkedBoundaryBase.toKernel_markedLeafCount
          terminalRule binaryRule base]
        exact hbaseMarks
      · simpa using
          MarkedBoundaryBase.toKernel_omittedCount
            terminalRule binaryRule base
      · exact
          markedBoundaryBase_toKernel_preserves_gap
            terminalRule binaryRule offset k base hbase

  | @binaryLeft A B C X left right z path siblings
      hbin child sibling hgap ih =>
      obtain ⟨K, hmarks, homit, hword, hKgap⟩ :=
        ih base hbaseMarks hbase
      refine
        ⟨MarkedBoundaryKernel.unaryLeft
            hbin K z sibling,
          ?_, ?_, ?_, ?_⟩
      · simpa [MarkedBoundaryKernel.markedLeafCount]
          using hmarks
      · simp only [MarkedBoundaryKernel.omittedCount,
          List.length_cons]
        rw [homit]
        omega
      · simpa [MarkedBoundaryKernel.markedWord]
          using hword
      · apply
          (MarkedBoundaryKernel.allOmissionsAtAux_unaryLeft_iff
            hbin K z sibling offset k).2
        refine ⟨hKgap, ?_⟩
        rw [hmarks]
        exact hgap

  | @binaryRight A B C X left right y path siblings
      hbin sibling child hgap ih =>
      obtain ⟨K, hmarks, homit, hword, hKgap⟩ :=
        ih base hbaseMarks hbase
      refine
        ⟨MarkedBoundaryKernel.unaryRight
            hbin y sibling K,
          ?_, ?_, ?_, ?_⟩
      · simpa [MarkedBoundaryKernel.markedLeafCount]
          using hmarks
      · simp only [MarkedBoundaryKernel.omittedCount,
          List.length_cons]
        rw [homit]
        omega
      · simpa [MarkedBoundaryKernel.markedWord]
          using hword
      · apply
          (MarkedBoundaryKernel.allOmissionsAtAux_unaryRight_iff
            hbin y sibling K offset k).2
        exact ⟨hgap, hKgap⟩

/--
Gap-aware normalized head/base decomposition.

The unary head has already been cycle-shortened to a repetition-free path.
Both the head and the base carry the same global central-gap invariant.
-/
structure GapNormalizedHeadData
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) where
  target : N
  left : Word α
  right : Word α
  path : List N
  siblings : List Nat
  base :
    MarkedBoundaryBase terminalRule binaryRule target
  spine :
    GapReachingSpine terminalRule binaryRule
      offset (MarkedBoundaryBase.markedLeafCount base) k
      A target left right path siblings
  path_nodup : path.Nodup
  marks_eq :
    MarkedBoundaryBase.markedLeafCount base =
      MarkedBoundaryKernel.markedLeafCount K
  word_eq :
    MarkedBoundaryBase.markedWord base =
      MarkedBoundaryKernel.markedWord K
  base_gap :
    MarkedBoundaryBaseAllOmissionsAtAux
      terminalRule binaryRule offset k base
  tail_bound :
    MarkedBoundaryBase.omittedBelow base ≤
      (2 * MarkedBoundaryKernel.markedLeafCount K - 2) *
        Fintype.card N

/-- A gap-aware normalized unary head contains at most |N| omissions. -/
theorem gapNormalizedHead_siblings_le_card
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    {K : MarkedBoundaryKernel terminalRule binaryRule A}
    (D :
      GapNormalizedHeadData
        terminalRule binaryRule offset k K) :
    D.siblings.length ≤ Fintype.card N := by
  have hpath :
      D.path.length ≤ Fintype.card N :=
    dependency_path_vertices_le
      D.path D.path_nodup
  have hstep :
      D.siblings.length + 1 = D.path.length :=
    gapReachingSpine_siblings_length_add_one_eq_path
      terminalRule binaryRule
      offset
      (MarkedBoundaryBase.markedLeafCount D.base)
      k D.spine
  omega

/--
Attach gap-aware normalized head data.

The result simultaneously preserves the marked word, satisfies the manuscript
omitted-sibling bound, and retains the central-gap invariant.
-/
theorem gapNormalizedHead_attach_bound
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset k : Nat)
    {A : N}
    {K : MarkedBoundaryKernel terminalRule binaryRule A}
    (D :
      GapNormalizedHeadData
        terminalRule binaryRule offset k K) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K' =
        MarkedBoundaryKernel.markedLeafCount K
      ∧
      MarkedBoundaryKernel.markedWord K' =
        MarkedBoundaryKernel.markedWord K
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N
      ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K' k := by
  obtain ⟨K', hmarks, homit, hword, hgap⟩ :=
    exists_attachGapHead
      terminalRule binaryRule
      offset
      (MarkedBoundaryBase.markedLeafCount D.base)
      k D.spine D.base rfl D.base_gap
  have hhead :
      D.siblings.length ≤ Fintype.card N :=
    gapNormalizedHead_siblings_le_card
      terminalRule binaryRule offset k D
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
  refine ⟨K', ?_, ?_, ?_, hgap⟩
  · rw [hmarks, D.marks_eq]
  · rw [hword, D.word_eq]
  · rw [homit]
    exact le_trans hsum (le_of_eq hfactor)

/--
Every gap-certified marked-boundary kernel admits a cycle-shortened
gap-certified head/base decomposition.
-/
theorem exists_gapNormalizedHeadData
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (offset k : Nat)
    (hgap :
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K k) :
    Nonempty
      (GapNormalizedHeadData
        terminalRule binaryRule offset k K) := by
  induction K generalizing offset k with
  | @marked A a hterm =>
      refine ⟨{
        target := A
        left := []
        right := []
        path := [A]
        siblings := []
        base := MarkedBoundaryBase.marked a hterm
        spine := GapReachingSpine.hole
        path_nodup := by simp
        marks_eq := by
          simp [MarkedBoundaryBase.markedLeafCount,
            MarkedBoundaryKernel.markedLeafCount]
        word_eq := by
          simp [MarkedBoundaryBase.markedWord,
            MarkedBoundaryKernel.markedWord]
        base_gap := by
          trivial
        tail_bound := by
          simp [MarkedBoundaryBase.omittedBelow,
            MarkedBoundaryKernel.markedLeafCount]
      }⟩

  | @unaryLeft A B C hbin child siblingWord sibling ih =>
      obtain ⟨hchildGap, hlast⟩ :=
        (MarkedBoundaryKernel.allOmissionsAtAux_unaryLeft_iff
          hbin child siblingWord sibling offset k).1 hgap
      obtain ⟨D⟩ :=
        ih offset k hchildGap
      have hlastBase :
          offset + MarkedBoundaryBase.markedLeafCount D.base = k := by
        rw [D.marks_eq]
        exact hlast
      let preSpine :
          GapReachingSpine terminalRule binaryRule
            offset
            (MarkedBoundaryBase.markedLeafCount D.base)
            k
            A D.target
            D.left (D.right ++ siblingWord)
            (A :: D.path)
            (siblingWord.length :: D.siblings) :=
        GapReachingSpine.binaryLeft
          hbin D.spine sibling hlastBase
      obtain ⟨left', right', path', siblings',
          spine', hnodup'⟩ :=
        normalize_gapReachingSpine_to_nodup
          terminalRule binaryRule
          offset
          (MarkedBoundaryBase.markedLeafCount D.base)
          k preSpine
      refine ⟨{
        target := D.target
        left := left'
        right := right'
        path := path'
        siblings := siblings'
        base := D.base
        spine := spine'
        path_nodup := hnodup'
        marks_eq := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.marks_eq
        word_eq := by
          simpa [MarkedBoundaryKernel.markedWord]
            using D.word_eq
        base_gap := D.base_gap
        tail_bound := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.tail_bound
      }⟩

  | @unaryRight A B C hbin siblingWord sibling child ih =>
      obtain ⟨hfirst, hchildGap⟩ :=
        (MarkedBoundaryKernel.allOmissionsAtAux_unaryRight_iff
          hbin siblingWord sibling child offset k).1 hgap
      obtain ⟨D⟩ :=
        ih offset k hchildGap
      let preSpine :
          GapReachingSpine terminalRule binaryRule
            offset
            (MarkedBoundaryBase.markedLeafCount D.base)
            k
            A D.target
            (siblingWord ++ D.left) D.right
            (A :: D.path)
            (siblingWord.length :: D.siblings) :=
        GapReachingSpine.binaryRight
          hbin sibling D.spine hfirst
      obtain ⟨left', right', path', siblings',
          spine', hnodup'⟩ :=
        normalize_gapReachingSpine_to_nodup
          terminalRule binaryRule
          offset
          (MarkedBoundaryBase.markedLeafCount D.base)
          k preSpine
      refine ⟨{
        target := D.target
        left := left'
        right := right'
        path := path'
        siblings := siblings'
        base := D.base
        spine := spine'
        path_nodup := hnodup'
        marks_eq := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.marks_eq
        word_eq := by
          simpa [MarkedBoundaryKernel.markedWord]
            using D.word_eq
        base_gap := D.base_gap
        tail_bound := by
          simpa [MarkedBoundaryKernel.markedLeafCount]
            using D.tail_bound
      }⟩

  | @branch A B C hbin left right ihL ihR =>
      obtain ⟨hleftGap, hrightGap⟩ :=
        (MarkedBoundaryKernel.allOmissionsAtAux_branch_iff
          hbin left right offset k).1 hgap
      obtain ⟨DL⟩ :=
        ihL offset k hleftGap
      obtain ⟨DR⟩ :=
        ihR
          (offset + MarkedBoundaryKernel.markedLeafCount left)
          k hrightGap
      obtain ⟨left', hleftMarks, hleftWord,
          hleftBound, hleftGap'⟩ :=
        gapNormalizedHead_attach_bound
          terminalRule binaryRule offset k DL
      obtain ⟨right', hrightMarks, hrightWord,
          hrightBound, hrightGap'⟩ :=
        gapNormalizedHead_attach_bound
          terminalRule binaryRule
          (offset + MarkedBoundaryKernel.markedLeafCount left)
          k DR
      let base :
          MarkedBoundaryBase terminalRule binaryRule A :=
        MarkedBoundaryBase.branch hbin left' right'
      have hrightGap'' :
          MarkedBoundaryKernel.AllOmissionsAtAux
            (offset +
              MarkedBoundaryKernel.markedLeafCount left')
            right' k := by
        rw [hleftMarks]
        exact hrightGap'
      have hbaseGap :
          MarkedBoundaryBaseAllOmissionsAtAux
            terminalRule binaryRule offset k base := by
        dsimp [base, MarkedBoundaryBaseAllOmissionsAtAux]
        exact ⟨hleftGap', hrightGap''⟩
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
        base := base
        spine := GapReachingSpine.hole
        path_nodup := by simp
        marks_eq := by
          dsimp [base, MarkedBoundaryBase.markedLeafCount]
          rw [hleftMarks, hrightMarks]
          simp [MarkedBoundaryKernel.markedLeafCount]
        word_eq := by
          dsimp [base, MarkedBoundaryBase.markedWord]
          rw [hleftWord, hrightWord]
          simp [MarkedBoundaryKernel.markedWord]
        base_gap := hbaseGap
        tail_bound := htail
      }⟩

/--
Cycle-shortening theorem with the central-gap invariant preserved.
-/
theorem exists_cycle_shortened_kernel_preserving_gap
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (offset k : Nat)
    (hgap :
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K k) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K' =
        MarkedBoundaryKernel.markedLeafCount K
      ∧
      MarkedBoundaryKernel.markedWord K' =
        MarkedBoundaryKernel.markedWord K
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N
      ∧
      MarkedBoundaryKernel.AllOmissionsAtAux
        offset K' k := by
  obtain ⟨D⟩ :=
    exists_gapNormalizedHeadData
      terminalRule binaryRule K offset k hgap
  exact
    gapNormalizedHead_attach_bound
      terminalRule binaryRule offset k D

/-- Zero-offset public version using `AllOmissionsAt`. -/
theorem exists_cycle_shortened_kernel_preserving_allOmissionsAt
    [Fintype N] [DecidableEq N]
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (k : Nat)
    (hgap :
      MarkedBoundaryKernel.AllOmissionsAt K k) :
    ∃ K' : MarkedBoundaryKernel terminalRule binaryRule A,
      MarkedBoundaryKernel.markedLeafCount K' =
        MarkedBoundaryKernel.markedLeafCount K
      ∧
      MarkedBoundaryKernel.markedWord K' =
        MarkedBoundaryKernel.markedWord K
      ∧
      MarkedBoundaryKernel.omittedCount K' ≤
        (2 * MarkedBoundaryKernel.markedLeafCount K - 1) *
          Fintype.card N
      ∧
      MarkedBoundaryKernel.AllOmissionsAt K' k := by
  have haux :
      MarkedBoundaryKernel.AllOmissionsAtAux
        0 K k :=
    (MarkedBoundaryKernel.allOmissionsAt_iff_aux_zero
      K k).1 hgap
  obtain ⟨K', hmarks, hword, hbound, haux'⟩ :=
    exists_cycle_shortened_kernel_preserving_gap
      terminalRule binaryRule K 0 k haux
  exact
    ⟨K', hmarks, hword, hbound,
      (MarkedBoundaryKernel.allOmissionsAt_iff_aux_zero
        K' k).2 haux'⟩

end MarkedBoundaryGapNormalization

end TCS1
end LeanCfgProject
