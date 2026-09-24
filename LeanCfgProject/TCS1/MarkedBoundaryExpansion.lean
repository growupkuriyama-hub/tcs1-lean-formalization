import LeanCfgProject.TCS1.MarkedBoundaryGapNormalization
import LeanCfgProject.TCS1.FixedWindowBoundarySemantic

/-!
# TCS #1 v68: expansion witnesses for marked-boundary reconstruction

A marked-boundary kernel contains marked terminal leaves and omitted sibling
subtrees.  Its `boundaryTemplate` replaces every omitted sibling by a
`none` placeholder.

This module makes the reconstruction step explicit.  A `BoundaryExpansion`
replaces the placeholders, from left to right, by a list of terminal words.
For every marked-boundary kernel, if every nonterminal has a terminal yield of
length at most tau, we construct:

* a genuine reconstructed derivation;
* the ordered list of replacement blocks;
* an expansion certificate against the kernel template;
* the exact number of blocks; and
* the uniform tau length bound.

The remaining positional lemma can therefore reason purely about the template
and its unique central gap.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section MarkedBoundaryExpansion

variable {N : Type u}
variable {α : Type v}

/-- Replace `none` placeholders by terminal blocks, preserving all `some`
terminals. -/
inductive BoundaryExpansion :
    List (Option α) → List (Word α) → Word α → Prop
  | nil :
      BoundaryExpansion [] [] []
  | some
      {a : α}
      {template : List (Option α)}
      {blocks : List (Word α)}
      {w : Word α}
      (tail :
        BoundaryExpansion template blocks w) :
      BoundaryExpansion
        (Option.some a :: template)
        blocks
        (a :: w)
  | none
      {template : List (Option α)}
      {blocks : List (Word α)}
      {w block : Word α}
      (tail :
        BoundaryExpansion template blocks w) :
      BoundaryExpansion
        (Option.none :: template)
        (block :: blocks)
        (block ++ w)

/-- Number of marked terminals in a boundary template. -/
def templateMarkedCount : List (Option α) → Nat
  | [] => 0
  | Option.some _ :: t => 1 + templateMarkedCount t
  | Option.none :: t => templateMarkedCount t

/-- Number of omission placeholders in a boundary template. -/
def templateOmissionCount : List (Option α) → Nat
  | [] => 0
  | Option.some _ :: t => templateOmissionCount t
  | Option.none :: t => 1 + templateOmissionCount t

/-- Marked terminals of a template, in left-to-right order. -/
def templateMarkedWord : List (Option α) → Word α
  | [] => []
  | Option.some a :: t => a :: templateMarkedWord t
  | Option.none :: t => templateMarkedWord t

/-- Marked-leaf ranks of the omission placeholders. -/
def templateOmissionRanksAux : Nat → List (Option α) → List Nat
  | _, [] => []
  | offset, Option.some _ :: t =>
      templateOmissionRanksAux (offset + 1) t
  | offset, Option.none :: t =>
      offset :: templateOmissionRanksAux offset t

@[simp] theorem templateMarkedCount_append
    (t₁ t₂ : List (Option α)) :
    templateMarkedCount (t₁ ++ t₂) =
      templateMarkedCount t₁ + templateMarkedCount t₂ := by
  induction t₁ with
  | nil =>
      simp [templateMarkedCount]
  | cons x t ih =>
      cases x with
      | none =>
          simp [templateMarkedCount, ih]
      | some a =>
          simp [templateMarkedCount, ih, Nat.add_assoc]

@[simp] theorem templateOmissionCount_append
    (t₁ t₂ : List (Option α)) :
    templateOmissionCount (t₁ ++ t₂) =
      templateOmissionCount t₁ + templateOmissionCount t₂ := by
  induction t₁ with
  | nil =>
      simp [templateOmissionCount]
  | cons x t ih =>
      cases x with
      | none =>
          simp [templateOmissionCount, ih, Nat.add_assoc]
      | some a =>
          simp [templateOmissionCount, ih]

@[simp] theorem templateMarkedWord_append
    (t₁ t₂ : List (Option α)) :
    templateMarkedWord (t₁ ++ t₂) =
      templateMarkedWord t₁ ++ templateMarkedWord t₂ := by
  induction t₁ with
  | nil =>
      rfl
  | cons x t ih =>
      cases x with
      | none =>
          simp [templateMarkedWord, ih]
      | some a =>
          simp [templateMarkedWord, ih]

theorem templateOmissionRanksAux_append
    (offset : Nat)
    (t₁ t₂ : List (Option α)) :
    templateOmissionRanksAux offset (t₁ ++ t₂) =
      templateOmissionRanksAux offset t₁ ++
        templateOmissionRanksAux
          (offset + templateMarkedCount t₁) t₂ := by
  induction t₁ generalizing offset with
  | nil =>
      simp [templateOmissionRanksAux, templateMarkedCount]
  | cons x t ih =>
      cases x with
      | none =>
          simp [templateOmissionRanksAux,
            templateMarkedCount, ih offset]
      | some a =>
          simp only [List.cons_append,
            templateOmissionRanksAux,
            templateMarkedCount]
          rw [ih (offset + 1)]
          congr 2
          omega

/-- Taking commutes with marking every terminal by `some`. -/
theorem take_map_some
    (w : Word α)
    (n : Nat) :
    (w.map Option.some).take n =
      (w.take n).map Option.some := by
  induction w generalizing n with
  | nil =>
      simp
  | cons a w ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          change
            Option.some a ::
                (w.map Option.some).take n =
              Option.some a ::
                (w.take n).map Option.some
          exact
            congrArg (List.cons (Option.some a))
              (ih n)

/-- Dropping commutes with marking every terminal by `some`. -/
theorem drop_map_some
    (w : Word α)
    (n : Nat) :
    (w.map Option.some).drop n =
      (w.drop n).map Option.some := by
  induction w generalizing n with
  | nil =>
      simp
  | cons a w ih =>
      cases n with
      | zero =>
          rfl
      | succ n =>
          change
            (w.map Option.some).drop n =
              (w.drop n).map Option.some
          exact ih n

/-- The kernel template contains one marked entry per marked leaf. -/
theorem boundaryTemplate_markedCount
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    templateMarkedCount
        (MarkedBoundaryKernel.boundaryTemplate K) =
      MarkedBoundaryKernel.markedLeafCount K := by
  induction K with
  | marked =>
      rfl
  | unaryLeft hbin child siblingWord sibling ih =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateMarkedCount, ih,
        MarkedBoundaryKernel.markedLeafCount]
  | unaryRight hbin siblingWord sibling child ih =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateMarkedCount, ih,
        MarkedBoundaryKernel.markedLeafCount]
  | branch hbin left right ihL ihR =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateMarkedCount, ihL, ihR,
        MarkedBoundaryKernel.markedLeafCount]

/-- The kernel template contains one placeholder per omitted sibling. -/
theorem boundaryTemplate_omissionCount
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    templateOmissionCount
        (MarkedBoundaryKernel.boundaryTemplate K) =
      MarkedBoundaryKernel.omittedCount K := by
  induction K with
  | marked =>
      rfl
  | unaryLeft hbin child siblingWord sibling ih =>
      simp only [MarkedBoundaryKernel.boundaryTemplate,
        templateOmissionCount_append,
        templateOmissionCount,
        MarkedBoundaryKernel.omittedCount]
      rw [ih]
      omega
  | unaryRight hbin siblingWord sibling child ih =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateOmissionCount, ih,
        MarkedBoundaryKernel.omittedCount]
  | branch hbin left right ihL ihR =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateOmissionCount, ihL, ihR,
        MarkedBoundaryKernel.omittedCount]

/-- Filtering the template placeholders recovers the marked terminal word. -/
theorem boundaryTemplate_markedWord
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    templateMarkedWord
        (MarkedBoundaryKernel.boundaryTemplate K) =
      MarkedBoundaryKernel.markedWord K := by
  induction K with
  | marked =>
      rfl
  | unaryLeft hbin child siblingWord sibling ih =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateMarkedWord, ih,
        MarkedBoundaryKernel.markedWord]
  | unaryRight hbin siblingWord sibling child ih =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateMarkedWord, ih,
        MarkedBoundaryKernel.markedWord]
  | branch hbin left right ihL ihR =>
      simp [MarkedBoundaryKernel.boundaryTemplate,
        templateMarkedWord, ihL, ihR,
        MarkedBoundaryKernel.markedWord]

/-- Template omission ranks coincide with the structural kernel ranks. -/
theorem boundaryTemplate_omissionRanksAux
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (offset : Nat)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    templateOmissionRanksAux offset
        (MarkedBoundaryKernel.boundaryTemplate K) =
      MarkedBoundaryKernel.omissionRanksAux offset K := by
  induction K generalizing offset with
  | marked =>
      rfl
  | unaryLeft hbin child siblingWord sibling ih =>
      rw [MarkedBoundaryKernel.boundaryTemplate]
      rw [templateOmissionRanksAux_append]
      rw [ih offset]
      rw [boundaryTemplate_markedCount
        terminalRule binaryRule child]
      rfl
  | unaryRight hbin siblingWord sibling child ih =>
      simp only [MarkedBoundaryKernel.boundaryTemplate,
        templateOmissionRanksAux,
        MarkedBoundaryKernel.omissionRanksAux]
      rw [ih offset]
  | branch hbin left right ihL ihR =>
      rw [MarkedBoundaryKernel.boundaryTemplate]
      rw [templateOmissionRanksAux_append]
      rw [ihL offset]
      rw [boundaryTemplate_markedCount
        terminalRule binaryRule left]
      rw [ihR
        (offset + MarkedBoundaryKernel.markedLeafCount left)]
      rfl

/--
If the unique omission gap lies strictly before the incoming offset, the
template has no omissions at all.
-/
theorem template_no_omissions_of_gap_lt_offset
    (t : List (Option α))
    (offset k : Nat)
    (hlt : k < offset)
    (hgap :
      ∀ j ∈ templateOmissionRanksAux offset t,
        j = k) :
    templateOmissionCount t = 0
      ∧ t = (templateMarkedWord t).map Option.some := by
  induction t generalizing offset with
  | nil =>
      exact ⟨rfl, rfl⟩
  | cons x t ih =>
      cases x with
      | none =>
          have hEq : offset = k :=
            hgap offset
              (by
                simp [templateOmissionRanksAux])
          omega
      | some a =>
          have htail :
              ∀ j ∈
                templateOmissionRanksAux (offset + 1) t,
                j = k := by
            intro j hj
            exact hgap j
              (by
                simpa [templateOmissionRanksAux] using hj)
          have hlt' : k < offset + 1 := by
            omega
          obtain ⟨hzero, hshape⟩ :=
            ih (offset + 1) hlt' htail
          constructor
          · simpa [templateOmissionCount] using hzero
          · change
              Option.some a :: t =
                Option.some a ::
                  (templateMarkedWord t).map Option.some
            exact congrArg (List.cons (Option.some a)) hshape

/--
A template whose every omission has marked-rank k has one central omission
run.  The marked terminals before and after that run are exactly the first
and remaining marked terminals.
-/
theorem template_central_shape_aux
    (t : List (Option α))
    (offset k : Nat)
    (hlo : offset ≤ k)
    (hhi : k ≤ offset + templateMarkedCount t)
    (hgap :
      ∀ j ∈ templateOmissionRanksAux offset t,
        j = k) :
    t =
      ((templateMarkedWord t).take (k - offset)).map Option.some ++
        List.replicate
          (templateOmissionCount t) Option.none ++
        ((templateMarkedWord t).drop (k - offset)).map Option.some := by
  induction t generalizing offset with
  | nil =>
      have hk : k = offset := by
        simp [templateMarkedCount] at hhi
        omega
      simp [templateMarkedWord, templateOmissionCount, hk]

  | cons x t ih =>
      cases x with
      | none =>
          have hk : offset = k :=
            hgap offset
              (by
                simp [templateOmissionRanksAux])
          have htailGap :
              ∀ j ∈ templateOmissionRanksAux offset t,
                j = k := by
            intro j hj
            exact hgap j
              (by
                simp [templateOmissionRanksAux, hj])
          have htailHi :
              k ≤ offset + templateMarkedCount t := by
            simpa [templateMarkedCount] using hhi
          have htail :=
            ih offset (by omega) htailHi htailGap
          have htail' :
              t =
                List.replicate
                    (templateOmissionCount t) Option.none ++
                  (templateMarkedWord t).map Option.some := by
            simpa [hk] using htail
          rw [hk]
          simp only [templateMarkedWord,
            templateOmissionCount, Nat.sub_self,
            List.take_zero, List.map_nil,
            List.nil_append, List.drop_zero]
          have hrep :
              List.replicate
                  (1 + templateOmissionCount t)
                  (Option.none : Option α) =
                (Option.none : Option α) ::
                  List.replicate
                    (templateOmissionCount t)
                    (Option.none : Option α) := by
            rw [show
              1 + templateOmissionCount t =
                Nat.succ (templateOmissionCount t) by omega]
            rfl
          rw [hrep]
          exact
            congrArg
              (List.cons (Option.none : Option α))
              htail'

      | some a =>
          have htailGap :
              ∀ j ∈
                templateOmissionRanksAux (offset + 1) t,
                j = k := by
            intro j hj
            exact hgap j
              (by
                simpa [templateOmissionRanksAux] using hj)
          by_cases hk : offset = k
          · have hlt : k < offset + 1 := by
              omega
            obtain ⟨hzero, hshape⟩ :=
              template_no_omissions_of_gap_lt_offset
                t (offset + 1) k hlt htailGap
            simp [templateMarkedWord,
              templateOmissionCount, hk, hzero] at ⊢
            exact hshape
          · have hlo' : offset + 1 ≤ k := by
              omega
            have hhi' :
                k ≤ offset + 1 + templateMarkedCount t := by
              simpa [templateMarkedCount, Nat.add_assoc] using hhi
            have htail :=
              ih (offset + 1) hlo' hhi' htailGap
            have hdiff :
                k - offset =
                  Nat.succ (k - (offset + 1)) := by
              omega
            simp [templateMarkedWord,
              templateOmissionCount, hdiff] at ⊢
            rw [take_map_some, drop_map_some]
            simpa only [List.append_assoc] using htail

/--
Kernel-facing central-template theorem.

If every omitted sibling lies after exactly k marked leaves and k is within
the marked-leaf range, then the kernel template is a marked prefix, one run of
omission placeholders, and a marked suffix.
-/
theorem boundaryTemplate_central_shape
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (k : Nat)
    (hk :
      k ≤ MarkedBoundaryKernel.markedLeafCount K)
    (hgap :
      MarkedBoundaryKernel.AllOmissionsAt K k) :
    MarkedBoundaryKernel.boundaryTemplate K =
      ((MarkedBoundaryKernel.markedWord K).take k).map Option.some ++
        List.replicate
          (MarkedBoundaryKernel.omittedCount K) Option.none ++
        ((MarkedBoundaryKernel.markedWord K).drop k).map Option.some := by
  have hgapTemplate :
      ∀ j ∈ templateOmissionRanksAux 0
          (MarkedBoundaryKernel.boundaryTemplate K),
        j = k := by
    intro j hj
    apply hgap j
    unfold MarkedBoundaryKernel.omissionRanks
    rw [← boundaryTemplate_omissionRanksAux
      terminalRule binaryRule 0 K]
    exact hj
  have hshape :=
    template_central_shape_aux
      (MarkedBoundaryKernel.boundaryTemplate K)
      0 k
      (Nat.zero_le k)
      (by
        rw [boundaryTemplate_markedCount
          terminalRule binaryRule K]
        simpa using hk)
      hgapTemplate
  rw [boundaryTemplate_markedWord
    terminalRule binaryRule K] at hshape
  rw [boundaryTemplate_omissionCount
    terminalRule binaryRule K] at hshape
  simpa using hshape

/-- Concatenate two independent template expansions. -/
theorem boundaryExpansion_append
    {t₁ t₂ : List (Option α)}
    {b₁ b₂ : List (Word α)}
    {w₁ w₂ : Word α}
    (e₁ : BoundaryExpansion t₁ b₁ w₁)
    (e₂ : BoundaryExpansion t₂ b₂ w₂) :
    BoundaryExpansion
      (t₁ ++ t₂) (b₁ ++ b₂) (w₁ ++ w₂) := by
  induction e₁ with
  | nil =>
      simpa using e₂
  | @some a template blocks w tail ih =>
      simpa using BoundaryExpansion.some ih
  | @none template blocks w block tail ih =>
      change
        BoundaryExpansion
          (Option.none :: (template ++ t₂))
          (block :: (blocks ++ b₂))
          ((block ++ w) ++ w₂)
      simpa only [List.append_assoc] using
        BoundaryExpansion.none (block := block) ih

/-- A single omitted placeholder expands to its chosen block. -/
theorem boundaryExpansion_single_none
    (block : Word α) :
    BoundaryExpansion [Option.none] [block] block := by
  simpa using
    (BoundaryExpansion.none
      (block := block)
      (BoundaryExpansion.nil :
        BoundaryExpansion ([] : List (Option α))
          ([] : List (Word α)) ([] : Word α)))

/-- A word of marked terminals expands without replacement blocks. -/
theorem boundaryExpansion_markedWord
    (w : Word α) :
    BoundaryExpansion
      (w.map Option.some) [] w := by
  induction w with
  | nil =>
      exact BoundaryExpansion.nil
  | cons a w ih =>
      exact BoundaryExpansion.some ih

/-- A run of omission placeholders expands to the concatenation of its blocks. -/
theorem boundaryExpansion_omissionRun
    (blocks : List (Word α)) :
    BoundaryExpansion
      (List.replicate blocks.length Option.none)
      blocks
      (concatBlocks blocks) := by
  induction blocks with
  | nil =>
      exact BoundaryExpansion.nil
  | cons block blocks ih =>
      change
        BoundaryExpansion
          (Option.none ::
            List.replicate blocks.length Option.none)
          (block :: blocks)
          (block ++ concatBlocks blocks)
      exact BoundaryExpansion.none ih

/-- Canonical expansion with one central replacement gap. -/
theorem boundaryExpansion_central
    (p q : Word α)
    (blocks : List (Word α)) :
    BoundaryExpansion
      (p.map Option.some ++
        List.replicate blocks.length Option.none ++
        q.map Option.some)
      blocks
      (boundaryAssembly p q blocks) := by
  have eP :
      BoundaryExpansion
        (p.map Option.some) [] p :=
    boundaryExpansion_markedWord p
  have eM :
      BoundaryExpansion
        (List.replicate blocks.length Option.none)
        blocks (concatBlocks blocks) :=
    boundaryExpansion_omissionRun blocks
  have eQ :
      BoundaryExpansion
        (q.map Option.some) [] q :=
    boundaryExpansion_markedWord q
  have ePM :
      BoundaryExpansion
        (p.map Option.some ++
          List.replicate blocks.length Option.none)
        blocks
        (p ++ concatBlocks blocks) :=
    boundaryExpansion_append eP eM
  have ePMQ :
      BoundaryExpansion
        ((p.map Option.some ++
            List.replicate blocks.length Option.none) ++
          q.map Option.some)
        blocks
        ((p ++ concatBlocks blocks) ++ q) := by
    simpa using boundaryExpansion_append ePM eQ
  simpa [boundaryAssembly, List.append_assoc] using ePMQ

/-- For fixed template and replacement blocks, the expanded word is unique. -/
theorem boundaryExpansion_word_unique
    {template : List (Option α)}
    {blocks : List (Word α)}
    {w₁ w₂ : Word α}
    (e₁ : BoundaryExpansion template blocks w₁)
    (e₂ : BoundaryExpansion template blocks w₂) :
    w₁ = w₂ := by
  induction e₁ generalizing w₂ with
  | nil =>
      cases e₂
      rfl
  | @some a template blocks w tail ih =>
      cases e₂ with
      | some tail₂ =>
          exact
            congrArg (List.cons a)
              (ih tail₂)
  | @none template blocks w block tail ih =>
      cases e₂ with
      | none tail₂ =>
          exact
            congrArg (fun x => block ++ x)
              (ih tail₂)

/--
A gap-certified kernel expansion is exactly a boundary assembly of the marked
prefix, the ordered replacement blocks, and the marked suffix.
-/
theorem boundaryExpansion_eq_boundaryAssembly_of_allOmissionsAt
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (k : Nat)
    (hk :
      k ≤ MarkedBoundaryKernel.markedLeafCount K)
    (hgap :
      MarkedBoundaryKernel.AllOmissionsAt K k)
    (blocks : List (Word α))
    (w' : Word α)
    (hexpand :
      BoundaryExpansion
        (MarkedBoundaryKernel.boundaryTemplate K)
        blocks w')
    (hcount :
      blocks.length =
        MarkedBoundaryKernel.omittedCount K) :
    w' =
      boundaryAssembly
        ((MarkedBoundaryKernel.markedWord K).take k)
        ((MarkedBoundaryKernel.markedWord K).drop k)
        blocks := by
  have hshape :=
    boundaryTemplate_central_shape
      terminalRule binaryRule K k hk hgap
  rw [← hcount] at hshape
  rw [hshape] at hexpand
  exact
    boundaryExpansion_word_unique
      hexpand
      (boundaryExpansion_central
        ((MarkedBoundaryKernel.markedWord K).take k)
        ((MarkedBoundaryKernel.markedWord K).drop k)
        blocks)

/--
Every marked-boundary kernel admits a tau-short block expansion whenever every
nonterminal has a tau-short terminal yield.
-/
theorem exists_rebuilt_short_expansion
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A) :
    ∃ blocks : List (Word α),
      ∃ w : Word α,
        BoundaryExpansion
          (MarkedBoundaryKernel.boundaryTemplate K)
          blocks w
        ∧
        UntypedDerives terminalRule binaryRule A w
        ∧
        blocks.length =
          MarkedBoundaryKernel.omittedCount K
        ∧
        (∀ block ∈ blocks, block.length ≤ τ) := by
  induction K with
  | marked a hterm =>
      refine
        ⟨[], [a], ?_,
          UntypedDerives.terminal hterm,
          by simp [MarkedBoundaryKernel.omittedCount],
          ?_⟩
      · exact
          BoundaryExpansion.some
            (BoundaryExpansion.nil :
              BoundaryExpansion ([] : List (Option α))
                ([] : List (Word α)) ([] : Word α))
      · intro block hmem
        simp at hmem

  | @unaryLeft A B C hbin child siblingWord sibling ih =>
      obtain ⟨blocks, w, hexpand, dChild,
          hcount, hlen⟩ := ih
      obtain ⟨z, dZ, hz⟩ := hshort C
      refine
        ⟨blocks ++ [z], w ++ z, ?_,
          UntypedDerives.binary hbin dChild dZ,
          ?_, ?_⟩
      · exact
          boundaryExpansion_append
            hexpand
            (boundaryExpansion_single_none z)
      · simp only [List.length_append,
          List.length_singleton,
          MarkedBoundaryKernel.omittedCount]
        rw [hcount]
        omega
      · intro block hmem
        simp only [List.mem_append, List.mem_singleton] at hmem
        rcases hmem with hmem | hmem
        · exact hlen block hmem
        · subst block
          exact hz

  | @unaryRight A B C hbin siblingWord sibling child ih =>
      obtain ⟨blocks, w, hexpand, dChild,
          hcount, hlen⟩ := ih
      obtain ⟨y, dY, hy⟩ := hshort B
      refine
        ⟨y :: blocks, y ++ w, ?_,
          UntypedDerives.binary hbin dY dChild,
          ?_, ?_⟩
      · exact BoundaryExpansion.none hexpand
      · simp only [List.length_cons,
          MarkedBoundaryKernel.omittedCount]
        rw [hcount]
        omega
      · intro block hmem
        simp only [List.mem_cons] at hmem
        rcases hmem with hmem | hmem
        · subst block
          exact hy
        · exact hlen block hmem

  | branch hbin left right ihL ihR =>
      obtain ⟨blocksL, wL, hExpandL, dL,
          hCountL, hLenL⟩ := ihL
      obtain ⟨blocksR, wR, hExpandR, dR,
          hCountR, hLenR⟩ := ihR
      refine
        ⟨blocksL ++ blocksR, wL ++ wR, ?_,
          UntypedDerives.binary hbin dL dR,
          ?_, ?_⟩
      · exact
          boundaryExpansion_append
            hExpandL hExpandR
      · simp only [List.length_append,
          MarkedBoundaryKernel.omittedCount]
        rw [hCountL, hCountR]
      · intro block hmem
        simp only [List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact hLenL block hmem
        · exact hLenR block hmem

/--
Short replacement reconstruction in the canonical central boundary-assembly
form.
-/
theorem exists_rebuilt_short_boundaryAssembly
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (τ : Nat)
    (hshort :
      ∀ X : N,
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule X z
          ∧ z.length ≤ τ)
    {A : N}
    (K : MarkedBoundaryKernel terminalRule binaryRule A)
    (k : Nat)
    (hk :
      k ≤ MarkedBoundaryKernel.markedLeafCount K)
    (hgap :
      MarkedBoundaryKernel.AllOmissionsAt K k) :
    ∃ blocks : List (Word α),
      UntypedDerives terminalRule binaryRule A
        (boundaryAssembly
          ((MarkedBoundaryKernel.markedWord K).take k)
          ((MarkedBoundaryKernel.markedWord K).drop k)
          blocks)
      ∧
      blocks.length =
        MarkedBoundaryKernel.omittedCount K
      ∧
      (∀ block ∈ blocks, block.length ≤ τ) := by
  obtain ⟨blocks, w', hexpand, d', hcount, hlen⟩ :=
    exists_rebuilt_short_expansion
      terminalRule binaryRule τ hshort K
  have hw :
      w' =
        boundaryAssembly
          ((MarkedBoundaryKernel.markedWord K).take k)
          ((MarkedBoundaryKernel.markedWord K).drop k)
          blocks :=
    boundaryExpansion_eq_boundaryAssembly_of_allOmissionsAt
      terminalRule binaryRule K k hk hgap
      blocks w' hexpand hcount
  refine ⟨blocks, ?_, hcount, hlen⟩
  simpa [hw] using d'


end MarkedBoundaryExpansion

end TCS1
end LeanCfgProject
