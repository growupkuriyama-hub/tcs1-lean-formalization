import LeanCfgProject.TCS1.LinearSpineBounds
import LeanCfgProject.TCS1.FixedWindowContextSemantic

/-!
# TCS #1: semantics of linear-spine SSBNF derivations

This file formalizes the semantic part of Appendix
"Proof of the short canonical-witness lemma".

A linear-spine SSBNF grammar has a distinguished class of fresh terminal
wrappers. Every wrapper has a terminal rule, no wrapper can head a binary
rule, and every binary rule has exactly one wrapper child. Thus every
non-wrapper derivation has one continuing spine.

We prove two facts used by the manuscript:

* every productive symbol has an alternative terminal yield of length at most
  the number of non-start typed symbols;
* every structural reaching spine can be shortened and its off-spine siblings
  replaced so that the resulting terminal context has length at most twice
  that number.

The statements are generic in the finite typed-symbol set. The next bridge
instantiates them with the active reduced yield-typed refinement.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section LinearSpineSemantic

variable {T : Type u}
variable {α : Type v}

/-- Structural single-spine condition for an SSBNF grammar. -/
structure LinearSpineShape
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop) : Prop where
  wrapper_terminal :
    ∀ X, Wrapper X → ∃ a, terminalRule X a
  wrapper_no_binary :
    ∀ {X B C}, Wrapper X → binaryRule X B C → False
  binary_children :
    ∀ {A B C}, binaryRule A B C →
      (Wrapper B ∧ ¬ Wrapper C) ∨
      (¬ Wrapper B ∧ Wrapper C)

/--
A productive derivation with the unique continuing linear spine exposed.

Every binary step stores only a one-symbol derivation of the wrapper sibling;
the other child continues the spine.
-/
inductive LinearYieldSpine
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop) :
    T → Word α → List T → Prop
  | terminal
      {A : T} {a : α}
      (hterm : terminalRule A a) :
      LinearYieldSpine terminalRule binaryRule A [a] [A]
  | binaryLeft
      {A B C : T}
      {a : α}
      {word : Word α}
      {path : List T}
      (hbin : binaryRule A B C)
      (child :
        LinearYieldSpine terminalRule binaryRule
          B word path)
      (hsibling : terminalRule C a) :
      LinearYieldSpine terminalRule binaryRule
        A (word ++ [a]) (A :: path)
  | binaryRight
      {A B C : T}
      {a : α}
      {word : Word α}
      {path : List T}
      (hbin : binaryRule A B C)
      (hsibling : terminalRule B a)
      (child :
        LinearYieldSpine terminalRule binaryRule
          C word path) :
      LinearYieldSpine terminalRule binaryRule
        A ([a] ++ word) (A :: path)

/-- Forgetting the exposed spine gives an ordinary SSBNF derivation. -/
theorem linearYieldSpine_to_derives
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A : T} {word : Word α} {path : List T}
    (d : LinearYieldSpine terminalRule binaryRule A word path) :
    UntypedDerives terminalRule binaryRule A word := by
  induction d with
  | terminal hterm =>
      exact UntypedDerives.terminal hterm
  | binaryLeft hbin child hsibling ih =>
      exact
        UntypedDerives.binary
          hbin ih (UntypedDerives.terminal hsibling)
  | binaryRight hbin hsibling child ih =>
      exact
        UntypedDerives.binary
          hbin (UntypedDerives.terminal hsibling) ih

/-- In a linear-spine derivation, one terminal is emitted per spine symbol. -/
theorem linearYieldSpine_length_eq_path
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A : T} {word : Word α} {path : List T}
    (d : LinearYieldSpine terminalRule binaryRule A word path) :
    word.length = path.length := by
  induction d with
  | terminal hterm =>
      simp
  | binaryLeft hbin child hsibling ih =>
      simpa [List.length_append, ih, Nat.add_comm]
  | binaryRight hbin hsibling child ih =>
      simpa [List.length_append, ih, Nat.add_comm]

/--
A suffix beginning at any symbol on a repetition-free linear yield spine is
again a repetition-free linear yield spine.
-/
theorem linearYieldSubspine_of_mem_of_nodup
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A X : T}
    {word : Word α} {path : List T}
    (d : LinearYieldSpine terminalRule binaryRule A word path)
    (hnodup : path.Nodup)
    (hmem : X ∈ path) :
    ∃ word' path',
      LinearYieldSpine terminalRule binaryRule X word' path'
      ∧ path'.Nodup := by
  induction d generalizing X with
  | @terminal A a hterm =>
      simp only [List.mem_singleton] at hmem
      subst X
      exact
        ⟨[a], [A],
          LinearYieldSpine.terminal hterm,
          by simp⟩
  | @binaryLeft A B C a word path hbin child hsibling ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hXA | htail
      · subst X
        exact
          ⟨word ++ [a], A :: path,
            LinearYieldSpine.binaryLeft hbin child hsibling,
            (by rw [List.nodup_cons]; exact hnodup)⟩
      · exact ih hnodup.2 htail
  | @binaryRight A B C a word path hbin hsibling child ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hXA | htail
      · subst X
        exact
          ⟨[a] ++ word, A :: path,
            LinearYieldSpine.binaryRight hbin hsibling child,
            (by rw [List.nodup_cons]; exact hnodup)⟩
      · exact ih hnodup.2 htail

/--
Delete repeated spine segments. The resulting derivation has the same root,
a repetition-free spine, and one emitted terminal per remaining spine symbol.
-/
theorem normalize_linearYieldSpine_to_nodup
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A : T}
    {word : Word α} {path : List T}
    (d : LinearYieldSpine terminalRule binaryRule A word path) :
    ∃ word' path',
      LinearYieldSpine terminalRule binaryRule A word' path'
      ∧ path'.Nodup := by
  induction d with
  | @terminal A a hterm =>
      exact
        ⟨[a], [A],
          LinearYieldSpine.terminal hterm,
          by simp⟩
  | @binaryLeft A B C a word path hbin child hsibling ih =>
      obtain ⟨word', path', child', hnodup⟩ := ih
      by_cases hmem : A ∈ path'
      · exact
          linearYieldSubspine_of_mem_of_nodup
            terminalRule binaryRule child' hnodup hmem
      · exact
          ⟨word' ++ [a], A :: path',
            LinearYieldSpine.binaryLeft hbin child' hsibling,
            (by rw [List.nodup_cons]; exact ⟨hmem, hnodup⟩)⟩
  | @binaryRight A B C a word path hbin hsibling child ih =>
      obtain ⟨word', path', child', hnodup⟩ := ih
      by_cases hmem : A ∈ path'
      · exact
          linearYieldSubspine_of_mem_of_nodup
            terminalRule binaryRule child' hnodup hmem
      · exact
          ⟨[a] ++ word', A :: path',
            LinearYieldSpine.binaryRight hbin hsibling child',
            (by rw [List.nodup_cons]; exact ⟨hmem, hnodup⟩)⟩

/--
Every derivation rooted at a non-wrapper symbol can be replaced by a derivation
that exposes the unique linear spine and uses one terminal at every wrapper
sibling.
-/
theorem exists_linearYieldSpine_of_nonwrapper_derives
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    {A : T} {word : Word α}
    (hA : ¬ Wrapper A)
    (d : UntypedDerives terminalRule binaryRule A word) :
    ∃ word' path,
      LinearYieldSpine terminalRule binaryRule A word' path := by
  induction d with
  | @terminal A a hterm =>
      exact
        ⟨[a], [A],
          LinearYieldSpine.terminal hterm⟩
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      rcases shape.binary_children hbin with
        ⟨hBW, hCnW⟩ | ⟨hBnW, hCW⟩
      · obtain ⟨a, ha⟩ :=
          shape.wrapper_terminal B hBW
        obtain ⟨word', path, child⟩ :=
          ihC hCnW
        exact
          ⟨[a] ++ word', A :: path,
            LinearYieldSpine.binaryRight
              hbin ha child⟩
      · obtain ⟨a, ha⟩ :=
          shape.wrapper_terminal C hCW
        obtain ⟨word', path, child⟩ :=
          ihB hBnW
        exact
          ⟨word' ++ [a], A :: path,
            LinearYieldSpine.binaryLeft
              hbin child ha⟩

/--
Every productive symbol in a finite linear-spine grammar admits a terminal
yield of length at most the number of symbols.
-/
theorem exists_linear_short_yield
    [Fintype T] [DecidableEq T]
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    {A : T} {word : Word α}
    (d : UntypedDerives terminalRule binaryRule A word) :
    ∃ word' : Word α,
      UntypedDerives terminalRule binaryRule A word'
      ∧ word'.length ≤ Fintype.card T := by
  by_cases hA : Wrapper A
  · obtain ⟨a, ha⟩ :=
      shape.wrapper_terminal A hA
    have hcard : 1 ≤ Fintype.card T := by
      letI : Nonempty T := ⟨A⟩
      exact Fintype.card_pos
    exact
      ⟨[a], UntypedDerives.terminal ha, by simpa using hcard⟩
  · obtain ⟨word₀, path₀, spine₀⟩ :=
      exists_linearYieldSpine_of_nonwrapper_derives
        terminalRule binaryRule Wrapper shape hA d
    obtain ⟨word₁, path₁, spine₁, hnodup⟩ :=
      normalize_linearYieldSpine_to_nodup
        terminalRule binaryRule spine₀
    have hpath :
        path₁.length ≤ Fintype.card T :=
      nodup_path_length_le_card path₁ hnodup
    have hlen :
        word₁.length = path₁.length :=
      linearYieldSpine_length_eq_path
        terminalRule binaryRule spine₁
    exact
      ⟨word₁,
        linearYieldSpine_to_derives
          terminalRule binaryRule spine₁,
        by omega⟩

/--
A reaching spine rooted at a wrapper cannot take a binary step; it is the
zero-step hole spine.
-/
theorem reachingSpine_of_wrapper_root_is_hole
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    {A X : T}
    {left right : Word α}
    {path : List T} {siblings : List Nat}
    (hA : Wrapper A)
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings) :
    A = X ∧ left = [] ∧ right = [] ∧
      path = [A] ∧ siblings = [] := by
  cases spine with
  | hole =>
      simp
  | @binaryLeft A B C X left right z path siblings
      hbin child sibling =>
      exact False.elim
        (shape.wrapper_no_binary hA hbin)
  | @binaryRight A B C X left right y path siblings
      hbin sibling child =>
      exact False.elim
        (shape.wrapper_no_binary hA hbin)

/--
Replace siblings along a reaching spine according to the linear shape.

All ordinary spine steps receive a one-terminal wrapper sibling. If the target
itself is a wrapper, only the final step may instead have a non-wrapper
sibling, and that sibling is replaced by a yield of length at most |T|.

The two numerical conclusions encode exactly this "at most one exceptional
sibling" fact.
-/
theorem linearReachingSpine_replace_siblings
    [Fintype T]
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    (hshort :
      ∀ (Y : T) {z₀ : Word α},
        ¬ Wrapper Y →
        UntypedDerives terminalRule binaryRule Y z₀ →
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule Y z
          ∧ z.length ≤ Fintype.card T)
    {A X : T}
    {left right : Word α}
    {path : List T} {siblings : List Nat}
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings) :
    ∃ left' right' siblings',
      ReachingSpine terminalRule binaryRule
        A X left' right' path siblings'
      ∧
      (Wrapper X →
        siblings'.sum ≤ siblings'.length + Fintype.card T)
      ∧
      (¬ Wrapper X →
        siblings'.sum ≤ siblings'.length) := by
  induction spine with
  | @hole A =>
      exact
        ⟨[], [], [],
          ReachingSpine.hole,
          (by intro h; simp),
          (by intro h; simp)⟩
  | @binaryLeft A B C X left right z path siblings
      hbin child sibling ih =>
      rcases shape.binary_children hbin with
        ⟨hBW, hCnW⟩ | ⟨hBnW, hCW⟩
      · have hhole :=
          reachingSpine_of_wrapper_root_is_hole
            terminalRule binaryRule Wrapper shape
            hBW child
        rcases hhole with
          ⟨hBX, hleft, hright, hpath, hsiblings⟩
        subst X
        subst left
        subst right
        subst path
        subst siblings
        obtain ⟨z', dz', hz'⟩ :=
          hshort C hCnW sibling
        refine
          ⟨[], z', [z'.length],
            ReachingSpine.binaryLeft
              hbin ReachingSpine.hole dz',
            ?_, ?_⟩
        · intro h
          simp
          omega
        · intro h
          exact False.elim (h hBW)
      · obtain ⟨a, ha⟩ :=
          shape.wrapper_terminal C hCW
        obtain ⟨left', right', siblings',
            child', hwrap, hnonwrap⟩ := ih
        refine
          ⟨left', right' ++ [a], 1 :: siblings',
            ReachingSpine.binaryLeft
              hbin child' (UntypedDerives.terminal ha),
            ?_, ?_⟩
        · intro hX
          have h := hwrap hX
          simp only [List.sum_cons, List.length_cons]
          omega
        · intro hX
          have h := hnonwrap hX
          simp only [List.sum_cons, List.length_cons]
          omega
  | @binaryRight A B C X left right y path siblings
      hbin sibling child ih =>
      rcases shape.binary_children hbin with
        ⟨hBW, hCnW⟩ | ⟨hBnW, hCW⟩
      · obtain ⟨a, ha⟩ :=
          shape.wrapper_terminal B hBW
        obtain ⟨left', right', siblings',
            child', hwrap, hnonwrap⟩ := ih
        refine
          ⟨[a] ++ left', right', 1 :: siblings',
            ReachingSpine.binaryRight
              hbin (UntypedDerives.terminal ha) child',
            ?_, ?_⟩
        · intro hX
          have h := hwrap hX
          simp only [List.sum_cons, List.length_cons]
          omega
        · intro hX
          have h := hnonwrap hX
          simp only [List.sum_cons, List.length_cons]
          omega
      · have hhole :=
          reachingSpine_of_wrapper_root_is_hole
            terminalRule binaryRule Wrapper shape
            hCW child
        rcases hhole with
          ⟨hCX, hleft, hright, hpath, hsiblings⟩
        subst X
        subst left
        subst right
        subst path
        subst siblings
        obtain ⟨y', dy', hy'⟩ :=
          hshort B hBnW sibling
        refine
          ⟨y', [], [y'.length],
            (by
              simpa using
                (ReachingSpine.binaryRight
                  hbin dy' ReachingSpine.hole)),
            ?_, ?_⟩
        · intro h
          simp
          omega
        · intro h
          exact False.elim (h hCW)

/--
Any reaching spine in a finite linear-spine grammar admits a repetition-free
replacement context of total terminal length at most 2|T|.
-/
theorem linearReachingSpine_short_context
    [Fintype T] [DecidableEq T]
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    (hshort :
      ∀ (Y : T) {z₀ : Word α},
        ¬ Wrapper Y →
        UntypedDerives terminalRule binaryRule Y z₀ →
        ∃ z : Word α,
          UntypedDerives terminalRule binaryRule Y z
          ∧ z.length ≤ Fintype.card T)
    {A X : T}
    {left right : Word α}
    {path : List T} {siblings : List Nat}
    (spine :
      ReachingSpine terminalRule binaryRule
        A X left right path siblings) :
    ∃ left' right' path' siblings',
      ReachingSpine terminalRule binaryRule
        A X left' right' path' siblings'
      ∧ path'.Nodup
      ∧ left'.length + right'.length ≤
          2 * Fintype.card T := by
  obtain ⟨left₀, right₀, path₀, siblings₀,
      spine₀, hnodup⟩ :=
    normalize_reachingSpine_to_nodup_unbounded
      terminalRule binaryRule spine
  obtain ⟨left₁, right₁, siblings₁,
      spine₁, hwrap, hnonwrap⟩ :=
    linearReachingSpine_replace_siblings
      terminalRule binaryRule Wrapper shape hshort spine₀
  have hpath :
      path₀.length ≤ Fintype.card T :=
    nodup_path_length_le_card path₀ hnodup
  have hsibPath :
      siblings₁.length + 1 = path₀.length :=
    reachingSpine_siblings_length_add_one_eq_path
      terminalRule binaryRule spine₁
  have hctx :
      left₁.length + right₁.length = siblings₁.sum :=
    reachingSpine_context_length_eq
      terminalRule binaryRule spine₁
  have hsum :
      siblings₁.sum ≤ 2 * Fintype.card T := by
    by_cases hX : Wrapper X
    · have h := hwrap hX
      omega
    · have h := hnonwrap hX
      omega
  exact
    ⟨left₁, right₁, path₀, siblings₁,
      spine₁, hnodup, by omega⟩

end LinearSpineSemantic

end TCS1
end LeanCfgProject
