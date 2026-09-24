import LeanCfgProject.TCS1.ShortestNonemptySpineSemantic

/-!
# TCS #1 v66: finite-support shortest-nonempty-yield bound

The semantic front-end grammar is intentionally generous: its ambient state
type contains every possible terminal wrapper and every possible suffix list.
Only finitely many of those states are created by a finite source grammar.

This module separates those two issues.  A finite support records the states
actually used by the grammar.  If unit and binary rules starting in the
support keep their children inside it, then every distinguished derivation
spine rooted in the support stays inside that finite set.  Consequently the
cycle-shortening argument needs the cardinality of the finite support, not a
Fintype instance on the whole ambient state type.

This is the bridge needed to use the convenient infinite semantic model while
recovering the manuscript's finite |V_B| bound.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section FiniteSupportSpineBound

variable {N : Type u}
variable {α : Type v}

/-- Uniform terminal-yield bound restricted to a finite support. -/
def YieldBoundOn
    [DecidableEq N]
    (L : NTLang N α)
    (support : Finset N)
    (b : Nat) : Prop :=
  ∀ A, A ∈ support →
    ∃ w, w ∈ L A ∧ w.length ≤ b

/-- Shortest-nonempty-yield bound restricted to a finite support. -/
def NonemptyYieldBoundOn
    [DecidableEq N]
    (L : NTLang N α)
    (support : Finset N)
    (b : Nat) : Prop :=
  ∀ A, A ∈ support →
    (∃ w, w ∈ L A ∧ w ≠ []) →
    ∃ w, w ∈ L A ∧ w ≠ [] ∧ w.length ≤ b

/--
Closure condition saying that every child reached by a unit or binary rule
from a supported state is supported as well.
-/
structure BinaryGrammarSupportedOn
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N) : Prop where
  unitChild :
    ∀ {A B}, A ∈ support →
      G.unitRule A B →
      B ∈ support
  binaryChildren :
    ∀ {A B C}, A ∈ support →
      G.binaryRule A B C →
      B ∈ support ∧ C ∈ support

/--
Every label on a distinguished spine rooted in the finite support remains in
that support.
-/
theorem nonemptySpine_path_mem_support
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (hclosed : BinaryGrammarSupportedOn G support)
    {A : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (hA : A ∈ support)
    (d : NonemptySpineDerives G A w path siblings) :
    ∀ X ∈ path, X ∈ support := by
  induction d with
  | @terminal A a h =>
      intro X hX
      simp only [List.mem_singleton] at hX
      simpa [hX] using hA
  | @unit A B w path siblings h d ih =>
      have hB : B ∈ support :=
        hclosed.unitChild hA h
      intro X hX
      simp only [List.mem_cons] at hX
      rcases hX with hXA | hXtail
      · simpa [hXA] using hA
      · exact ih hB X hXtail
  | @binaryLeft A B C wB wC path siblings h dB dC ih =>
      have hBC := hclosed.binaryChildren hA h
      intro X hX
      simp only [List.mem_cons] at hX
      rcases hX with hXA | hXtail
      · simpa [hXA] using hA
      · exact ih hBC.1 X hXtail
  | @binaryRight A B C wB wC path siblings h dB dC ih =>
      have hBC := hclosed.binaryChildren hA h
      intro X hX
      simp only [List.mem_cons] at hX
      rcases hX with hXA | hXtail
      · simpa [hXA] using hA
      · exact ih hBC.2 X hXtail

/-- A repetition-free path contained in a finite support is no longer than it. -/
theorem nodup_path_length_le_support_card
    [DecidableEq N]
    (support : Finset N)
    (path : List N)
    (hnodup : path.Nodup)
    (hmem : ∀ X ∈ path, X ∈ support) :
    path.length ≤ support.card := by
  have hsubset : path.toFinset ⊆ support := by
    intro X hX
    have hXlist : X ∈ path := by
      simpa using hX
    exact hmem X hXlist
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hnodup] at hcard
  exact hcard

/--
Finite-support version of the off-spine sibling bound.
-/
theorem sibling_replacement_sum_le_support
    [DecidableEq N]
    (support : Finset N)
    (path : List N)
    (siblings : List Nat)
    (τB : Nat)
    (hnodup : path.Nodup)
    (hmem : ∀ X ∈ path, X ∈ support)
    (hindex : siblings.length ≤ path.length)
    (heach : ∀ s ∈ siblings, s ≤ τB) :
    siblings.sum ≤ support.card * τB := by
  have hpath :
      path.length ≤ support.card :=
    nodup_path_length_le_support_card
      support path hnodup hmem
  exact chainExpansion_sum_le
    siblings support.card τB
    (le_trans hindex hpath) heach

/--
The chosen terminal leaf contributes one symbol, giving
1 + |support| * tau_B.
-/
theorem shortened_path_nonempty_yield_bound_support
    [DecidableEq N]
    (support : Finset N)
    (path : List N)
    (siblings : List Nat)
    (τB : Nat)
    (hnodup : path.Nodup)
    (hmem : ∀ X ∈ path, X ∈ support)
    (hindex : siblings.length ≤ path.length)
    (heach : ∀ s ∈ siblings, s ≤ τB) :
    1 + siblings.sum ≤ 1 + support.card * τB := by
  exact Nat.add_le_add_left
    (sibling_replacement_sum_le_support
      support path siblings τB
      hnodup hmem hindex heach)
    1

/--
Local version of boundedSpine_of_nonemptyDerivation.  Only supported states
need short witnesses; support closure supplies the induction hypotheses for
children.
-/
theorem boundedSpine_of_nonemptyDerivation_on_support
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (τB : Nat)
    (hclosed : BinaryGrammarSupportedOn G support)
    (hshort :
      YieldBoundOn
        (fun A => {w | BinaryNullableDerives G A w})
        support τB)
    {A : N} {w : List α}
    (hA : A ∈ support)
    (d : BinaryNullableDerives G A w)
    (hne : w ≠ []) :
    ∃ w' path siblings,
      NonemptySpineDerives G A w' path siblings
      ∧ (∀ s ∈ siblings, s ≤ τB) := by
  induction d with
  | @terminal A a h =>
      exact
        ⟨[a], [A], [],
          NonemptySpineDerives.terminal h,
          by simp⟩
  | @epsilon A h =>
      exact False.elim (hne rfl)
  | @unit A B w h d ih =>
      have hB : B ∈ support :=
        hclosed.unitChild hA h
      obtain ⟨w', path, siblings, hspine, hsib⟩ :=
        ih hB hne
      exact
        ⟨w', A :: path, siblings,
          NonemptySpineDerives.unit h hspine,
          hsib⟩
  | @binary A B C wB wC h dB dC ihB ihC =>
      have hBC := hclosed.binaryChildren hA h
      by_cases hBword : wB = []
      · subst wB
        have hCword : wC ≠ [] := by
          simpa using hne
        obtain ⟨w', path, siblings, hspine, hsib⟩ :=
          ihC hBC.2 hCword
        obtain ⟨u, hu, hlenU⟩ :=
          hshort B hBC.1
        refine
          ⟨u ++ w', A :: path, u.length :: siblings,
            NonemptySpineDerives.binaryRight h hu hspine,
            ?_⟩
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hlenU
        · exact hsib s hs
      · obtain ⟨w', path, siblings, hspine, hsib⟩ :=
          ihB hBC.1 hBword
        obtain ⟨v, hv, hlenV⟩ :=
          hshort C hBC.2
        refine
          ⟨w' ++ v, A :: path, v.length :: siblings,
            NonemptySpineDerives.binaryLeft h hspine hv,
            ?_⟩
        intro s hs
        simp only [List.mem_cons] at hs
        rcases hs with rfl | hs
        · exact hlenV
        · exact hsib s hs

/--
Finite-support version of the Appendix A shortest-nonempty-yield theorem.
The ambient state type may be infinite.
-/
theorem nonemptyYieldBoundOn_of_yieldBoundOn
    [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (support : Finset N)
    (τB : Nat)
    (hclosed : BinaryGrammarSupportedOn G support)
    (hshort :
      YieldBoundOn
        (fun A => {w | BinaryNullableDerives G A w})
        support τB) :
    NonemptyYieldBoundOn
      (fun A => {w | BinaryNullableDerives G A w})
      support
      (1 + support.card * τB) := by
  intro A hA hExists
  obtain ⟨w, hw, hne⟩ := hExists
  obtain ⟨w₀, path₀, siblings₀, hspine₀, hsib₀⟩ :=
    boundedSpine_of_nonemptyDerivation_on_support
      G support τB hclosed hshort hA hw hne
  obtain ⟨w₁, path₁, siblings₁, hspine₁, hnodup, hsib₁⟩ :=
    normalize_boundedSpine_to_nodup
      G τB hspine₀ hsib₀
  have hpathmem :
      ∀ X ∈ path₁, X ∈ support :=
    nonemptySpine_path_mem_support
      G support hclosed hA hspine₁
  have hindex :
      siblings₁.length ≤ path₁.length :=
    nonemptySpine_siblings_length_le_path
      G hspine₁
  have hbound :
      1 + siblings₁.sum ≤
        1 + support.card * τB :=
    shortened_path_nonempty_yield_bound_support
      support path₁ siblings₁ τB
      hnodup hpathmem hindex hsib₁
  have hlen :
      w₁.length = 1 + siblings₁.sum :=
    nonemptySpine_length_eq G hspine₁
  refine
    ⟨w₁,
      nonemptySpine_to_derives G hspine₁,
      nonemptySpine_word_ne_nil G hspine₁,
      ?_⟩
  rw [hlen]
  exact hbound

end FiniteSupportSpineBound

end TCS1
end LeanCfgProject
