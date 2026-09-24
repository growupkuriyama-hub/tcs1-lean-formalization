import LeanCfgProject.TCS1.BinaryEpsilonElimination
import LeanCfgProject.TCS1.ShortestNonemptyPathBound

/-!
# TCS #1 v66: semantic spine kernel for the shortest nonempty yield bound

Appendix A bounds the shortest nonempty yield of a nullable symbol by choosing
one terminal leaf, following a root-to-leaf spine, shortcutting repeated
nonterminal labels, and replacing every off-spine sibling by a shortest
terminal yield.

This module formalizes the semantic part of that argument. A
NonemptySpineDerives object records the selected terminal spine together
with the lengths of the off-spine sibling yields. It proves:

* every such spine is a genuine derivation;
* its derived word is nonempty;
* its length is exactly one plus the sum of sibling lengths;
* every nonempty derivation can be converted to a spine whose siblings use a
  supplied uniform short-yield bound; and
* once the spine has no repeated nonterminal labels, the manuscript bound
  1 + |V_B| * tau_B follows from ShortestNonemptyPathBound.

The remaining cycle-shortcut obligation is therefore isolated precisely as
existence of a NodupBoundedSpineProperty; no yield-length arithmetic remains
hidden in that step.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ShortestNonemptySpineSemantic

variable {N : Type u}
variable {α : Type v}

/--
A successful derivation with one distinguished terminal-leaf spine.

The list path records nonterminal labels on the distinguished path, including
the root and terminal parent. The list siblings records the terminal-yield
length of one off-path sibling for every binary node on that spine.
-/
inductive NonemptySpineDerives
    (G : BinaryNullableGrammar N α) :
    N → List α → List N → List Nat → Prop
  | terminal
      {A : N} {a : α}
      (h : G.terminalRule A a) :
      NonemptySpineDerives G A [a] [A] []
  | unit
      {A B : N} {w : List α}
      {path : List N} {siblings : List Nat}
      (h : G.unitRule A B)
      (d : NonemptySpineDerives G B w path siblings) :
      NonemptySpineDerives G A w (A :: path) siblings
  | binaryLeft
      {A B C : N} {wB wC : List α}
      {path : List N} {siblings : List Nat}
      (h : G.binaryRule A B C)
      (dB : NonemptySpineDerives G B wB path siblings)
      (dC : BinaryNullableDerives G C wC) :
      NonemptySpineDerives G A (wB ++ wC)
        (A :: path) (wC.length :: siblings)
  | binaryRight
      {A B C : N} {wB wC : List α}
      {path : List N} {siblings : List Nat}
      (h : G.binaryRule A B C)
      (dB : BinaryNullableDerives G B wB)
      (dC : NonemptySpineDerives G C wC path siblings) :
      NonemptySpineDerives G A (wB ++ wC)
        (A :: path) (wB.length :: siblings)

/-- Forgetting the distinguished spine gives an ordinary derivation. -/
theorem nonemptySpine_to_derives
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (d : NonemptySpineDerives G A w path siblings) :
    BinaryNullableDerives G A w := by
  induction d with
  | terminal h =>
      exact BinaryNullableDerives.terminal h
  | unit h _ ih =>
      exact BinaryNullableDerives.unit h ih
  | binaryLeft h _ dC ih =>
      exact BinaryNullableDerives.binary h ih dC
  | binaryRight h dB _ ih =>
      exact BinaryNullableDerives.binary h dB ih

/-- The distinguished terminal leaf guarantees a nonempty total yield. -/
theorem nonemptySpine_word_ne_nil
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (d : NonemptySpineDerives G A w path siblings) :
    w ≠ [] := by
  induction d with
  | terminal _ =>
      simp
  | unit _ _ ih =>
      exact ih
  | binaryLeft _ _ _ ih =>
      exact append_ne_nil_of_left_ne_nil ih
  | binaryRight _ _ _ ih =>
      exact List.append_ne_nil_of_right_ne_nil _ ih

/--
The selected terminal contributes exactly one symbol and every binary spine
node contributes exactly its recorded off-path sibling yield.
-/
theorem nonemptySpine_length_eq
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (d : NonemptySpineDerives G A w path siblings) :
    w.length = 1 + siblings.sum := by
  induction d with
  | terminal _ =>
      simp
  | unit _ _ ih =>
      exact ih
  | binaryLeft _ _ _ ih =>
      simp only [List.length_append, List.sum_cons]
      omega
  | binaryRight _ _ _ ih =>
      simp only [List.length_append, List.sum_cons]
      omega

/--
There can be no more recorded binary siblings than nonterminal occurrences on
the distinguished path.
-/
theorem nonemptySpine_siblings_length_le_path
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (d : NonemptySpineDerives G A w path siblings) :
    siblings.length ≤ path.length := by
  induction d with
  | terminal _ =>
      simp
  | unit _ _ ih =>
      simp only [List.length_cons]
      omega
  | binaryLeft _ _ _ ih =>
      simp only [List.length_cons]
      exact Nat.succ_le_succ ih
  | binaryRight _ _ _ ih =>
      simp only [List.length_cons]
      exact Nat.succ_le_succ ih

/--
Every nonempty derivation admits a distinguished spine whose off-path siblings
have been replaced by witnesses from a supplied uniform yield bound.

The path produced here may still repeat labels; that is exactly the separate
cycle-shortcut step of Appendix A.
-/
theorem boundedSpine_of_nonemptyDerivation
    (G : BinaryNullableGrammar N α)
    (τB : Nat)
    (hshort :
      YieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        τB)
    {A : N} {w : List α}
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
      obtain ⟨w', path, siblings, hspine, hsib⟩ :=
        ih hne
      exact
        ⟨w', A :: path, siblings,
          NonemptySpineDerives.unit h hspine,
          hsib⟩

  | @binary A B C wB wC h dB dC ihB ihC =>
      by_cases hB : wB = []
      · subst wB
        have hC : wC ≠ [] := by
          simpa using hne
        obtain ⟨w', path, siblings, hspine, hsib⟩ :=
          ihC hC
        obtain ⟨u, hu, hlenU⟩ := hshort B
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
          ihB hB
        obtain ⟨v, hv, hlenV⟩ := hshort C
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
If a nonterminal label occurs on a repetition-free distinguished spine, the
subspine beginning at that occurrence is itself a valid repetition-free
spine. Bounds on recorded off-path siblings are inherited.
-/
theorem subspine_of_mem_of_nodup
    (G : BinaryNullableGrammar N α)
    (τB : Nat)
    {A X : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (d : NonemptySpineDerives G A w path siblings)
    (hnodup : path.Nodup)
    (hsib : ∀ s ∈ siblings, s ≤ τB)
    (hmem : X ∈ path) :
    ∃ w' path' siblings',
      NonemptySpineDerives G X w' path' siblings'
      ∧ path'.Nodup
      ∧ (∀ s ∈ siblings', s ≤ τB) := by
  induction d generalizing X with
  | @terminal A a h =>
      simp only [List.mem_singleton] at hmem
      subst X
      exact
        ⟨[a], [A], [],
          NonemptySpineDerives.terminal h,
          by simp,
          by simp⟩
  | @unit A B w path siblings h d ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      rcases hmem with hXA | hXtail
      · subst X
        exact
          ⟨w, A :: path, siblings,
            NonemptySpineDerives.unit h d,
            (by rw [List.nodup_cons]; exact hnodup),
            hsib⟩
      · exact ih hnodup.2 hsib hXtail
  | @binaryLeft A B C wB wC path siblings h dB dC ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      have hsibTail : ∀ s ∈ siblings, s ≤ τB := by
        intro s hs
        exact hsib s (List.mem_cons_of_mem _ hs)
      rcases hmem with hXA | hXtail
      · subst X
        exact
          ⟨wB ++ wC, A :: path, wC.length :: siblings,
            NonemptySpineDerives.binaryLeft h dB dC,
            (by rw [List.nodup_cons]; exact hnodup),
            hsib⟩
      · exact ih hnodup.2 hsibTail hXtail
  | @binaryRight A B C wB wC path siblings h dB dC ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.mem_cons] at hmem
      have hsibTail : ∀ s ∈ siblings, s ≤ τB := by
        intro s hs
        exact hsib s (List.mem_cons_of_mem _ hs)
      rcases hmem with hXA | hXtail
      · subst X
        exact
          ⟨wB ++ wC, A :: path, wB.length :: siblings,
            NonemptySpineDerives.binaryRight h dB dC,
            (by rw [List.nodup_cons]; exact hnodup),
            hsib⟩
      · exact ih hnodup.2 hsibTail hXtail

/--
Cycle-shortening normalization for a bounded distinguished spine.

The recursive child spine is normalized first. If the current root label
already occurs in that normalized child path, the derivation jumps directly
to that lower occurrence; otherwise the current rule is reattached. This is
the formal version of the manuscript's "shortcut repeated nonterminal labels"
argument.
-/
theorem normalize_boundedSpine_to_nodup
    (G : BinaryNullableGrammar N α)
    (τB : Nat)
    {A : N} {w : List α}
    {path : List N} {siblings : List Nat}
    (d : NonemptySpineDerives G A w path siblings)
    (hsib : ∀ s ∈ siblings, s ≤ τB) :
    ∃ w' path' siblings',
      NonemptySpineDerives G A w' path' siblings'
      ∧ path'.Nodup
      ∧ (∀ s ∈ siblings', s ≤ τB) := by
  induction d with
  | @terminal A a h =>
      exact
        ⟨[a], [A], [],
          NonemptySpineDerives.terminal h,
          by simp,
          by simp⟩

  | @unit A B w path siblings h d ih =>
      obtain ⟨w', path', siblings', hspine, hnodup, hsib'⟩ :=
        ih hsib
      by_cases hmem : A ∈ path'
      · exact
          subspine_of_mem_of_nodup
            G τB hspine hnodup hsib' hmem
      · exact
          ⟨w', A :: path', siblings',
            NonemptySpineDerives.unit h hspine,
            (by simpa [List.nodup_cons, hmem] using hnodup),
            hsib'⟩

  | @binaryLeft A B C wB wC path siblings h dB dC ih =>
      have hhead : wC.length ≤ τB :=
        hsib wC.length (List.mem_cons_self ..)
      have hsibTail : ∀ s ∈ siblings, s ≤ τB := by
        intro s hs
        exact hsib s (List.mem_cons_of_mem _ hs)
      obtain ⟨w', path', siblings', hspine, hnodup, hsib'⟩ :=
        ih hsibTail
      by_cases hmem : A ∈ path'
      · exact
          subspine_of_mem_of_nodup
            G τB hspine hnodup hsib' hmem
      · refine
          ⟨w' ++ wC, A :: path', wC.length :: siblings',
            NonemptySpineDerives.binaryLeft h hspine dC,
            ?_,
            ?_⟩
        · rw [List.nodup_cons]
          exact ⟨hmem, hnodup⟩
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact hhead
          · exact hsib' s hs

  | @binaryRight A B C wB wC path siblings h dB dC ih =>
      have hhead : wB.length ≤ τB :=
        hsib wB.length (List.mem_cons_self ..)
      have hsibTail : ∀ s ∈ siblings, s ≤ τB := by
        intro s hs
        exact hsib s (List.mem_cons_of_mem _ hs)
      obtain ⟨w', path', siblings', hspine, hnodup, hsib'⟩ :=
        ih hsibTail
      by_cases hmem : A ∈ path'
      · exact
          subspine_of_mem_of_nodup
            G τB hspine hnodup hsib' hmem
      · refine
          ⟨wB ++ w', A :: path', wB.length :: siblings',
            NonemptySpineDerives.binaryRight h dB hspine,
            ?_,
            ?_⟩
        · rw [List.nodup_cons]
          exact ⟨hmem, hnodup⟩
        · intro s hs
          simp only [List.mem_cons] at hs
          rcases hs with rfl | hs
          · exact hhead
          · exact hsib' s hs

/--
The exact remaining shortcut property: every nonempty-productive state has a
bounded-sibling distinguished spine with no repeated nonterminal label.
-/
def NodupBoundedSpineProperty
    (G : BinaryNullableGrammar N α)
    (τB : Nat) : Prop :=
  ∀ A,
    (∃ w, BinaryNullableDerives G A w ∧ w ≠ []) →
    ∃ w path siblings,
      NonemptySpineDerives G A w path siblings
      ∧ path.Nodup
      ∧ (∀ s ∈ siblings, s ≤ τB)

/--
A uniform short-yield bound supplies the full cycle-shortcut property needed
by the Appendix A shortest-nonempty-yield argument.
-/
theorem nodupBoundedSpineProperty_of_yieldBound
    (G : BinaryNullableGrammar N α)
    (τB : Nat)
    (hshort :
      YieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        τB) :
    NodupBoundedSpineProperty G τB := by
  intro A hExists
  obtain ⟨w, hw, hne⟩ := hExists
  obtain ⟨w₀, path₀, siblings₀, hspine₀, hsib₀⟩ :=
    boundedSpine_of_nonemptyDerivation G τB hshort hw hne
  exact
    normalize_boundedSpine_to_nodup
      G τB hspine₀ hsib₀

/--
Once the cycle-shortcut property is supplied, the semantic shortest-nonempty
yield statement used in Appendix A follows with the exact
1 + |V_B| * tau_B envelope.
-/
theorem nonemptyYieldBound_of_nodupBoundedSpines
    [Fintype N] [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (τB : Nat)
    (hshortcut : NodupBoundedSpineProperty G τB) :
    NonemptyYieldBound
      (fun A => {w | BinaryNullableDerives G A w})
      (nullableNonemptyEnvelope (Fintype.card N) τB) := by
  intro A hExists
  obtain ⟨w, path, siblings, hspine, hnodup, hsib⟩ :=
    hshortcut A hExists
  refine
    ⟨w,
      nonemptySpine_to_derives G hspine,
      nonemptySpine_word_ne_nil G hspine,
      ?_⟩
  have hcount :
      siblings.length ≤ path.length :=
    nonemptySpine_siblings_length_le_path G hspine
  have hbound :
      1 + siblings.sum ≤
        1 + Fintype.card N * τB :=
    shortened_path_nonempty_yield_bound
      path siblings τB hnodup hcount hsib
  have hlen :
      w.length = 1 + siblings.sum :=
    nonemptySpine_length_eq G hspine
  unfold nullableNonemptyEnvelope
  rw [hlen]
  exact hbound


/--
Fully discharged semantic shortest-nonempty-yield bound from a uniform
short-yield bound: the cycle-shortening hypothesis is no longer external.
-/
theorem nonemptyYieldBound_of_yieldBound
    [Fintype N] [DecidableEq N]
    (G : BinaryNullableGrammar N α)
    (τB : Nat)
    (hshort :
      YieldBound
        (fun A => {w | BinaryNullableDerives G A w})
        τB) :
    NonemptyYieldBound
      (fun A => {w | BinaryNullableDerives G A w})
      (nullableNonemptyEnvelope (Fintype.card N) τB) := by
  exact
    nonemptyYieldBound_of_nodupBoundedSpines
      G τB
      (nodupBoundedSpineProperty_of_yieldBound
        G τB hshort)

end ShortestNonemptySpineSemantic

end TCS1
end LeanCfgProject
