import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# TCS #1 v135: step-counted list primitives for `thm:poly-build`

**Cost model (stated once, used everywhere in the `PolyBuild` namespace).**
Every function here returns a pair `(value, steps)`.  The step count is
computed *by the same recursion that computes the value*; there is no separate
cost function that could drift from the computation.  One step is charged for

* visiting or creating one cell of a linked list (`List` is a linked list in
  Lean, so `drop`, `take`, `length`, list comparison and the spine copy of an
  append are all charged per cell);
* one equality test of two letters (`DecidableEq α`; the alphabet is fixed);
* one lookup of a letter type `h(a)` and one multiplication in the fixed
  finite monoid, and one equality test of two monoid elements;
* one comparison of two natural-number loop indices (indices are at most the
  input length, i.e. word-RAM unit cost; this is RAM operation count, not
  bit complexity);
* one unit of loop overhead per iteration.

No operation on unbounded data (word comparison, slicing, typing a factor) is
treated as constant time: each is implemented below by explicit recursion and
charged per cell.  `Finset` operations are not used by the algorithm.
-/

namespace LeanCfgProject
namespace TCS1
namespace PolyBuild

universe u v w

section Primitives

variable {α : Type u}

/-- `List.length` with one step per cell. -/
def lengthC : List α → Nat × Nat
  | [] => (0, 1)
  | _ :: l => ((lengthC l).1 + 1, (lengthC l).2 + 1)

theorem lengthC_fst : ∀ l : List α, (lengthC l).1 = l.length
  | [] => rfl
  | _ :: l => by
      show (lengthC l).1 + 1 = l.length + 1
      rw [lengthC_fst l]

theorem lengthC_snd : ∀ l : List α, (lengthC l).2 = l.length + 1
  | [] => rfl
  | _ :: l => by
      show (lengthC l).2 + 1 = l.length + 1 + 1
      rw [lengthC_snd l]

/-- `List.drop` with one step per visited cell. -/
def dropC : Nat → List α → List α × Nat
  | 0, l => (l, 1)
  | _ + 1, [] => ([], 1)
  | n + 1, _ :: l => ((dropC n l).1, (dropC n l).2 + 1)

theorem dropC_fst : ∀ (n : Nat) (l : List α), (dropC n l).1 = l.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: l => by
      show (dropC n l).1 = l.drop n
      exact dropC_fst n l

theorem dropC_snd_le : ∀ (n : Nat) (l : List α), (dropC n l).2 ≤ n + 1
  | 0, _ => le_refl _
  | _ + 1, [] => by show 1 ≤ _; omega
  | n + 1, _ :: l => by
      show (dropC n l).2 + 1 ≤ n + 1 + 1
      have := dropC_snd_le n l
      omega

/-- `List.take` with one step per created cell. -/
def takeC : Nat → List α → List α × Nat
  | 0, _ => ([], 1)
  | _ + 1, [] => ([], 1)
  | n + 1, a :: l => (a :: (takeC n l).1, (takeC n l).2 + 1)

theorem takeC_fst : ∀ (n : Nat) (l : List α), (takeC n l).1 = l.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, a :: l => by
      show a :: (takeC n l).1 = a :: l.take n
      rw [takeC_fst n l]

theorem takeC_snd_le : ∀ (n : Nat) (l : List α), (takeC n l).2 ≤ n + 1
  | 0, _ => le_refl _
  | _ + 1, [] => by show 1 ≤ _; omega
  | n + 1, _ :: l => by
      show (takeC n l).2 + 1 ≤ n + 1 + 1
      have := takeC_snd_le n l
      omega

/-- The factor `w[i:j]` (as `(w.drop i).take (j - i)`). -/
def slice (w : List α) (i j : Nat) : List α := (w.drop i).take (j - i)

/-- Slicing: drop to position `i`, then copy `j - i` cells. -/
def sliceC (w : List α) (i j : Nat) : List α × Nat :=
  ((takeC (j - i) (dropC i w).1).1, (dropC i w).2 + (takeC (j - i) (dropC i w).1).2)

theorem sliceC_fst (w : List α) (i j : Nat) : (sliceC w i j).1 = slice w i j := by
  show (takeC (j - i) (dropC i w).1).1 = (w.drop i).take (j - i)
  rw [takeC_fst, dropC_fst]

theorem sliceC_snd_le (w : List α) (i j : Nat) :
    (sliceC w i j).2 ≤ i + (j - i) + 2 := by
  show (dropC i w).2 + (takeC (j - i) (dropC i w).1).2 ≤ _
  have h1 := dropC_snd_le i w
  have h2 := takeC_snd_le (j - i) (dropC i w).1
  omega

/-- Letter-by-letter comparison of two words. -/
def eqC [DecidableEq α] : List α → List α → Bool × Nat
  | [], [] => (true, 1)
  | [], _ :: _ => (false, 1)
  | _ :: _, [] => (false, 1)
  | a :: s, b :: t =>
      if a = b then ((eqC s t).1, (eqC s t).2 + 1) else (false, 1)

theorem eqC_fst [DecidableEq α] :
    ∀ s t : List α, (eqC s t).1 = decide (s = t)
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: s, b :: t => by
      by_cases h : a = b
      · subst h
        show (if a = a then ((eqC s t).1, (eqC s t).2 + 1) else (false, 1)).1 = _
        rw [if_pos rfl]
        show (eqC s t).1 = decide (a :: s = a :: t)
        rw [eqC_fst s t]
        simp
      · show (if a = b then ((eqC s t).1, (eqC s t).2 + 1) else (false, 1)).1 = _
        rw [if_neg h]
        simp [h]

theorem eqC_snd_le [DecidableEq α] :
    ∀ s t : List α, (eqC s t).2 ≤ s.length + 1
  | [], [] => le_refl _
  | [], _ :: _ => le_refl _
  | _ :: _, [] => by show 1 ≤ _; omega
  | a :: s, b :: t => by
      show (if a = b then ((eqC s t).1, (eqC s t).2 + 1) else (false, 1)).2 ≤ _
      have := eqC_snd_le s t
      split_ifs
      · show (eqC s t).2 + 1 ≤ (a :: s).length + 1
        simp only [List.length_cons]
        omega
      · show 1 ≤ _
        omega

end Primitives

section Typing

variable {α : Type u} {M : Type v} [Monoid M]

/-- The monoid type of a word, one letter lookup and one multiplication per
letter: `h(a₁⋯aₘ) = h(a₁)⋯h(aₘ)`.  The letter images are given by `ha`. -/
def typeC (ha : α → M) : List α → M × Nat
  | [] => (1, 1)
  | a :: w => (ha a * (typeC ha w).1, (typeC ha w).2 + 1)

theorem typeC_snd (ha : α → M) : ∀ w : List α, (typeC ha w).2 = w.length + 1
  | [] => rfl
  | _ :: w => by
      show (typeC ha w).2 + 1 = w.length + 1 + 1
      rw [typeC_snd ha w]

/-- For a monoid homomorphism on words, `typeC` computes the homomorphic
image from the letter images. -/
theorem typeC_fst (h : List α → M) (hnil : h [] = 1)
    (happ : ∀ u v : List α, h (u ++ v) = h u * h v) :
    ∀ w : List α, (typeC (fun a => h [a]) w).1 = h w
  | [] => hnil.symm
  | a :: w => by
      show h [a] * (typeC (fun a => h [a]) w).1 = h (a :: w)
      rw [typeC_fst h hnil happ w]
      have := happ [a] w
      simpa using this.symm

end Typing

section Loops

variable {γ : Type w} {β : Type v}

/-- `for k in [0, n)`: concatenate the outputs of the body, paying its steps,
one step of loop overhead, and one step per output cell for the append. -/
def forNatC (f : Nat → List γ × Nat) : Nat → List γ × Nat
  | 0 => ([], 1)
  | n + 1 =>
      ((f n).1 ++ (forNatC f n).1,
        (f n).2 + (forNatC f n).2 + (f n).1.length + 1)

theorem mem_forNatC (f : Nat → List γ × Nat) (x : γ) :
    ∀ n, x ∈ (forNatC f n).1 ↔ ∃ k, k < n ∧ x ∈ (f k).1
  | 0 => by simp [forNatC]
  | n + 1 => by
      show x ∈ (f n).1 ++ (forNatC f n).1 ↔ _
      rw [List.mem_append, mem_forNatC f x n]
      constructor
      · rintro (h | ⟨k, hk, h⟩)
        · exact ⟨n, Nat.lt_succ_self n, h⟩
        · exact ⟨k, Nat.lt_succ_of_lt hk, h⟩
      · rintro ⟨k, hk, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
        · exact Or.inr ⟨k, hk, h⟩
        · exact Or.inl h

/-- Loop bound: if every body call outputs at most as many cells as it
spends steps and spends at most `c` steps, the loop spends at most
`n * (2c + 1) + 1` steps (and still outputs at most its step count). -/
theorem forNatC_bound (f : Nat → List γ × Nat) (c : Nat) :
    ∀ n, (∀ k, k < n → (f k).1.length ≤ (f k).2 ∧ (f k).2 ≤ c) →
      (forNatC f n).1.length ≤ (forNatC f n).2 ∧
      (forNatC f n).2 ≤ n * (2 * c + 1) + 1
  | 0, _ => by simp [forNatC]
  | n + 1, hf => by
      obtain ⟨ih1, ih2⟩ := forNatC_bound f c n
        (fun k hk => hf k (Nat.lt_succ_of_lt hk))
      obtain ⟨h1, h2⟩ := hf n (Nat.lt_succ_self n)
      show ((f n).1 ++ (forNatC f n).1).length ≤
          (f n).2 + (forNatC f n).2 + (f n).1.length + 1 ∧
        (f n).2 + (forNatC f n).2 + (f n).1.length + 1 ≤
          (n + 1) * (2 * c + 1) + 1
      rw [List.length_append]
      constructor
      · omega
      · have : (n + 1) * (2 * c + 1) + 1 = n * (2 * c + 1) + 1 + 2 * c + 1 := by
          ring
        omega

/-- `for b in l`: same accounting as `forNatC`. -/
def forListC (f : β → List γ × Nat) : List β → List γ × Nat
  | [] => ([], 1)
  | b :: l =>
      ((f b).1 ++ (forListC f l).1,
        (f b).2 + (forListC f l).2 + (f b).1.length + 1)

theorem mem_forListC (f : β → List γ × Nat) (x : γ) :
    ∀ l : List β, x ∈ (forListC f l).1 ↔ ∃ b, b ∈ l ∧ x ∈ (f b).1
  | [] => by simp [forListC]
  | b :: l => by
      show x ∈ (f b).1 ++ (forListC f l).1 ↔ _
      rw [List.mem_append, mem_forListC f x l]
      constructor
      · rintro (h | ⟨b', hb', h⟩)
        · exact ⟨b, by simp, h⟩
        · exact ⟨b', List.mem_cons_of_mem _ hb', h⟩
      · rintro ⟨b', hb', h⟩
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact Or.inl h
        · exact Or.inr ⟨b', hb', h⟩

theorem forListC_bound (f : β → List γ × Nat) (c : β → Nat) :
    ∀ l : List β,
      (∀ b, b ∈ l → (f b).1.length ≤ (f b).2 ∧ (f b).2 ≤ c b) →
      (forListC f l).1.length ≤ (forListC f l).2 ∧
        (forListC f l).2 ≤ (l.map (fun b => 2 * c b + 1)).sum + 1
  | [], _ => by simp [forListC]
  | b :: l, hf => by
      obtain ⟨ih1, ih2⟩ :=
        forListC_bound f c l (fun b' hb' => hf b' (List.mem_cons_of_mem _ hb'))
      obtain ⟨h1, h2⟩ := hf b (by simp)
      show ((f b).1 ++ (forListC f l).1).length ≤
          (f b).2 + (forListC f l).2 + (f b).1.length + 1 ∧
        (f b).2 + (forListC f l).2 + (f b).1.length + 1 ≤
          ((b :: l).map (fun b => 2 * c b + 1)).sum + 1
      rw [List.length_append, List.map_cons, List.sum_cons]
      constructor
      · omega
      · omega

end Loops

section Arithmetic

/-- One loop level multiplies a monomial bound by the number of iterations. -/
theorem loopStep_le (m c K X : Nat) (hX : 1 ≤ X) (hm : 1 ≤ m)
    (hc : c ≤ K * X) :
    m * (2 * c + 1) + 1 ≤ (2 * K + 2) * (m * X) := by
  have h1 : m * (2 * c + 1) ≤ m * (2 * (K * X) + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : m ≤ m * X := Nat.le_mul_of_pos_right m hX
  have h3 : 1 ≤ m * X := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  have e1 : m * (2 * (K * X) + 1) = 2 * K * (m * X) + m := by ring
  have e2 : (2 * K + 2) * (m * X) = 2 * K * (m * X) + 2 * (m * X) := by ring
  omega

/-- `Σ_{b∈l} f b * Y = (Σ f) * Y`. -/
theorem sum_map_mul_const {β : Type v} (l : List β) (f : β → Nat) (Y : Nat) :
    (l.map (fun b => f b * Y)).sum = (l.map f).sum * Y := by
  induction l with
  | nil => simp
  | cons b l ih => simp [List.sum_cons, ih, Nat.add_mul]

/-- Every summand is at most the sum. -/
theorem le_sum_map_of_mem {β : Type v} {l : List β} (f : β → Nat) {b : β}
    (hb : b ∈ l) : f b ≤ (l.map f).sum := by
  induction l with
  | nil => cases hb
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hb with rfl | hb
      · omega
      · have := ih hb
        omega

theorem sum_map_le_sum_map {β : Type v} (l : List β) (f g : β → Nat)
    (h : ∀ b, b ∈ l → f b ≤ g b) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have h1 := h a (by simp)
      have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      omega

theorem length_le_sum_map_succ {β : Type v} (l : List β) (f : β → Nat) :
    l.length ≤ (l.map (fun b => f b + 1)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons]
      omega

end Arithmetic

end PolyBuild
end TCS1
end LeanCfgProject
