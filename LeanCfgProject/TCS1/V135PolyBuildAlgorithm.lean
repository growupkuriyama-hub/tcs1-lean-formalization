import LeanCfgProject.TCS1.V135CostedPrimitives

/-!
# TCS #1 v135: an executable, step-counted constructor for the v116 grammar

The manuscript's reconstruction operator `B_h(K)` (v116 form) has

* nonterminals: the nonempty factors observed in `K`;
* (B) `x → y z` for every observed `x = y z` with `y, z ≠ λ`;
* (U) `x → y` whenever `x, y` share a context in `K` and `h(x) = h(y)`;
* (L) `[a] → a` for every observed one-letter factor;
* (S) `S₀ → w` for every nonempty `w ∈ K`;
* (ε) `S₀ → λ` iff `λ ∈ K`.

`constructV116C` below computes all of these from a list `ws` of sample
words, writing factors literally as nonterminal names (the manuscript's proof
explicitly allows this).  Equal names are equal strings, so no hashing or
identifier assignment is involved.  The output lists may contain repeated
productions; the *set* of productions is the v116 grammar.

Every step is counted with the cost model of `V135CostedPrimitives`.
This file proves, against self-contained specifications:

* exact membership characterizations of all six output components;
* `constructV116C_cost_le`: the step count is at most `C · (N + 1)^4`, where
  `N = Σ_{w ∈ ws} (|w| + 1)` is the encoded size of the input list and `C`
  is an absolute numeral (independent of `h`, `Σ`, `M`).

The connection with the existing finite rule tables and with `BatchLanguage`
is in `V135PolyBuildBridge.lean`.
-/

namespace LeanCfgProject
namespace TCS1
namespace PolyBuild

set_option linter.unusedSectionVars false

universe u v

section SliceLemmas

variable {α : Type u}

theorem slice_split (w : List α) {i j : Nat} (hij : i ≤ j) :
    w.take i ++ slice w i j ++ w.drop j = w := by
  have ht : w.take j = w.take i ++ slice w i j := by
    unfold slice
    have h := List.take_add (l := w) (i := i) (j := j - i)
    rwa [Nat.add_sub_cancel' hij] at h
  rw [← ht, List.take_append_drop]

theorem slice_length (w : List α) {i j : Nat} (hij : i ≤ j) (hj : j ≤ w.length) :
    (slice w i j).length = j - i := by
  unfold slice
  simp only [List.length_take, List.length_drop]
  omega

theorem slice_ne_nil (w : List α) {i j : Nat} (hij : i < j) (hj : j ≤ w.length) :
    slice w i j ≠ [] := by
  intro h
  have := slice_length w (le_of_lt hij) hj
  rw [h] at this
  simp at this
  omega

theorem slice_of_split (p m q : List α) :
    slice (p ++ m ++ q) p.length (p.length + m.length) = m := by
  unfold slice
  rw [List.append_assoc, List.drop_left, Nat.add_sub_cancel_left, List.take_left]

theorem slice_append (w : List α) {i j k : Nat} (hij : i ≤ j) (hjk : j ≤ k) :
    slice w i j ++ slice w j k = slice w i k := by
  unfold slice
  have h := List.take_add (l := w.drop i) (i := j - i) (j := k - j)
  have e1 : j - i + (k - j) = k - i := by omega
  rw [e1, List.drop_drop] at h
  have e2 : i + (j - i) = j := by omega
  rw [e2] at h
  exact h.symm

theorem take_of_split (p m q : List α) : (p ++ m ++ q).take p.length = p := by
  rw [List.append_assoc, List.take_left]

theorem drop_of_split (p m q : List α) :
    (p ++ m ++ q).drop (p.length + m.length) = q := by
  rw [← List.length_append, List.drop_left]

end SliceLemmas

section Constructor

variable {α : Type u} [DecidableEq α]
variable {M : Type v} [Monoid M] [DecidableEq M]

/-- (B) body: emit `w[i:k] → w[i:j] w[j:k]` when `i < j < k`. -/
def binaryBody (w : List α) (i j k : Nat) :
    List (List α × List α × List α) × Nat :=
  if i < j ∧ j < k then
    ([((sliceC w i k).1, (sliceC w i j).1, (sliceC w j k).1)],
      (sliceC w i k).2 + (sliceC w i j).2 + (sliceC w j k).2 + 1)
  else ([], 1)

/-- (B) for one sample word: three nested index loops over `[0, |w|]`. -/
def binaryWord (w : List α) : List (List α × List α × List α) × Nat :=
  ((forNatC (fun i => forNatC (fun j => forNatC (fun k => binaryBody w i j k)
      ((lengthC w).1 + 1)) ((lengthC w).1 + 1)) ((lengthC w).1 + 1)).1,
    (lengthC w).2 + (forNatC (fun i => forNatC (fun j => forNatC
      (fun k => binaryBody w i j k) ((lengthC w).1 + 1)) ((lengthC w).1 + 1))
      ((lengthC w).1 + 1)).2)

/-- (U) body for the pair of sample words `w, w'`, positions `i < j` in `w`
and `i < j'` in `w'`: emit `w[i:j] → w'[i:j']` iff the left contexts
`w[0:i] = w'[0:i]`, the right contexts `w[j:] = w'[j':]`, and the types agree.
All three tests are performed letter by letter / letter-type by letter-type. -/
def unaryBody (ha : α → M) (w w' : List α) (i j j' : Nat) :
    List (List α × List α) × Nat :=
  if i < j ∧ i < j' then
    let p1 := takeC i w
    let p2 := takeC i w'
    let e1 := eqC p1.1 p2.1
    let s1 := dropC j w
    let s2 := dropC j' w'
    let e2 := eqC s1.1 s2.1
    let x := sliceC w i j
    let y := sliceC w' i j'
    let tx := typeC ha x.1
    let ty := typeC ha y.1
    let c := p1.2 + p2.2 + e1.2 + s1.2 + s2.2 + e2.2 + x.2 + y.2 +
      tx.2 + ty.2 + 1
    if e1.1 = true ∧ e2.1 = true ∧ tx.1 = ty.1 then ([(x.1, y.1)], c) else ([], c)
  else ([], 1)

/-- (U) for one ordered pair of sample words. -/
def unaryPair (ha : α → M) (w w' : List α) : List (List α × List α) × Nat :=
  ((forNatC (fun i => forNatC (fun j => forNatC (fun j' => unaryBody ha w w' i j j')
      ((lengthC w').1 + 1)) ((lengthC w).1 + 1)) ((lengthC w).1 + 1)).1,
    (lengthC w).2 + (lengthC w').2 +
      (forNatC (fun i => forNatC (fun j => forNatC
        (fun j' => unaryBody ha w w' i j j') ((lengthC w').1 + 1))
        ((lengthC w).1 + 1)) ((lengthC w).1 + 1)).2)

/-- Emit a lexical rule from a one-letter factor. -/
def lexEmit : List α → List (List α × α)
  | [a] => [([a], a)]
  | _ => []

/-- (L) body: the factor `w[i:i+1]`. -/
def lexicalBody (w : List α) (i : Nat) : List (List α × α) × Nat :=
  (lexEmit (sliceC w i (i + 1)).1, (sliceC w i (i + 1)).2 + 1)

def lexicalWord (w : List α) : List (List α × α) × Nat :=
  ((forNatC (lexicalBody w) (lengthC w).1).1,
    (lengthC w).2 + (forNatC (lexicalBody w) (lengthC w).1).2)

/-- (S) emits every nonempty sample word (shared, not copied). -/
def startEmit : List α → List (List α)
  | [] => []
  | a :: l => [a :: l]

/-- (ε) marker for the empty sample word. -/
def epsEmit : List α → List Unit
  | [] => [()]
  | _ :: _ => []

/-- (S) loop body: one step per sample word. -/
def startBody (w : List α) : List (List α) × Nat := (startEmit w, 1)

/-- (ε) loop body: one step per sample word. -/
def epsBody (w : List α) : List Unit × Nat := (epsEmit w, 1)

/-- Nonterminal list: every nonempty factor `w[i:j]`. -/
def ntBody (w : List α) (i j : Nat) : List (List α) × Nat :=
  if i < j then ([(sliceC w i j).1], (sliceC w i j).2 + 1) else ([], 1)

def ntWord (w : List α) : List (List α) × Nat :=
  ((forNatC (fun i => forNatC (fun j => ntBody w i j) ((lengthC w).1 + 1))
      ((lengthC w).1 + 1)).1,
    (lengthC w).2 + (forNatC (fun i => forNatC (fun j => ntBody w i j)
      ((lengthC w).1 + 1)) ((lengthC w).1 + 1)).2)

/-- Literal encoding of the v116 grammar `B_h(K)`. -/
structure V116GrammarCode (α : Type u) where
  nonterminals : List (List α)
  binary : List (List α × List α × List α)
  unary : List (List α × List α)
  lexical : List (List α × α)
  start : List (List α)
  epsilon : Bool

/-- The whole constructor, with its step count. -/
def constructV116C (ha : α → M) (ws : List (List α)) : V116GrammarCode α × Nat :=
  let N := forListC ntWord ws
  let B := forListC binaryWord ws
  let U := forListC (fun w => forListC (fun w' => unaryPair ha w w') ws) ws
  let L := forListC lexicalWord ws
  let S := forListC startBody ws
  let E := forListC epsBody ws
  (⟨N.1, B.1, U.1, L.1, S.1, !E.1.isEmpty⟩,
    N.2 + B.2 + U.2 + L.2 + S.2 + E.2 + 1)

/-- The constructed grammar code. -/
def constructV116 (ha : α → M) (ws : List (List α)) : V116GrammarCode α :=
  (constructV116C ha ws).1

/-- The number of steps spent by the constructor. -/
def constructV116Cost (ha : α → M) (ws : List (List α)) : Nat :=
  (constructV116C ha ws).2

end Constructor

section Correctness

variable {α : Type u} [DecidableEq α]
variable {M : Type v} [Monoid M] [DecidableEq M]

/-- `x` occurs as a nonempty factor of some sample word, in context `(p, q)`. -/
def OccursIn (ws : List (List α)) (x p q : List α) : Prop :=
  x ≠ [] ∧ p ++ x ++ q ∈ ws

theorem mem_binaryBody (w : List α) (i j k : Nat) (t : List α × List α × List α) :
    t ∈ (binaryBody w i j k).1 ↔
      i < j ∧ j < k ∧ t = (slice w i k, slice w i j, slice w j k) := by
  unfold binaryBody
  by_cases h : i < j ∧ j < k
  · rw [if_pos h]
    simp [sliceC_fst, h]
  · rw [if_neg h]
    simp only [List.not_mem_nil, false_iff]
    intro h'
    exact h ⟨h'.1, h'.2.1⟩

theorem mem_binaryWord (w : List α) (t : List α × List α × List α) :
    t ∈ (binaryWord w).1 ↔
      ∃ i j k, i < j ∧ j < k ∧ k ≤ w.length ∧
        t = (slice w i k, slice w i j, slice w j k) := by
  show t ∈ (forNatC _ _).1 ↔ _
  rw [lengthC_fst]
  constructor
  · intro ht
    obtain ⟨i, hi, ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨j, hj, ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨k, hk, ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨h1, h2, h3⟩ := (mem_binaryBody w i j k t).1 ht
    exact ⟨i, j, k, h1, h2, by omega, h3⟩
  · rintro ⟨i, j, k, h1, h2, hk, ht⟩
    refine (mem_forNatC _ _ _).2 ⟨i, by omega, ?_⟩
    refine (mem_forNatC _ _ _).2 ⟨j, by omega, ?_⟩
    refine (mem_forNatC _ _ _).2 ⟨k, by omega, ?_⟩
    exact (mem_binaryBody w i j k t).2 ⟨h1, h2, ht⟩

/-- **(B) is exact**: the emitted binary productions are precisely the
`x → y z` with `x = y z`, `y, z ≠ λ`, and `x` an observed factor. -/
theorem mem_binary (ha : α → M) (ws : List (List α)) (x y z : List α) :
    (x, y, z) ∈ (constructV116 ha ws).binary ↔
      x = y ++ z ∧ y ≠ [] ∧ z ≠ [] ∧ ∃ p q, OccursIn ws x p q := by
  show (x, y, z) ∈ (forListC binaryWord ws).1 ↔ _
  rw [mem_forListC]
  constructor
  · rintro ⟨w, hw, ht⟩
    obtain ⟨i, j, k, hij, hjk, hk, ht⟩ := (mem_binaryWord w _).1 ht
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl, rfl⟩ := ht
    refine ⟨(slice_append w (le_of_lt hij) (le_of_lt hjk)).symm,
      slice_ne_nil w hij (by omega), slice_ne_nil w hjk hk,
      w.take i, w.drop k, slice_ne_nil w (by omega) hk, ?_⟩
    rw [slice_split w (by omega)]
    exact hw
  · rintro ⟨rfl, hy, hz, p, q, _, hw⟩
    refine ⟨p ++ (y ++ z) ++ q, hw, ?_⟩
    apply (mem_binaryWord _ _).2
    have hy0 : 0 < y.length := List.length_pos_iff.mpr hy
    have hz0 : 0 < z.length := List.length_pos_iff.mpr hz
    refine ⟨p.length, p.length + y.length, p.length + y.length + z.length,
      by omega, by omega, by simp; omega, ?_⟩
    have e1 : slice (p ++ (y ++ z) ++ q) p.length
        (p.length + y.length + z.length) = y ++ z := by
      have := slice_of_split p (y ++ z) q
      rwa [List.length_append, ← Nat.add_assoc] at this
    have e2 : slice (p ++ (y ++ z) ++ q) p.length (p.length + y.length) = y := by
      have := slice_of_split p y (z ++ q)
      simpa only [List.append_assoc] using this
    have e3 : slice (p ++ (y ++ z) ++ q) (p.length + y.length)
        (p.length + y.length + z.length) = z := by
      have := slice_of_split (p ++ y) z q
      simpa only [List.append_assoc, List.length_append] using this
    rw [e1, e2, e3]

theorem mem_unaryBody (ha : α → M) (w w' : List α) (i j j' : Nat)
    (t : List α × List α) :
    t ∈ (unaryBody ha w w' i j j').1 ↔
      i < j ∧ i < j' ∧ w.take i = w'.take i ∧ w.drop j = w'.drop j' ∧
        (typeC ha (slice w i j)).1 = (typeC ha (slice w' i j')).1 ∧
        t = (slice w i j, slice w' i j') := by
  unfold unaryBody
  by_cases h : i < j ∧ i < j'
  · rw [if_pos h]
    simp only [takeC_fst, dropC_fst, eqC_fst, sliceC_fst, decide_eq_true_eq]
    by_cases h2 : w.take i = w'.take i ∧ w.drop j = w'.drop j' ∧
        (typeC ha (slice w i j)).1 = (typeC ha (slice w' i j')).1
    · rw [if_pos h2]
      simp [h, h2]
    · rw [if_neg h2]
      simp only [List.not_mem_nil, false_iff]
      rintro ⟨_, _, a, b, c, _⟩
      exact h2 ⟨a, b, c⟩
  · rw [if_neg h]
    simp only [List.not_mem_nil, false_iff]
    rintro ⟨a, b, _⟩
    exact h ⟨a, b⟩

theorem mem_unaryPair (ha : α → M) (w w' : List α) (t : List α × List α) :
    t ∈ (unaryPair ha w w').1 ↔
      ∃ i j j', i < j ∧ i < j' ∧ j ≤ w.length ∧ j' ≤ w'.length ∧
        w.take i = w'.take i ∧ w.drop j = w'.drop j' ∧
        (typeC ha (slice w i j)).1 = (typeC ha (slice w' i j')).1 ∧
        t = (slice w i j, slice w' i j') := by
  show t ∈ (forNatC _ _).1 ↔ _
  rw [lengthC_fst, lengthC_fst]
  constructor
  · intro ht
    obtain ⟨i, hi, ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨j, hj, ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨j', hj', ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := (mem_unaryBody ha w w' i j j' t).1 ht
    exact ⟨i, j, j', h1, h2, by omega, by omega, h3, h4, h5, h6⟩
  · rintro ⟨i, j, j', h1, h2, hj, hj', h3, h4, h5, h6⟩
    refine (mem_forNatC _ _ _).2 ⟨i, by omega, ?_⟩
    refine (mem_forNatC _ _ _).2 ⟨j, by omega, ?_⟩
    refine (mem_forNatC _ _ _).2 ⟨j', by omega, ?_⟩
    exact (mem_unaryBody ha w w' i j j' t).2 ⟨h1, h2, h3, h4, h5, h6⟩

/-- **(U) is exact**: for a monoid homomorphism `h` on words whose letter
images are `ha`, the emitted unit productions are precisely the pairs of
observed factors with a shared context and equal `h`-type. -/
theorem mem_unary (h : List α → M) (hnil : h [] = 1)
    (happ : ∀ u v : List α, h (u ++ v) = h u * h v)
    (ws : List (List α)) (x y : List α) :
    (x, y) ∈ (constructV116 (fun a => h [a]) ws).unary ↔
      h x = h y ∧ ∃ p q, OccursIn ws x p q ∧ OccursIn ws y p q := by
  have hty := typeC_fst h hnil happ
  show (x, y) ∈ (forListC (fun w => forListC (fun w' => unaryPair _ w w') ws) ws).1 ↔ _
  rw [mem_forListC]
  constructor
  · rintro ⟨w, hw, ht⟩
    obtain ⟨w', hw', ht⟩ := (mem_forListC _ _ _).1 ht
    obtain ⟨i, j, j', hij, hij', hj, hj', hp, hq, htype, ht⟩ :=
      (mem_unaryPair _ w w' _).1 ht
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    rw [hty, hty] at htype
    refine ⟨htype, w.take i, w.drop j, ⟨slice_ne_nil w hij hj, ?_⟩,
      ⟨slice_ne_nil w' hij' hj', ?_⟩⟩
    · rw [slice_split w (le_of_lt hij)]; exact hw
    · rw [hp, hq, slice_split w' (le_of_lt hij')]; exact hw'
  · rintro ⟨htype, p, q, ⟨hx, hwx⟩, ⟨hy, hwy⟩⟩
    refine ⟨p ++ x ++ q, hwx, (mem_forListC _ _ _).2 ⟨p ++ y ++ q, hwy, ?_⟩⟩
    apply (mem_unaryPair _ _ _ _).2
    have hx0 : 0 < x.length := List.length_pos_iff.mpr hx
    have hy0 : 0 < y.length := List.length_pos_iff.mpr hy
    refine ⟨p.length, p.length + x.length, p.length + y.length,
      by omega, by omega, by simp, by simp, ?_, ?_, ?_, ?_⟩
    · rw [take_of_split, take_of_split]
    · rw [drop_of_split, drop_of_split]
    · rw [slice_of_split, slice_of_split, hty, hty]; exact htype
    · rw [slice_of_split, slice_of_split]

theorem mem_lexEmit (l : List α) (t : List α × α) :
    t ∈ lexEmit l ↔ ∃ a, l = [a] ∧ t = ([a], a) := by
  match l with
  | [] => simp [lexEmit]
  | [a] => simp [lexEmit]
  | a :: b :: l => simp [lexEmit]

/-- **(L) is exact.** -/
theorem mem_lexical (ha : α → M) (ws : List (List α)) (x : List α) (a : α) :
    (x, a) ∈ (constructV116 ha ws).lexical ↔
      x = [a] ∧ ∃ p q, OccursIn ws [a] p q := by
  show (x, a) ∈ (forListC lexicalWord ws).1 ↔ _
  rw [mem_forListC]
  constructor
  · rintro ⟨w, hw, ht⟩
    have ht' : (x, a) ∈ (forNatC (lexicalBody w) (lengthC w).1).1 := ht
    rw [lengthC_fst] at ht'
    obtain ⟨i, hi, ht⟩ := (mem_forNatC _ _ _).1 ht'
    have ht2 : (x, a) ∈ lexEmit (slice w i (i + 1)) := by
      have : (x, a) ∈ lexEmit (sliceC w i (i + 1)).1 := ht
      rwa [sliceC_fst] at this
    obtain ⟨b, hb, ht⟩ := (mem_lexEmit _ _).1 ht2
    simp only [Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    refine ⟨rfl, w.take i, w.drop (i + 1), by simp, ?_⟩
    rw [← hb, slice_split w (by omega)]
    exact hw
  · rintro ⟨rfl, p, q, _, hw⟩
    refine ⟨p ++ [a] ++ q, hw, ?_⟩
    show ([a], a) ∈ (forNatC (lexicalBody _) (lengthC _).1).1
    rw [lengthC_fst]
    refine (mem_forNatC _ _ _).2 ⟨p.length, by simp, ?_⟩
    show ([a], a) ∈ lexEmit (sliceC (p ++ [a] ++ q) p.length (p.length + 1)).1
    rw [sliceC_fst]
    have := slice_of_split p [a] q
    simp only [List.length_singleton] at this
    rw [this]
    simp [lexEmit]

/-- **(S) is exact.** -/
theorem mem_start (ha : α → M) (ws : List (List α)) (x : List α) :
    x ∈ (constructV116 ha ws).start ↔ x ∈ ws ∧ x ≠ [] := by
  show x ∈ (forListC startBody ws).1 ↔ _
  rw [mem_forListC]
  constructor
  · rintro ⟨w, hw, ht⟩
    match w, ht with
    | a :: l, ht =>
        have : x = a :: l := by simpa [startBody, startEmit] using ht
        subst this
        exact ⟨hw, by simp⟩
  · rintro ⟨hx, hne⟩
    refine ⟨x, hx, ?_⟩
    match x, hne with
    | a :: l, _ => simp [startBody, startEmit]

/-- **(ε) is exact.** -/
theorem epsilon_iff (ha : α → M) (ws : List (List α)) :
    (constructV116 ha ws).epsilon = true ↔ [] ∈ ws := by
  show (!(forListC epsBody ws).1.isEmpty) = true ↔ _
  rw [Bool.not_eq_true', List.isEmpty_eq_false_iff_exists_mem]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨w, hw, hu⟩ := (mem_forListC _ _ _).1 hu
    match w, hu with
    | [], _ => exact hw
  · intro h
    exact ⟨(), (mem_forListC _ _ _).2 ⟨[], h, by simp [epsBody, epsEmit]⟩⟩

theorem mem_ntBody (w : List α) (i j : Nat) (x : List α) :
    x ∈ (ntBody w i j).1 ↔ i < j ∧ x = slice w i j := by
  unfold ntBody
  by_cases h : i < j
  · rw [if_pos h]; simp [sliceC_fst, h]
  · rw [if_neg h]; simp [h]

/-- **The declared nonterminals are exactly the observed factors.** -/
theorem mem_nonterminals (ha : α → M) (ws : List (List α)) (x : List α) :
    x ∈ (constructV116 ha ws).nonterminals ↔ ∃ p q, OccursIn ws x p q := by
  show x ∈ (forListC ntWord ws).1 ↔ _
  rw [mem_forListC]
  constructor
  · rintro ⟨w, hw, ht⟩
    have ht' : x ∈ (forNatC (fun i => forNatC (fun j => ntBody w i j)
        ((lengthC w).1 + 1)) ((lengthC w).1 + 1)).1 := ht
    rw [lengthC_fst] at ht'
    obtain ⟨i, hi, ht⟩ := (mem_forNatC _ _ _).1 ht'
    obtain ⟨j, hj, ht⟩ := (mem_forNatC _ _ _).1 ht
    obtain ⟨hij, rfl⟩ := (mem_ntBody w i j x).1 ht
    refine ⟨w.take i, w.drop j, slice_ne_nil w hij (by omega), ?_⟩
    rw [slice_split w (le_of_lt hij)]
    exact hw
  · rintro ⟨p, q, hx, hw⟩
    refine ⟨p ++ x ++ q, hw, ?_⟩
    show x ∈ (forNatC (fun i => forNatC (fun j => ntBody _ i j)
        ((lengthC _).1 + 1)) ((lengthC _).1 + 1)).1
    rw [lengthC_fst]
    have hx0 : 0 < x.length := List.length_pos_iff.mpr hx
    refine (mem_forNatC _ _ _).2 ⟨p.length, by simp; omega, ?_⟩
    refine (mem_forNatC _ _ _).2 ⟨p.length + x.length, by simp; omega, ?_⟩
    exact (mem_ntBody _ _ _ _).2 ⟨by omega, (slice_of_split p x q).symm⟩

end Correctness

section CostBounds

variable {α : Type u} [DecidableEq α]
variable {M : Type v} [Monoid M] [DecidableEq M]

theorem take_length_le (i : Nat) (w : List α) : (takeC i w).1.length ≤ i := by
  rw [takeC_fst, List.length_take]; exact Nat.min_le_left _ _

theorem slice_length_le (w : List α) (i j : Nat) : (slice w i j).length ≤ j - i := by
  unfold slice; rw [List.length_take]; exact Nat.min_le_left _ _

theorem binaryBody_bound (w : List α) (i j k : Nat)
    (hi : i < w.length + 1) (hj : j < w.length + 1) (hk : k < w.length + 1) :
    (binaryBody w i j k).1.length ≤ (binaryBody w i j k).2 ∧
      (binaryBody w i j k).2 ≤ 7 * (w.length + 1) := by
  unfold binaryBody
  split_ifs with h
  · have h1 := sliceC_snd_le w i k
    have h2 := sliceC_snd_le w i j
    have h3 := sliceC_snd_le w j k
    simp only [List.length_singleton]
    omega
  · simp only [List.length_nil]
    omega

theorem binaryWord_bound (w : List α) :
    (binaryWord w).1.length ≤ (binaryWord w).2 ∧
      (binaryWord w).2 ≤ 71 * ((w.length + 1) * ((w.length + 1) *
        ((w.length + 1) * (w.length + 1)))) := by
  set a := w.length + 1 with ha
  have ha1 : 1 ≤ a := by omega
  have hL : (lengthC w).1 + 1 = a := by rw [lengthC_fst]
  -- innermost loop over k
  have hk : ∀ i j, i < a → j < a →
      (forNatC (fun k => binaryBody w i j k) a).1.length ≤
        (forNatC (fun k => binaryBody w i j k) a).2 ∧
      (forNatC (fun k => binaryBody w i j k) a).2 ≤ 16 * (a * a) := by
    intro i j hi hj
    obtain ⟨l1, l2⟩ := forNatC_bound (fun k => binaryBody w i j k) (7 * a) a
      (fun k hk => binaryBody_bound w i j k hi hj hk)
    exact ⟨l1, l2.trans (loopStep_le a (7 * a) 7 a ha1 ha1 le_rfl)⟩
  have hj : ∀ i, i < a →
      (forNatC (fun j => forNatC (fun k => binaryBody w i j k) a) a).1.length ≤
        (forNatC (fun j => forNatC (fun k => binaryBody w i j k) a) a).2 ∧
      (forNatC (fun j => forNatC (fun k => binaryBody w i j k) a) a).2 ≤
        34 * (a * (a * a)) := by
    intro i hi
    obtain ⟨l1, l2⟩ := forNatC_bound _ (16 * (a * a)) a
      (fun j hj' => hk i j hi hj')
    exact ⟨l1, l2.trans (loopStep_le a _ 16 (a * a) (Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))) ha1 le_rfl)⟩
  obtain ⟨l1, l2⟩ := forNatC_bound _ (34 * (a * (a * a))) a (fun i hi => hj i hi)
  have l3 := l2.trans (loopStep_le a _ 34 (a * (a * a))
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
      (Nat.mul_ne_zero (by omega) (by omega)))) ha1 le_rfl)
  have hlen := lengthC_snd w
  have ha4 : a ≤ a * (a * (a * a)) := by
    have : 1 ≤ a * (a * a) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (Nat.mul_ne_zero (by omega) (by omega)))
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * (a * (a * a)) := Nat.mul_le_mul_left a this
  unfold binaryWord
  rw [hL]
  simp only
  constructor <;> omega

theorem unaryBody_bound (ha : α → M) (w w' : List α) (i j j' : Nat)
    (hi : i < w.length + 1) (hj : j < w.length + 1) (hj' : j' < w'.length + 1) :
    (unaryBody ha w w' i j j').1.length ≤ (unaryBody ha w w' i j j').2 ∧
      (unaryBody ha w w' i j j').2 ≤
        15 * ((w.length + 1) + (w'.length + 1)) := by
  unfold unaryBody
  dsimp only
  have t1 := takeC_snd_le i w
  have t2 := takeC_snd_le i w'
  have t3 := eqC_snd_le (takeC i w).1 (takeC i w').1
  have t3' := take_length_le i w
  have d1 := dropC_snd_le j w
  have d2 := dropC_snd_le j' w'
  have d3 := eqC_snd_le (dropC j w).1 (dropC j' w').1
  have d3' : (dropC j w).1.length ≤ w.length := by
    rw [dropC_fst, List.length_drop]; omega
  have s1 := sliceC_snd_le w i j
  have s2 := sliceC_snd_le w' i j'
  have y1 := typeC_snd ha (sliceC w i j).1
  have y2 := typeC_snd ha (sliceC w' i j').1
  have y1' : (sliceC w i j).1.length ≤ j - i := by
    rw [sliceC_fst]; exact slice_length_le w i j
  have y2' : (sliceC w' i j').1.length ≤ j' - i := by
    rw [sliceC_fst]; exact slice_length_le w' i j'
  split_ifs <;> simp only [List.length_singleton, List.length_nil] <;> omega

theorem unaryPair_bound (ha : α → M) (w w' : List α) :
    (unaryPair ha w w').1.length ≤ (unaryPair ha w w').2 ∧
      (unaryPair ha w w').2 ≤ 135 * ((w.length + 1) * ((w.length + 1) *
        ((w'.length + 1) * ((w.length + 1) + (w'.length + 1))))) := by
  set a := w.length + 1 with ha'
  set b := w'.length + 1 with hb'
  set s := a + b with hs
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hs1 : 1 ≤ s := by omega
  have p1 : ∀ x y : Nat, 1 ≤ x → 1 ≤ y → 1 ≤ x * y := fun x y hx hy =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hk : ∀ i j, i < a → j < a →
      (forNatC (fun j' => unaryBody ha w w' i j j') b).1.length ≤
        (forNatC (fun j' => unaryBody ha w w' i j j') b).2 ∧
      (forNatC (fun j' => unaryBody ha w w' i j j') b).2 ≤ 32 * (b * s) := by
    intro i j hi hj
    obtain ⟨l1, l2⟩ := forNatC_bound (fun j' => unaryBody ha w w' i j j') (15 * s) b
      (fun j' hj' => unaryBody_bound ha w w' i j j' hi hj hj')
    exact ⟨l1, l2.trans (loopStep_le b (15 * s) 15 s hs1 hb1 le_rfl)⟩
  have hj : ∀ i, i < a →
      (forNatC (fun j => forNatC (fun j' => unaryBody ha w w' i j j') b) a).1.length ≤
        (forNatC (fun j => forNatC (fun j' => unaryBody ha w w' i j j') b) a).2 ∧
      (forNatC (fun j => forNatC (fun j' => unaryBody ha w w' i j j') b) a).2 ≤
        66 * (a * (b * s)) := by
    intro i hi
    obtain ⟨l1, l2⟩ := forNatC_bound _ (32 * (b * s)) a (fun j hj' => hk i j hi hj')
    exact ⟨l1, l2.trans (loopStep_le a _ 32 (b * s) (p1 b s hb1 hs1) ha1 le_rfl)⟩
  obtain ⟨l1, l2⟩ := forNatC_bound _ (66 * (a * (b * s))) a (fun i hi => hj i hi)
  have l3 := l2.trans (loopStep_le a _ 66 (a * (b * s))
    (p1 a (b * s) ha1 (p1 b s hb1 hs1)) ha1 le_rfl)
  have h1 := lengthC_snd w
  have h2 := lengthC_snd w'
  have hsmall : s ≤ a * (a * (b * s)) := by
    have : 1 ≤ a * (a * b) := p1 a (a * b) ha1 (p1 a b ha1 hb1)
    calc s = 1 * s := (Nat.one_mul s).symm
      _ ≤ (a * (a * b)) * s := Nat.mul_le_mul_right s this
      _ = a * (a * (b * s)) := by ring
  have hLa : (lengthC w).1 + 1 = a := by rw [lengthC_fst]
  have hLb : (lengthC w').1 + 1 = b := by rw [lengthC_fst]
  unfold unaryPair
  rw [hLa, hLb]
  simp only
  constructor <;> omega

theorem lexEmit_length_le (l : List α) : (lexEmit l).length ≤ 1 := by
  match l with
  | [] => simp [lexEmit]
  | [a] => simp [lexEmit]
  | a :: b :: l => simp [lexEmit]

theorem lexicalWord_bound (w : List α) :
    (lexicalWord w).1.length ≤ (lexicalWord w).2 ∧
      (lexicalWord w).2 ≤ 11 * ((w.length + 1) * (w.length + 1)) := by
  set a := w.length + 1 with ha
  have ha1 : 1 ≤ a := by omega
  obtain ⟨l1, l2⟩ := forNatC_bound (lexicalBody w) (4 * a) w.length
    (fun i hi => by
      have h1 := sliceC_snd_le w i (i + 1)
      have h2 := lexEmit_length_le (sliceC w i (i + 1)).1
      show (lexEmit (sliceC w i (i + 1)).1).length ≤ (sliceC w i (i + 1)).2 + 1 ∧
        (sliceC w i (i + 1)).2 + 1 ≤ 4 * a
      omega)
  have l3 : w.length * (2 * (4 * a) + 1) + 1 ≤ 10 * (a * a) := by
    have h := loopStep_le a (4 * a) 4 a ha1 ha1 le_rfl
    have : w.length * (2 * (4 * a) + 1) ≤ a * (2 * (4 * a) + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hlen := lengthC_snd w
  have haa : a ≤ a * a := Nat.le_mul_of_pos_right a ha1
  unfold lexicalWord
  rw [lengthC_fst]
  simp only
  constructor <;> omega

theorem ntWord_bound (w : List α) :
    (ntWord w).1.length ≤ (ntWord w).2 ∧
      (ntWord w).2 ≤ 19 * ((w.length + 1) * ((w.length + 1) * (w.length + 1))) := by
  set a := w.length + 1 with ha
  have ha1 : 1 ≤ a := by omega
  have hb : ∀ i j, i < a → j < a →
      (ntBody w i j).1.length ≤ (ntBody w i j).2 ∧ (ntBody w i j).2 ≤ 3 * a := by
    intro i j hi hj
    unfold ntBody
    split_ifs
    · have := sliceC_snd_le w i j
      simp only [List.length_singleton]
      omega
    · simp only [List.length_nil]; omega
  have hj : ∀ i, i < a →
      (forNatC (fun j => ntBody w i j) a).1.length ≤
        (forNatC (fun j => ntBody w i j) a).2 ∧
      (forNatC (fun j => ntBody w i j) a).2 ≤ 8 * (a * a) := by
    intro i hi
    obtain ⟨l1, l2⟩ := forNatC_bound (fun j => ntBody w i j) (3 * a) a
      (fun j hj' => hb i j hi hj')
    exact ⟨l1, l2.trans (loopStep_le a (3 * a) 3 a ha1 ha1 le_rfl)⟩
  obtain ⟨l1, l2⟩ := forNatC_bound _ (8 * (a * a)) a (fun i hi => hj i hi)
  have l3 := l2.trans (loopStep_le a _ 8 (a * a)
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) ha1 le_rfl)
  have hlen := lengthC_snd w
  have ha3 : a ≤ a * (a * a) := by
    have : 1 ≤ a * a := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * (a * a) := Nat.mul_le_mul_left a this
  have hL : (lengthC w).1 + 1 = a := by rw [lengthC_fst]
  unfold ntWord
  rw [hL]
  simp only
  constructor <;> omega

/-- Encoded size of the input list: `N = Σ_{w ∈ ws} (|w| + 1)`. -/
def inputNorm (ws : List (List α)) : Nat := (ws.map (fun w => w.length + 1)).sum

theorem sum_map_affine {β : Type u} (l : List β) (f : β → Nat) (Y : Nat) :
    (l.map (fun b => f b * Y + 1)).sum = (l.map f).sum * Y + l.length := by
  induction l with
  | nil => simp
  | cons b l ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring

/-- Generic summation step: if each element `w` costs at most `a_w · Y`
(`a_w = |w| + 1`), the loop over `ws` costs at most `2·N·Y + N + 1`. -/
theorem forListC_sum_bound {γ : Type*} (ws : List (List α))
    (f : List α → List γ × Nat) (Y : Nat)
    (hf : ∀ w, w ∈ ws → (f w).1.length ≤ (f w).2 ∧
      (f w).2 ≤ (w.length + 1) * Y) :
    (forListC f ws).1.length ≤ (forListC f ws).2 ∧
      (forListC f ws).2 ≤ 2 * (inputNorm ws * Y) + inputNorm ws + 1 := by
  obtain ⟨l1, l2⟩ := forListC_bound f (fun w => (w.length + 1) * Y) ws hf
  refine ⟨l1, l2.trans ?_⟩
  have e : (ws.map (fun w => 2 * ((w.length + 1) * Y) + 1)).sum =
      (ws.map (fun w => (w.length + 1) * (2 * Y) + 1)).sum := by
    congr 1
    apply List.map_congr_left
    intro w _
    ring
  rw [e, sum_map_affine]
  have hlen : ws.length ≤ inputNorm ws := by
    unfold inputNorm
    have := length_le_sum_map_succ ws (fun w => w.length)
    simpa using this
  unfold inputNorm at hlen ⊢
  have : (ws.map (fun w => w.length + 1)).sum * (2 * Y) =
      2 * ((ws.map (fun w => w.length + 1)).sum * Y) := by ring
  omega

theorem le_inputNorm {ws : List (List α)} {w : List α} (hw : w ∈ ws) :
    w.length + 1 ≤ inputNorm ws :=
  le_sum_map_of_mem (fun w : List α => w.length + 1) hw

/-- **Polynomial (quartic) step bound for the v116 constructor.** -/
theorem constructV116Cost_le (ha : α → M) (ws : List (List α)) :
    constructV116Cost ha ws ≤ 1400 * (inputNorm ws + 1) ^ 4 := by
  set N := inputNorm ws with hN
  have pos : ∀ x y : Nat, 1 ≤ x → 1 ≤ y → 1 ≤ x * y := fun x y hx hy =>
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  -- nonterminals
  have hNT := forListC_sum_bound ws ntWord (19 * (N * N)) (fun w hw => by
    obtain ⟨l1, l2⟩ := ntWord_bound w
    refine ⟨l1, l2.trans ?_⟩
    have ha := le_inputNorm hw
    rw [← hN] at ha
    calc 19 * ((w.length + 1) * ((w.length + 1) * (w.length + 1)))
        ≤ 19 * ((w.length + 1) * (N * N)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul ha ha))
      _ = (w.length + 1) * (19 * (N * N)) := by ring)
  -- binary
  have hB := forListC_sum_bound ws binaryWord (71 * (N * (N * N))) (fun w hw => by
    obtain ⟨l1, l2⟩ := binaryWord_bound w
    refine ⟨l1, l2.trans ?_⟩
    have ha := le_inputNorm hw
    rw [← hN] at ha
    calc 71 * ((w.length + 1) * ((w.length + 1) * ((w.length + 1) * (w.length + 1))))
        ≤ 71 * ((w.length + 1) * (N * (N * N))) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
            (Nat.mul_le_mul ha (Nat.mul_le_mul ha ha)))
      _ = (w.length + 1) * (71 * (N * (N * N))) := by ring)
  -- unary: inner loop over w', then outer loop over w
  have hU := forListC_sum_bound ws (fun w => forListC (fun w' => unaryPair ha w w') ws)
    (542 * (N * (N * N))) (fun w hw => by
      have haN := le_inputNorm hw
      rw [← hN] at haN
      have hN1 : 1 ≤ N := by omega
      have inner := forListC_sum_bound ws (fun w' => unaryPair ha w w')
        (270 * ((w.length + 1) * (N * N))) (fun w' hw' => by
          obtain ⟨l1, l2⟩ := unaryPair_bound ha w w'
          refine ⟨l1, l2.trans ?_⟩
          have hbN := le_inputNorm hw'
          rw [← hN] at hbN
          have hs : (w.length + 1) + (w'.length + 1) ≤ 2 * N := by omega
          calc 135 * ((w.length + 1) * ((w.length + 1) *
                ((w'.length + 1) * ((w.length + 1) + (w'.length + 1)))))
              ≤ 135 * ((w.length + 1) * (N * ((w'.length + 1) * (2 * N)))) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
                  (Nat.mul_le_mul haN (Nat.mul_le_mul_left _ hs)))
            _ = (w'.length + 1) * (270 * ((w.length + 1) * (N * N))) := by ring)
      obtain ⟨l1, l2⟩ := inner
      rw [← hN] at l2
      refine ⟨l1, l2.trans ?_⟩
      have e : 2 * (N * (270 * ((w.length + 1) * (N * N)))) =
          (w.length + 1) * (540 * (N * (N * N))) := by ring
      have h3 : N + 1 ≤ (w.length + 1) * (2 * (N * (N * N))) := by
        have : 1 ≤ N * N := pos N N hN1 hN1
        have : N ≤ N * (N * N) := by
          calc N = N * 1 := (Nat.mul_one N).symm
            _ ≤ N * (N * N) := Nat.mul_le_mul_left N this
        have : 2 * (N * (N * N)) ≤ (w.length + 1) * (2 * (N * (N * N))) :=
          Nat.le_mul_of_pos_left _ (by omega)
        omega
      have e2 : (w.length + 1) * (542 * (N * (N * N))) =
          (w.length + 1) * (540 * (N * (N * N))) +
            (w.length + 1) * (2 * (N * (N * N))) := by ring
      omega)
  -- lexical
  have hL := forListC_sum_bound ws lexicalWord (11 * N) (fun w hw => by
    obtain ⟨l1, l2⟩ := lexicalWord_bound w
    refine ⟨l1, l2.trans ?_⟩
    have ha := le_inputNorm hw
    rw [← hN] at ha
    calc 11 * ((w.length + 1) * (w.length + 1)) ≤ 11 * ((w.length + 1) * N) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ha)
      _ = (w.length + 1) * (11 * N) := by ring)
  -- start and epsilon
  have hS := forListC_sum_bound ws startBody 1 (fun w _ => by
    match w with
    | [] => simp [startBody, startEmit]
    | _ :: _ => simp [startBody, startEmit])
  have hE := forListC_sum_bound ws epsBody 1 (fun w _ => by
    match w with
    | [] => simp [epsBody, epsEmit]
    | _ :: _ => simp [epsBody, epsEmit])
  rw [← hN] at hNT hB hU hL hS hE
  -- assemble: every term is dominated by a multiple of (N + 1)^4
  have X1 : N ≤ (N + 1) ^ 4 := by
    calc N ≤ N + 1 := Nat.le_succ N
      _ ≤ (N + 1) ^ 4 := Nat.le_self_pow (by omega) _
  have X2 : N * N ≤ (N + 1) ^ 4 := by
    calc N * N ≤ (N + 1) * (N + 1) := Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)
      _ = (N + 1) ^ 2 := by ring
      _ ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (Nat.succ_pos N) (by omega)
  have X3 : N * (N * N) ≤ (N + 1) ^ 4 := by
    calc N * (N * N) ≤ (N + 1) * ((N + 1) * (N + 1)) :=
          Nat.mul_le_mul (Nat.le_succ N) (Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N))
      _ = (N + 1) ^ 3 := by ring
      _ ≤ (N + 1) ^ 4 := Nat.pow_le_pow_right (Nat.succ_pos N) (by omega)
  have X4 : N * (N * (N * N)) ≤ (N + 1) ^ 4 := by
    calc N * (N * (N * N)) ≤ (N + 1) * ((N + 1) * ((N + 1) * (N + 1))) :=
          Nat.mul_le_mul (Nat.le_succ N) (Nat.mul_le_mul (Nat.le_succ N)
            (Nat.mul_le_mul (Nat.le_succ N) (Nat.le_succ N)))
      _ = (N + 1) ^ 4 := by ring
  have X0 : 1 ≤ (N + 1) ^ 4 := Nat.one_le_pow _ _ (Nat.succ_pos N)
  have r1 : N * (19 * (N * N)) = 19 * (N * (N * N)) := by ring
  have r2 : N * (71 * (N * (N * N))) = 71 * (N * (N * (N * N))) := by ring
  have r3 : N * (542 * (N * (N * N))) = 542 * (N * (N * (N * N))) := by ring
  have r4 : N * (11 * N) = 11 * (N * N) := by ring
  unfold constructV116Cost constructV116C
  simp only
  omega

end CostBounds

end PolyBuild
end TCS1
end LeanCfgProject
