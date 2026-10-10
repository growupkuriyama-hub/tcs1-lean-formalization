import LeanCfgProject.TCS1.V135PolyBuildBridge
import LeanCfgProject.TCS1.V144SSBNFNormalizer

/-!
# TCS #1 v158: step-counted membership for the written v116 grammar codes

`codeMemberC c w` decides `w ∈ codeLanguage c` for a grammar code `c` written by
the v116 constructor (`V116GrammarCode`: binary rules `x → y z`, unary rules
`x → y`, lexical rules `x → a`, start rules and the ε flag), with a step count
produced by the same recursion.

**Algorithm (CYK as a Horn closure).**  For `ℓ = |w|`, the atoms are the
triples `(x, i, j)` (`x` derives `w[i:j]`, `0 ≤ i < j ≤ ℓ`).  The Horn clauses
are
* `(x, i, i+1)` for every lexical rule `x → a` and every position `i` with
  `w[i] = a`;
* `(x, i, j) ⇐ (y, i, j)` for every unary rule `x → y` and every span;
* `(x, i, j) ⇐ (y, i, k), (z, k, j)` for every binary rule `x → y z` and every
  split `i < k < j`.
The chart is the Horn closure computed by `Horn.hornC` (`V144HornClosure`); the
domain is the set of atoms whose name is a rule head.  The word is accepted iff
`(x, 0, ℓ)` is in the chart for a start name `x`, or `w = []` and the ε flag is
set.

**Cost model** (as in `V135CostedPrimitives`): one step per list cell visited or
created, per loop iteration, per letter comparison and per index comparison.
Two atoms are compared by comparing their names letter by letter (`eqC`) and
their two indices (2 steps).

Results: `codeMemberC_correct` (`= true ↔ w ∈ codeLanguage c`) and
`codeMemberC_cost_le` (an explicit polynomial in the code size, `|w|` and the
longest name).
-/

namespace LeanCfgProject
namespace TCS1
namespace CodeCYK

open PolyBuild Horn SSBNFNorm

universe u

variable {α : Type u} [DecidableEq α]

/-! ### Atoms and their comparison -/

/-- A chart atom `(x, i, j)`: name `x` derives `w[i:j]`. -/
abbrev Atom (α : Type u) := List α × Nat × Nat

/-- Costed atom comparison. -/
def atomEqC (p q : Atom α) : Bool × Nat :=
  ((eqC p.1 q.1).1 && decide (p.2.1 = q.2.1) && decide (p.2.2 = q.2.2), (eqC p.1 q.1).2 + 2)

theorem atomEqC_correct : CeqCorrect (atomEqC (α := α)) := by
  intro p q
  obtain ⟨x, i, j⟩ := p
  obtain ⟨y, k, l⟩ := q
  simp only [atomEqC, eqC_fst, Prod.mk.injEq]
  by_cases h1 : x = y <;> by_cases h2 : i = k <;> by_cases h3 : j = l <;> simp [h1, h2, h3]

theorem atomEqC_snd_le (p q : Atom α) : (atomEqC p q).2 ≤ p.1.length + 3 := by
  have := eqC_snd_le p.1 q.1
  simp only [atomEqC]
  omega

/-! ### Enumerations of positions, spans and splits -/

/-- Positions with their letters. -/
def enumFrom (k : Nat) : List α → List (Nat × α)
  | [] => []
  | x :: xs => (k, x) :: enumFrom (k + 1) xs

theorem slice_cons_succ (x : α) (xs : List α) (i j : Nat) :
    slice (x :: xs) (i + 1) (j + 1) = slice xs i j := by
  simp [slice]

theorem mem_enumFrom (b : α) :
    ∀ (w : List α) (k i : Nat),
      (i, b) ∈ enumFrom k w ↔ k ≤ i ∧ i - k < w.length ∧ slice w (i - k) (i - k + 1) = [b]
  | [], k, i => by simp [enumFrom]
  | x :: xs, k, i => by
      simp only [enumFrom, List.mem_cons, Prod.mk.injEq]
      rw [mem_enumFrom b xs (k + 1) i]
      constructor
      · rintro (⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩)
        · refine ⟨le_refl _, by simp, ?_⟩
          simp [slice]
        · refine ⟨by omega, by simp; omega, ?_⟩
          have e : i - k = (i - (k + 1)) + 1 := by omega
          rw [e, slice_cons_succ]
          exact h3
      · rintro ⟨h1, h2, h3⟩
        by_cases hik : i = k
        · subst hik
          left
          simp [slice] at h3
          exact ⟨rfl, h3.symm⟩
        · right
          have e : i - k = (i - (k + 1)) + 1 := by omega
          rw [e, slice_cons_succ] at h3
          refine ⟨by omega, ?_, h3⟩
          simp at h2
          omega

/-- Costed enumeration (one step per cell). -/
def enumC (w : List α) : List (Nat × α) × Nat := (enumFrom 0 w, w.length + 1)

theorem enumFrom_length : ∀ (w : List α) (k : Nat), (enumFrom k w).length = w.length
  | [], _ => rfl
  | _ :: xs, k => by simp [enumFrom, enumFrom_length xs]

/-- All spans `(i, j)` with `i < j ≤ ℓ`. -/
def spansC (ℓ : Nat) : List (Nat × Nat) × Nat :=
  forNatC (fun i => forNatC (fun d => ([(i, i + d + 1)], 1)) (ℓ - i)) ℓ

theorem mem_spansC (ℓ i j : Nat) : (i, j) ∈ (spansC ℓ).1 ↔ i < j ∧ j ≤ ℓ := by
  unfold spansC
  rw [mem_forNatC]
  constructor
  · rintro ⟨i', hi', hm⟩
    rw [mem_forNatC] at hm
    obtain ⟨d, hd, hm⟩ := hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨i, by omega, ?_⟩
    rw [mem_forNatC]
    exact ⟨j - i - 1, by omega, by simp; omega⟩

/-- All splits `(i, k, j)` with `i < k < j ≤ ℓ`. -/
def splitsC (ℓ : Nat) : List (Nat × Nat × Nat) × Nat :=
  forNatC (fun i => forNatC (fun d => forNatC (fun e =>
    ([(i, i + d + 1, i + d + 1 + e + 1)], 1)) (ℓ - (i + d + 1))) (ℓ - i)) ℓ

theorem mem_splitsC (ℓ i k j : Nat) :
    (i, k, j) ∈ (splitsC ℓ).1 ↔ i < k ∧ k < j ∧ j ≤ ℓ := by
  unfold splitsC
  rw [mem_forNatC]
  constructor
  · rintro ⟨i', hi', hm⟩
    rw [mem_forNatC] at hm
    obtain ⟨d, hd, hm⟩ := hm
    rw [mem_forNatC] at hm
    obtain ⟨e, he, hm⟩ := hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨i, by omega, ?_⟩
    rw [mem_forNatC]
    refine ⟨k - i - 1, by omega, ?_⟩
    rw [mem_forNatC]
    exact ⟨j - k - 1, by omega, by simp; omega⟩

/-! ### Rules, domain and chart -/

variable (c : V116GrammarCode α) (w : List α)

/-- Lexical clauses. -/
def lexRulesC : List (Atom α × List (Atom α)) × Nat :=
  forListC (fun p : List α × α => forListC (fun q : Nat × α =>
    if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), [])], 1) else ([], 1)) (enumC w).1) c.lexical

/-- Unary clauses. -/
def unRulesC : List (Atom α × List (Atom α)) × Nat :=
  forListC (fun p : List α × List α => forListC (fun s : Nat × Nat =>
    ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) (spansC w.length).1) c.unary

/-- Binary clauses. -/
def binRulesC : List (Atom α × List (Atom α)) × Nat :=
  forListC (fun t : List α × List α × List α => forListC (fun s : Nat × Nat × Nat =>
    ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1))
    (splitsC w.length).1) c.binary

/-- All clauses. -/
def rulesOf : List (Atom α × List (Atom α)) :=
  (lexRulesC c w).1 ++ ((unRulesC c w).1 ++ (binRulesC c w).1)

/-- Rule heads (names). -/
def headsOf : List (List α) :=
  c.lexical.map Prod.fst ++ (c.unary.map Prod.fst ++ c.binary.map Prod.fst)

/-- The domain: every atom whose name is a rule head. -/
def domC : List (Atom α) × Nat :=
  forListC (fun x : List α => forListC (fun s : Nat × Nat => ([(x, s.1, s.2)], 1))
    (spansC w.length).1) (headsOf c)

/-- Does some start name derive the whole word? -/
def startTestC (chart : List (Atom α)) : List (List α) → Bool × Nat
  | [] => (false, 1)
  | x :: xs =>
      if (memC atomEqC (x, 0, w.length) chart).1 then
        (true, (memC atomEqC (x, 0, w.length) chart).2 + 1)
      else
        ((startTestC chart xs).1,
          (memC atomEqC (x, 0, w.length) chart).2 + (startTestC chart xs).2 + 1)

/-- **The costed membership test.** -/
def codeMemberC : Bool × Nat :=
  let ch := hornC atomEqC (domC c w).1 (rulesOf c w)
  let st := startTestC w ch.1 c.start
  (if w.length = 0 then c.epsilon else st.1,
    (enumC w).2 + (spansC w.length).2 + (splitsC w.length).2 + (lexRulesC c w).2 +
      (unRulesC c w).2 + (binRulesC c w).2 +
      (c.lexical.length + c.unary.length + c.binary.length + 3) +
      (domC c w).2 + ch.2 + st.2 + 1)

/-! ### Rule membership -/

theorem mem_lexRules (x : List α) (i j : Nat) (body : List (Atom α)) :
    ((x, i, j), body) ∈ (lexRulesC c w).1 ↔
      ∃ a, (x, a) ∈ c.lexical ∧ i < w.length ∧ slice w i (i + 1) = [a] ∧ j = i + 1 ∧
        body = [] := by
  unfold lexRulesC
  rw [mem_forListC]
  constructor
  · rintro ⟨p, hp, hm⟩
    rw [mem_forListC] at hm
    obtain ⟨q, hq, hm⟩ := hm
    split_ifs at hm with heq
    · simp only [List.mem_singleton, Prod.mk.injEq] at hm
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hm
      have hq' : (q.1, q.2) ∈ enumFrom 0 w := hq
      rw [mem_enumFrom] at hq'
      simp only [Nat.sub_zero] at hq'
      refine ⟨p.2, by simpa using hp, hq'.2.1, by rw [hq'.2.2, heq], rfl, rfl⟩
    · simp at hm
  · rintro ⟨a, ha, hi, hs, rfl, rfl⟩
    refine ⟨(x, a), ha, ?_⟩
    rw [mem_forListC]
    refine ⟨(i, a), ?_, ?_⟩
    · show (i, a) ∈ enumFrom 0 w
      rw [mem_enumFrom]
      simpa using ⟨hi, hs⟩
    · simp

theorem mem_unRules (x : List α) (i j : Nat) (body : List (Atom α)) :
    ((x, i, j), body) ∈ (unRulesC c w).1 ↔
      ∃ y, (x, y) ∈ c.unary ∧ i < j ∧ j ≤ w.length ∧ body = [(y, i, j)] := by
  unfold unRulesC
  rw [mem_forListC]
  constructor
  · rintro ⟨p, hp, hm⟩
    rw [mem_forListC] at hm
    obtain ⟨s, hs, hm⟩ := hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hm
    have hs' : (s.1, s.2) ∈ (spansC w.length).1 := hs
    rw [mem_spansC] at hs'
    exact ⟨p.2, by simpa using hp, hs'.1, hs'.2, rfl⟩
  · rintro ⟨y, hy, h1, h2, rfl⟩
    refine ⟨(x, y), hy, ?_⟩
    rw [mem_forListC]
    exact ⟨(i, j), (mem_spansC _ _ _).mpr ⟨h1, h2⟩, by simp⟩

theorem mem_binRules (x : List α) (i j : Nat) (body : List (Atom α)) :
    ((x, i, j), body) ∈ (binRulesC c w).1 ↔
      ∃ y z k, (x, y, z) ∈ c.binary ∧ i < k ∧ k < j ∧ j ≤ w.length ∧
        body = [(y, i, k), (z, k, j)] := by
  unfold binRulesC
  rw [mem_forListC]
  constructor
  · rintro ⟨t, ht, hm⟩
    rw [mem_forListC] at hm
    obtain ⟨s, hs, hm⟩ := hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := hm
    have hs' : (s.1, s.2.1, s.2.2) ∈ (splitsC w.length).1 := hs
    rw [mem_splitsC] at hs'
    exact ⟨t.2.1, t.2.2, s.2.1, by simpa using ht, hs'.1, hs'.2.1, hs'.2.2, rfl⟩
  · rintro ⟨y, z, k, ht, h1, h2, h3, rfl⟩
    refine ⟨(x, y, z), ht, ?_⟩
    rw [mem_forListC]
    exact ⟨(i, k, j), (mem_splitsC _ _ _ _).mpr ⟨h1, h2, h3⟩, by simp⟩

theorem mem_dom (x : List α) (i j : Nat) :
    (x, i, j) ∈ (domC c w).1 ↔ x ∈ headsOf c ∧ i < j ∧ j ≤ w.length := by
  unfold domC
  rw [mem_forListC]
  constructor
  · rintro ⟨y, hy, hm⟩
    rw [mem_forListC] at hm
    obtain ⟨s, hs, hm⟩ := hm
    simp only [List.mem_singleton, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    have hs' : (s.1, s.2) ∈ (spansC w.length).1 := hs
    rw [mem_spansC] at hs'
    exact ⟨hy, hs'⟩
  · rintro ⟨hx, h1, h2⟩
    refine ⟨x, hx, ?_⟩
    rw [mem_forListC]
    exact ⟨(i, j), (mem_spansC _ _ _).mpr ⟨h1, h2⟩, by simp⟩

/-! ### Semantics of the chart -/

theorem slice_split_of_eq {i j : Nat} (hij : i ≤ j) (hj : j ≤ w.length) {u v : List α}
    (h : slice w i j = u ++ v) :
    slice w i (i + u.length) = u ∧ slice w (i + u.length) j = v ∧ i + u.length ≤ j := by
  have hl := slice_length w hij hj
  rw [h, List.length_append] at hl
  have hk : i + u.length ≤ j := by omega
  have hs := slice_append w (i := i) (j := i + u.length) (k := j) (by omega) hk
  rw [h] at hs
  have hl2 := slice_length w (i := i) (j := i + u.length) (by omega) (by omega)
  have := List.append_inj hs (by rw [hl2]; omega)
  exact ⟨this.1, this.2, hk⟩

/-- Derived words of the code grammar are nonempty (no ε-rules). -/
theorem codeDerives_ne_nil {x : List α} {u : List α}
    (d : BinaryNullableDerives (codeGrammar c) x u) : u ≠ [] := by
  induction d with
  | terminal _ => simp
  | epsilon h => exact absurd h id
  | unit _ _ ih => exact ih
  | binary _ _ _ ihB _ => intro h; exact ihB (List.append_eq_nil_iff.mp h).1

theorem horn_sound {p : Atom α} (h : HornDerivable (rulesOf c w) p) :
    p.2.1 < p.2.2 ∧ p.2.2 ≤ w.length ∧
      BinaryNullableDerives (codeGrammar c) p.1 (slice w p.2.1 p.2.2) := by
  induction h with
  | @rule p body hm _ ih =>
      obtain ⟨x, i, j⟩ := p
      show i < j ∧ j ≤ w.length ∧ BinaryNullableDerives (codeGrammar c) x (slice w i j)
      simp only [rulesOf, List.mem_append] at hm
      rcases hm with hm | hm | hm
      · obtain ⟨a, ha, hi, hs, rfl, rfl⟩ := (mem_lexRules c w x i j body).mp hm
        refine ⟨by omega, by omega, ?_⟩
        rw [hs]
        exact BinaryNullableDerives.terminal ha
      · obtain ⟨y, hy, h1, h2, rfl⟩ := (mem_unRules c w x i j body).mp hm
        obtain ⟨_, _, d⟩ := ih (y, i, j) (by simp)
        exact ⟨h1, h2, BinaryNullableDerives.unit hy d⟩
      · obtain ⟨y, z, k, ht, h1, h2, h3, rfl⟩ := (mem_binRules c w x i j body).mp hm
        obtain ⟨_, _, dB⟩ := ih (y, i, k) (by simp)
        obtain ⟨_, _, dC⟩ := ih (z, k, j) (by simp)
        refine ⟨by omega, h3, ?_⟩
        rw [← slice_append w (le_of_lt h1) (le_of_lt h2)]
        exact BinaryNullableDerives.binary ht dB dC

theorem horn_complete {x : List α} {u : List α}
    (d : BinaryNullableDerives (codeGrammar c) x u) :
    ∀ i j, i < j → j ≤ w.length → slice w i j = u → HornDerivable (rulesOf c w) (x, i, j) := by
  induction d with
  | @terminal x a h =>
      intro i j hij hj hs
      have hl := slice_length w (le_of_lt hij) hj
      rw [hs] at hl
      simp at hl
      have hj' : j = i + 1 := by omega
      subst hj'
      refine HornDerivable.rule (body := []) ?_ (by simp)
      simp only [rulesOf, List.mem_append]
      exact Or.inl ((mem_lexRules c w x i (i + 1) []).mpr ⟨a, h, by omega, hs, rfl, rfl⟩)
  | epsilon h => exact absurd h id
  | @unit x y u h _ ih =>
      intro i j hij hj hs
      refine HornDerivable.rule (body := [(y, i, j)]) ?_ ?_
      · simp only [rulesOf, List.mem_append]
        exact Or.inr (Or.inl ((mem_unRules c w x i j _).mpr ⟨y, h, hij, hj, rfl⟩))
      · intro q hq
        simp only [List.mem_singleton] at hq
        subst hq
        exact ih i j hij hj hs
  | @binary x y z uB uC h dB dC ihB ihC =>
      intro i j hij hj hs
      obtain ⟨h1, h2, hk⟩ := slice_split_of_eq w (le_of_lt hij) hj hs
      have hB := codeDerives_ne_nil c dB
      have hC := codeDerives_ne_nil c dC
      have hBl : 0 < uB.length := List.length_pos_iff.mpr hB
      have hk2 : i + uB.length < j := by
        rcases Nat.lt_or_ge (i + uB.length) j with h | h
        · exact h
        · exfalso
          have : i + uB.length = j := by omega
          rw [this] at h2
          simp [slice] at h2
          exact hC h2
      refine HornDerivable.rule (body := [(y, i, i + uB.length), (z, i + uB.length, j)]) ?_ ?_
      · simp only [rulesOf, List.mem_append]
        exact Or.inr (Or.inr ((mem_binRules c w x i j _).mpr
          ⟨y, z, i + uB.length, h, by omega, hk2, hj, rfl⟩))
      · intro q hq
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl
        · exact ihB i (i + uB.length) (by omega) (by omega) h1
        · exact ihC (i + uB.length) j hk2 hj h2

theorem rules_heads_mem_dom : ∀ p body, (p, body) ∈ rulesOf c w → p ∈ (domC c w).1 := by
  intro p body hm
  obtain ⟨x, i, j⟩ := p
  rw [mem_dom]
  simp only [rulesOf, List.mem_append] at hm
  rcases hm with hm | hm | hm
  · obtain ⟨a, ha, hi, _, rfl, rfl⟩ := (mem_lexRules c w x i j body).mp hm
    refine ⟨?_, by omega, by omega⟩
    simp only [headsOf, List.mem_append, List.mem_map]
    exact Or.inl ⟨(x, a), ha, rfl⟩
  · obtain ⟨y, hy, h1, h2, rfl⟩ := (mem_unRules c w x i j body).mp hm
    refine ⟨?_, h1, h2⟩
    simp only [headsOf, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl ⟨(x, y), hy, rfl⟩)
  · obtain ⟨y, z, k, ht, h1, h2, h3, rfl⟩ := (mem_binRules c w x i j body).mp hm
    refine ⟨?_, by omega, h3⟩
    simp only [headsOf, List.mem_append, List.mem_map]
    exact Or.inr (Or.inr ⟨(x, y, z), ht, rfl⟩)

/-- **The chart is exactly the set of derivable spans.** -/
theorem mem_chart_iff (x : List α) (i j : Nat) :
    (x, i, j) ∈ (hornC atomEqC (domC c w).1 (rulesOf c w)).1 ↔
      i < j ∧ j ≤ w.length ∧ BinaryNullableDerives (codeGrammar c) x (slice w i j) := by
  rw [mem_hornC_iff atomEqC_correct _ _ (rules_heads_mem_dom c w)]
  constructor
  · exact horn_sound c w
  · rintro ⟨h1, h2, d⟩
    exact horn_complete c w d i j h1 h2 rfl

theorem startTestC_fst (chart : List (Atom α)) :
    ∀ xs : List (List α),
      (startTestC w chart xs).1 = true ↔ ∃ x, x ∈ xs ∧ (x, 0, w.length) ∈ chart
  | [] => by simp [startTestC]
  | x :: xs => by
      have ih := startTestC_fst chart xs
      unfold startTestC
      by_cases h : (x, 0, w.length) ∈ chart
      · have hb : (memC atomEqC (x, 0, w.length) chart).1 = true := by
          rw [memC_fst atomEqC_correct]; simpa using h
        simp only [hb, if_true, true_iff]
        exact ⟨x, by simp, h⟩
      · have hb : (memC atomEqC (x, 0, w.length) chart).1 = false := by
          rw [memC_fst atomEqC_correct]; simpa using h
        simp only [hb, Bool.false_eq_true, if_false, ih]
        constructor
        · rintro ⟨y, hy, hm⟩; exact ⟨y, by simp [hy], hm⟩
        · rintro ⟨y, hy, hm⟩
          rcases List.mem_cons.mp hy with rfl | hy
          · exact absurd hm h
          · exact ⟨y, hy, hm⟩

/-- **Correctness of the costed membership test.** -/
theorem codeMemberC_correct :
    (codeMemberC c w).1 = true ↔ w ∈ codeLanguage c := by
  show (if w.length = 0 then c.epsilon else
      (startTestC w (hornC atomEqC (domC c w).1 (rulesOf c w)).1 c.start).1) = true ↔
    ((∃ x, x ∈ c.start ∧ BinaryNullableDerives (codeGrammar c) x w) ∨
      (w = [] ∧ c.epsilon = true))
  by_cases hw : w.length = 0
  · have hw' : w = [] := List.length_eq_zero_iff.mp hw
    rw [if_pos hw]
    constructor
    · intro h; exact Or.inr ⟨hw', h⟩
    · rintro (⟨x, _, d⟩ | ⟨_, h⟩)
      · exact absurd hw' (codeDerives_ne_nil c d)
      · exact h
  · rw [if_neg hw, startTestC_fst]
    have hslice : slice w 0 w.length = w := by simp [slice]
    constructor
    · rintro ⟨x, hx, hm⟩
      rw [mem_chart_iff] at hm
      obtain ⟨_, _, d⟩ := hm
      rw [hslice] at d
      exact Or.inl ⟨x, hx, d⟩
    · rintro (⟨x, hx, d⟩ | ⟨h, _⟩)
      · refine ⟨x, hx, ?_⟩
        rw [mem_chart_iff]
        exact ⟨by omega, le_refl _, by rw [hslice]; exact d⟩
      · exact absurd (by rw [h]; rfl) hw


/-! ### Operation count -/

section Costs

theorem mono_X (a b e i j k : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (he : 1 ≤ e)
    (hi : i ≤ 3) (hj : j ≤ 7) (hk : k ≤ 1) :
    a ^ i * b ^ j * e ^ k ≤ a ^ 3 * b ^ 7 * e := by
  have h1 : a ^ i ≤ a ^ 3 := Nat.pow_le_pow_right ha hi
  have h2 : b ^ j ≤ b ^ 7 := Nat.pow_le_pow_right hb hj
  have h3 : e ^ k ≤ e := by
    calc e ^ k ≤ e ^ 1 := Nat.pow_le_pow_right he hk
      _ = e := pow_one e
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3

theorem spansC_bound (ℓ : Nat) :
    (spansC ℓ).1.length ≤ (spansC ℓ).2 ∧ (spansC ℓ).2 ≤ 10 * (ℓ + 1) ^ 2 := by
  unfold spansC
  have := forNatC_bound (fun i => forNatC (fun d => ([(i, i + d + 1)], 1)) (ℓ - i))
    (3 * ℓ + 1) ℓ (fun i _ => by
      have h := forNatC_bound (fun d => ([(i, i + d + 1)], 1)) 1 (ℓ - i)
        (fun _ _ => ⟨by simp, le_refl _⟩)
      refine ⟨h.1, le_trans h.2 ?_⟩
      have : (ℓ - i) * (2 * 1 + 1) ≤ ℓ * 3 := Nat.mul_le_mul (by omega) (le_refl _)
      omega)
  refine ⟨this.1, le_trans this.2 ?_⟩
  nlinarith

theorem splitsC_bound (ℓ : Nat) :
    (splitsC ℓ).1.length ≤ (splitsC ℓ).2 ∧ (splitsC ℓ).2 ≤ 30 * (ℓ + 1) ^ 3 := by
  unfold splitsC
  have inner : ∀ i d, (forNatC (fun e => ([(i, i + d + 1, i + d + 1 + e + 1)], 1))
      (ℓ - (i + d + 1))).1.length ≤ (forNatC (fun e => ([(i, i + d + 1, i + d + 1 + e + 1)], 1))
      (ℓ - (i + d + 1))).2 ∧ (forNatC (fun e => ([(i, i + d + 1, i + d + 1 + e + 1)], 1))
      (ℓ - (i + d + 1))).2 ≤ 3 * ℓ + 1 := by
    intro i d
    have h := forNatC_bound (fun e => ([(i, i + d + 1, i + d + 1 + e + 1)], 1)) 1
      (ℓ - (i + d + 1)) (fun _ _ => ⟨by simp, le_refl _⟩)
    refine ⟨h.1, le_trans h.2 ?_⟩
    have : (ℓ - (i + d + 1)) * (2 * 1 + 1) ≤ ℓ * 3 := Nat.mul_le_mul (by omega) (le_refl _)
    omega
  have middle : ∀ i, (forNatC (fun d => forNatC (fun e =>
      ([(i, i + d + 1, i + d + 1 + e + 1)], 1)) (ℓ - (i + d + 1))) (ℓ - i)).1.length ≤
      (forNatC (fun d => forNatC (fun e =>
      ([(i, i + d + 1, i + d + 1 + e + 1)], 1)) (ℓ - (i + d + 1))) (ℓ - i)).2 ∧
      (forNatC (fun d => forNatC (fun e =>
      ([(i, i + d + 1, i + d + 1 + e + 1)], 1)) (ℓ - (i + d + 1))) (ℓ - i)).2 ≤
        10 * (ℓ + 1) ^ 2 := by
    intro i
    have h := forNatC_bound _ (3 * ℓ + 1) (ℓ - i) (fun d _ => inner i d)
    refine ⟨h.1, le_trans h.2 ?_⟩
    have : (ℓ - i) * (2 * (3 * ℓ + 1) + 1) ≤ ℓ * (2 * (3 * ℓ + 1) + 1) :=
      Nat.mul_le_mul (by omega) (le_refl _)
    nlinarith
  have h := forNatC_bound _ (10 * (ℓ + 1) ^ 2) ℓ (fun i _ => middle i)
  refine ⟨h.1, le_trans h.2 ?_⟩
  nlinarith

/-- Size parameters of a code: every rule list has at most `C` entries. -/
structure CodeSize (c : V116GrammarCode α) (C : Nat) : Prop where
  lexical : c.lexical.length ≤ C
  unary : c.unary.length ≤ C
  binary : c.binary.length ≤ C
  start : c.start.length ≤ C

/-- Every name occurring in a rule or start entry has length at most `Λ`. -/
structure NameBound (c : V116GrammarCode α) (Λ : Nat) : Prop where
  lexical : ∀ p, p ∈ c.lexical → p.1.length ≤ Λ
  unary : ∀ p, p ∈ c.unary → p.1.length ≤ Λ ∧ p.2.length ≤ Λ
  binary : ∀ t, t ∈ c.binary → t.1.length ≤ Λ ∧ t.2.1.length ≤ Λ ∧ t.2.2.length ≤ Λ
  start : ∀ x, x ∈ c.start → x.length ≤ Λ

variable {c} {C Λ : Nat}

theorem lexRulesC_bound (hs : CodeSize c C) :
    (lexRulesC c w).1.length ≤ C * w.length ∧
    (lexRulesC c w).2 ≤ C * (6 * w.length + 3) + 1 := by
  unfold lexRulesC
  have hin : ∀ p : List α × α, (forListC (fun q : Nat × α =>
      if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), ([] : List (Atom α)))], 1) else ([], 1)) (enumC w).1).1.length ≤
      w.length ∧
      (forListC (fun q : Nat × α =>
      if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), ([] : List (Atom α)))], 1) else ([], 1)) (enumC w).1).1.length ≤
      (forListC (fun q : Nat × α =>
      if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), ([] : List (Atom α)))], 1) else ([], 1)) (enumC w).1).2 ∧
      (forListC (fun q : Nat × α =>
      if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), ([] : List (Atom α)))], 1) else ([], 1)) (enumC w).1).2 ≤
        3 * w.length + 1 := by
    intro p
    have hlen : (enumC w).1.length = w.length := enumFrom_length w 0
    have h := forListC_bound_const (fun q : Nat × α =>
      if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), ([] : List (Atom α)))], 1) else ([], 1)) 1 (enumC w).1
      (fun q _ => by split_ifs <;> simp)
    have h2 := forListC_length_le (fun q : Nat × α =>
      if p.2 = q.2 then ([((p.1, q.1, q.1 + 1), ([] : List (Atom α)))], 1) else ([], 1)) 1 (enumC w).1
      (fun q _ => by split_ifs <;> simp)
    rw [hlen] at h h2
    refine ⟨by simpa using h2, h.1, ?_⟩
    omega
  have h := forListC_bound_const _ (3 * w.length + 1) c.lexical
    (fun p _ => ⟨(hin p).2.1, (hin p).2.2⟩)
  have h2 := forListC_length_le _ w.length c.lexical (fun p _ => (hin p).1)
  have hl := hs.lexical
  constructor
  · exact le_trans h2 (Nat.mul_le_mul_right _ hl)
  · refine le_trans h.2 ?_
    have : c.lexical.length * (2 * (3 * w.length + 1) + 1) ≤ C * (6 * w.length + 3) :=
      Nat.mul_le_mul hl (by omega)
    omega

theorem unRulesC_bound (hs : CodeSize c C) :
    (unRulesC c w).1.length ≤ C * (10 * (w.length + 1) ^ 2) ∧
    (unRulesC c w).2 ≤ C * (60 * (w.length + 1) ^ 2 + 3) + 1 := by
  unfold unRulesC
  obtain ⟨hS1, hS2⟩ := spansC_bound w.length
  have hSl : (spansC w.length).1.length ≤ 10 * (w.length + 1) ^ 2 := le_trans hS1 hS2
  have hin : ∀ p : List α × List α, (forListC (fun s : Nat × Nat =>
      ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) (spansC w.length).1).1.length ≤
        10 * (w.length + 1) ^ 2 ∧
      (forListC (fun s : Nat × Nat =>
      ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) (spansC w.length).1).1.length ≤
      (forListC (fun s : Nat × Nat =>
      ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) (spansC w.length).1).2 ∧
      (forListC (fun s : Nat × Nat =>
      ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) (spansC w.length).1).2 ≤
        30 * (w.length + 1) ^ 2 + 1 := by
    intro p
    have h := forListC_bound_const (fun s : Nat × Nat =>
      ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) 1 (spansC w.length).1
      (fun _ _ => ⟨by simp, le_refl _⟩)
    have h2 := forListC_length_le (fun s : Nat × Nat =>
      ([((p.1, s.1, s.2), [(p.2, s.1, s.2)])], 1)) 1 (spansC w.length).1 (fun _ _ => by simp)
    refine ⟨by rw [Nat.mul_one] at h2; omega, h.1, by omega⟩
  have h := forListC_bound_const _ (30 * (w.length + 1) ^ 2 + 1) c.unary
    (fun p _ => ⟨(hin p).2.1, (hin p).2.2⟩)
  have h2 := forListC_length_le _ (10 * (w.length + 1) ^ 2) c.unary (fun p _ => (hin p).1)
  have hl := hs.unary
  constructor
  · exact le_trans h2 (Nat.mul_le_mul_right _ hl)
  · refine le_trans h.2 ?_
    have : c.unary.length * (2 * (30 * (w.length + 1) ^ 2 + 1) + 1) ≤
        C * (60 * (w.length + 1) ^ 2 + 3) := Nat.mul_le_mul hl (by omega)
    omega

theorem binRulesC_bound (hs : CodeSize c C) :
    (binRulesC c w).1.length ≤ C * (30 * (w.length + 1) ^ 3) ∧
    (binRulesC c w).2 ≤ C * (180 * (w.length + 1) ^ 3 + 3) + 1 := by
  unfold binRulesC
  obtain ⟨hS1, hS2⟩ := splitsC_bound w.length
  have hin : ∀ t : List α × List α × List α, (forListC (fun s : Nat × Nat × Nat =>
      ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1))
      (splitsC w.length).1).1.length ≤ 30 * (w.length + 1) ^ 3 ∧
      (forListC (fun s : Nat × Nat × Nat =>
      ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1))
      (splitsC w.length).1).1.length ≤
      (forListC (fun s : Nat × Nat × Nat =>
      ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1))
      (splitsC w.length).1).2 ∧
      (forListC (fun s : Nat × Nat × Nat =>
      ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1))
      (splitsC w.length).1).2 ≤ 90 * (w.length + 1) ^ 3 + 1 := by
    intro t
    have h := forListC_bound_const (fun s : Nat × Nat × Nat =>
      ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1)) 1
      (splitsC w.length).1 (fun _ _ => ⟨by simp, le_refl _⟩)
    have h2 := forListC_length_le (fun s : Nat × Nat × Nat =>
      ([((t.1, s.1, s.2.2), [(t.2.1, s.1, s.2.1), (t.2.2, s.2.1, s.2.2)])], 1)) 1
      (splitsC w.length).1 (fun _ _ => by simp)
    refine ⟨by rw [Nat.mul_one] at h2; omega, h.1, by omega⟩
  have h := forListC_bound_const _ (90 * (w.length + 1) ^ 3 + 1) c.binary
    (fun t _ => ⟨(hin t).2.1, (hin t).2.2⟩)
  have h2 := forListC_length_le _ (30 * (w.length + 1) ^ 3) c.binary (fun t _ => (hin t).1)
  have hl := hs.binary
  constructor
  · exact le_trans h2 (Nat.mul_le_mul_right _ hl)
  · refine le_trans h.2 ?_
    have : c.binary.length * (2 * (90 * (w.length + 1) ^ 3 + 1) + 1) ≤
        C * (180 * (w.length + 1) ^ 3 + 3) := Nat.mul_le_mul hl (by omega)
    omega

theorem headsOf_length (hs : CodeSize c C) : (headsOf c).length ≤ 3 * C := by
  simp only [headsOf, List.length_append, List.length_map]
  have := hs.lexical; have := hs.unary; have := hs.binary
  omega

theorem domC_bound (hs : CodeSize c C) :
    (domC c w).1.length ≤ 3 * C * (10 * (w.length + 1) ^ 2) ∧
    (domC c w).2 ≤ 3 * C * (60 * (w.length + 1) ^ 2 + 3) + 1 := by
  unfold domC
  obtain ⟨hS1, hS2⟩ := spansC_bound w.length
  have hin : ∀ x : List α, (forListC (fun s : Nat × Nat => ([(x, s.1, s.2)], 1))
      (spansC w.length).1).1.length ≤ 10 * (w.length + 1) ^ 2 ∧
      (forListC (fun s : Nat × Nat => ([(x, s.1, s.2)], 1))
      (spansC w.length).1).1.length ≤ (forListC (fun s : Nat × Nat => ([(x, s.1, s.2)], 1))
      (spansC w.length).1).2 ∧
      (forListC (fun s : Nat × Nat => ([(x, s.1, s.2)], 1))
      (spansC w.length).1).2 ≤ 30 * (w.length + 1) ^ 2 + 1 := by
    intro x
    have h := forListC_bound_const (fun s : Nat × Nat => ([(x, s.1, s.2)], 1)) 1
      (spansC w.length).1 (fun _ _ => ⟨by simp, le_refl _⟩)
    have h2 := forListC_length_le (fun s : Nat × Nat => ([(x, s.1, s.2)], 1)) 1
      (spansC w.length).1 (fun _ _ => by simp)
    refine ⟨by rw [Nat.mul_one] at h2; omega, h.1, by omega⟩
  have h := forListC_bound_const _ (30 * (w.length + 1) ^ 2 + 1) (headsOf c)
    (fun x _ => ⟨(hin x).2.1, (hin x).2.2⟩)
  have h2 := forListC_length_le _ (10 * (w.length + 1) ^ 2) (headsOf c) (fun x _ => (hin x).1)
  have hl := headsOf_length hs
  constructor
  · exact le_trans h2 (Nat.mul_le_mul_right _ hl)
  · refine le_trans h.2 ?_
    have : (headsOf c).length * (2 * (30 * (w.length + 1) ^ 2 + 1) + 1) ≤
        3 * C * (60 * (w.length + 1) ^ 2 + 3) := Nat.mul_le_mul hl (by omega)
    omega

theorem startTestC_snd_le (chart : List (Atom α)) (K : Nat)
    (hK : ∀ x, x ∈ c.start → (memC atomEqC (x, 0, w.length) chart).2 ≤ K) :
    ∀ xs : List (List α), (∀ x, x ∈ xs → x ∈ c.start) →
      (startTestC w chart xs).2 ≤ xs.length * (K + 1) + 1
  | [], _ => by simp [startTestC]
  | x :: xs, hx => by
      have h1 := hK x (hx x (by simp))
      have h2 := startTestC_snd_le chart K hK xs (fun y hy => hx y (List.mem_cons_of_mem _ hy))
      have e : (xs.length + 1) * (K + 1) = xs.length * (K + 1) + K + 1 := by ring
      unfold startTestC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega

/-- Atoms whose name has length at most `Λ`. -/
def AtomD (Λ : Nat) (p : Atom α) : Prop := p.1.length ≤ Λ

theorem atomEqC_bound (Λ : Nat) : CeqBound (atomEqC (α := α)) (AtomD Λ) (Λ + 3) := by
  intro p q hp _
  have := atomEqC_snd_le p q
  unfold AtomD at hp
  omega

theorem rules_atomD (hn : NameBound c Λ) :
    ∀ r, r ∈ rulesOf c w → AtomD Λ r.1 ∧ ∀ y, y ∈ r.2 → AtomD Λ y := by
  intro r hr
  obtain ⟨⟨x, i, j⟩, body⟩ := r
  simp only [rulesOf, List.mem_append] at hr
  rcases hr with hm | hm | hm
  · obtain ⟨a, ha, _, _, rfl, rfl⟩ := (mem_lexRules c w x i j body).mp hm
    exact ⟨hn.lexical _ ha, by simp⟩
  · obtain ⟨y, hy, _, _, rfl⟩ := (mem_unRules c w x i j body).mp hm
    have := hn.unary _ hy
    refine ⟨this.1, ?_⟩
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact this.2
  · obtain ⟨y, z, k, ht, _, _, _, rfl⟩ := (mem_binRules c w x i j body).mp hm
    have := hn.binary _ ht
    refine ⟨this.1, ?_⟩
    intro q hq
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact this.2.1
    · exact this.2.2

theorem rules_body_le_two :
    ∀ r, r ∈ rulesOf c w → r.2.length ≤ 2 := by
  intro r hr
  obtain ⟨⟨x, i, j⟩, body⟩ := r
  simp only [rulesOf, List.mem_append] at hr
  rcases hr with hm | hm | hm
  · obtain ⟨_, _, _, _, _, rfl⟩ := (mem_lexRules c w x i j body).mp hm; simp
  · obtain ⟨_, _, _, _, rfl⟩ := (mem_unRules c w x i j body).mp hm; simp
  · obtain ⟨_, _, _, _, _, _, _, rfl⟩ := (mem_binRules c w x i j body).mp hm; simp

theorem dom_atomD (hn : NameBound c Λ) : ∀ p, p ∈ (domC c w).1 → AtomD Λ p := by
  intro p hp
  obtain ⟨x, i, j⟩ := p
  rw [mem_dom] at hp
  have hx := hp.1
  simp only [headsOf, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · exact hn.lexical q hq
  · exact (hn.unary q hq).1
  · exact (hn.binary q hq).1

/-- **Operation count of the costed membership test**:
`≤ 2·10⁶ · (C+1)³ · (|w|+1)⁷ · (Λ+4)`. -/
theorem codeMemberC_cost_le (hs : CodeSize c C) (hn : NameBound c Λ) :
    (codeMemberC c w).2 ≤
      2000000 * ((C + 1) ^ 3 * (w.length + 1) ^ 7 * (Λ + 4)) := by
  obtain ⟨_, hSp⟩ := spansC_bound w.length
  obtain ⟨_, hSl⟩ := splitsC_bound w.length
  obtain ⟨hLx1, hLx2⟩ := lexRulesC_bound w hs
  obtain ⟨hU1, hU2⟩ := unRulesC_bound w hs
  obtain ⟨hB1, hB2⟩ := binRulesC_bound w hs
  obtain ⟨hD1, hD2⟩ := domC_bound w hs
  have hat := rules_atomD w hn
  have hH := hornC_cost_le (atomEqC_bound Λ) (domC c w).1 (rulesOf c w) (dom_atomD w hn)
    (fun r hr => (hat r hr).1) (fun r hr => (hat r hr).2)
  have hHl := hornC_length_le (atomEqC_bound Λ) (domC c w).1 (rulesOf c w) (dom_atomD w hn)
    (fun r hr => (hat r hr).1) (fun r hr => (hat r hr).2)
  -- rule measure
  have hRl : (rulesOf c w).length ≤ C * w.length + C * (10 * (w.length + 1) ^ 2) + C * (30 * (w.length + 1) ^ 3) := by
    simp only [rulesOf, List.length_append]; omega
  have hBody : bodySize (rulesOf c w) ≤ (rulesOf c w).length * 2 := by
    unfold bodySize
    exact sum_map_const_le _ _ 2 (fun r hr => rules_body_le_two w r hr)
  have hRM : ruleMeasure (rulesOf c w) ≤ 3 * (C * w.length + C * (10 * (w.length + 1) ^ 2) +
      C * (30 * (w.length + 1) ^ 3)) + 1 := by
    unfold ruleMeasure; omega
  -- start test
  have hST := startTestC_snd_le w (hornC atomEqC (domC c w).1 (rulesOf c w)).1
    ((3 * C * (10 * (w.length + 1) ^ 2)) * (Λ + 3 + 1) + 1) (fun x hx => by
      have := memC_snd_le' (atomEqC_bound Λ) (x, 0, w.length) (hn.start x hx)
        (hornC atomEqC (domC c w).1 (rulesOf c w)).1
        (fun y hy => dom_atomD w hn y (hornC_sub_dom (atomEqC_bound Λ) _ _ (dom_atomD w hn)
          (fun r hr => (hat r hr).1) (fun r hr => (hat r hr).2) y hy))
        (le_trans hHl hD1)
      exact this) c.start (fun x hx => hx)
  have hstart := hs.start
  show (enumC w).2 + (spansC w.length).2 + (splitsC w.length).2 + (lexRulesC c w).2 +
      (unRulesC c w).2 + (binRulesC c w).2 +
      (c.lexical.length + c.unary.length + c.binary.length + 3) +
      (domC c w).2 + (hornC atomEqC (domC c w).1 (rulesOf c w)).2 +
      (startTestC w (hornC atomEqC (domC c w).1 (rulesOf c w)).1 c.start).2 + 1 ≤ _
  -- monomials
  set a := C + 1 with ha
  set b := w.length + 1 with hb
  set e := Λ + 4 with he
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have he1 : 1 ≤ e := by omega
  set X := a ^ 3 * b ^ 7 * e with hX
  have m010 : b ≤ X := by
    have := mono_X a b e 0 1 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m020 : b ^ 2 ≤ X := by
    have := mono_X a b e 0 2 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m030 : b ^ 3 ≤ X := by
    have := mono_X a b e 0 3 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m110 : a * b ≤ X := by
    have := mono_X a b e 1 1 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m120 : a * b ^ 2 ≤ X := by
    have := mono_X a b e 1 2 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m130 : a * b ^ 3 ≤ X := by
    have := mono_X a b e 1 3 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m100 : a ≤ X := by
    have := mono_X a b e 1 0 0 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  have m221 : a ^ 2 * b ^ 2 * e ≤ X := by
    have := mono_X a b e 2 2 1 ha1 hb1 he1 (by omega) (by omega) (by omega)
    simpa using this
  -- component bounds
  have c1 : (enumC w).2 ≤ X := by show w.length + 1 ≤ X; omega
  have c2 : (spansC w.length).2 ≤ 10 * X := by omega
  have c3 : (splitsC w.length).2 ≤ 30 * X := by omega
  have c4 : (lexRulesC c w).2 ≤ 10 * X := by
    have : C * (6 * w.length + 3) ≤ 6 * (a * b) := by
      calc C * (6 * w.length + 3) ≤ a * (6 * b) := Nat.mul_le_mul (by omega) (by omega)
        _ = 6 * (a * b) := by ring
    omega
  have c5 : (unRulesC c w).2 ≤ 70 * X := by
    have : C * (60 * b ^ 2 + 3) ≤ 63 * (a * b ^ 2) := by
      have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb1
      calc C * (60 * b ^ 2 + 3) ≤ a * (63 * b ^ 2) := Nat.mul_le_mul (by omega) (by omega)
        _ = 63 * (a * b ^ 2) := by ring
    omega
  have c6 : (binRulesC c w).2 ≤ 190 * X := by
    have : C * (180 * b ^ 3 + 3) ≤ 183 * (a * b ^ 3) := by
      have hb3 : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
      calc C * (180 * b ^ 3 + 3) ≤ a * (183 * b ^ 3) := Nat.mul_le_mul (by omega) (by omega)
        _ = 183 * (a * b ^ 3) := by ring
    omega
  have c7 : c.lexical.length + c.unary.length + c.binary.length + 3 ≤ 6 * X := by
    have := hs.lexical; have := hs.unary; have := hs.binary
    omega
  have c8 : (domC c w).2 ≤ 200 * X := by
    have : 3 * C * (60 * b ^ 2 + 3) ≤ 189 * (a * b ^ 2) := by
      have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb1
      calc 3 * C * (60 * b ^ 2 + 3) ≤ 3 * a * (63 * b ^ 2) :=
            Nat.mul_le_mul (by omega) (by omega)
        _ = 189 * (a * b ^ 2) := by ring
    omega
  have c9 : (hornC atomEqC (domC c w).1 (rulesOf c w)).2 ≤ 1000000 * X := by
    refine le_trans hH ?_
    have hd : (domC c w).1.length + 1 ≤ 31 * (a * b ^ 2) := by
      have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb1
      have : 3 * C * (10 * b ^ 2) ≤ 30 * (a * b ^ 2) := by
        calc 3 * C * (10 * b ^ 2) ≤ 3 * a * (10 * b ^ 2) :=
              Nat.mul_le_mul (by omega) (by omega)
          _ = 30 * (a * b ^ 2) := by ring
      have : 1 ≤ a * b ^ 2 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      omega
    have hr : ruleMeasure (rulesOf c w) ≤ 124 * (a * b ^ 3) := by
      have hb3 : 1 ≤ b ^ 3 := Nat.one_le_pow _ _ hb1
      have h1 : C * w.length ≤ a * b ^ 3 := by
        calc C * w.length ≤ a * b := Nat.mul_le_mul (by omega) (by omega)
          _ ≤ a * b ^ 3 := Nat.mul_le_mul_left _ (by
              calc b = b ^ 1 := (pow_one b).symm
                _ ≤ b ^ 3 := Nat.pow_le_pow_right hb1 (by omega))
      have h2 : C * (10 * b ^ 2) ≤ 10 * (a * b ^ 3) := by
        calc C * (10 * b ^ 2) ≤ a * (10 * b ^ 3) := Nat.mul_le_mul (by omega)
              (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hb1 (by omega)))
          _ = 10 * (a * b ^ 3) := by ring
      have h3 : C * (30 * b ^ 3) ≤ 30 * (a * b ^ 3) := by
        calc C * (30 * b ^ 3) ≤ a * (30 * b ^ 3) := Nat.mul_le_mul (by omega) (le_refl _)
          _ = 30 * (a * b ^ 3) := by ring
      have : 1 ≤ a * b ^ 3 := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      omega
    calc 8 * ((domC c w).1.length + 1) ^ 2 * ruleMeasure (rulesOf c w) * (Λ + 3 + 1)
        ≤ 8 * (31 * (a * b ^ 2)) ^ 2 * (124 * (a * b ^ 3)) * e := by
          gcongr
      _ = 953312 * X := by rw [hX]; ring
      _ ≤ 1000000 * X := by omega
  have c10 : (startTestC w (hornC atomEqC (domC c w).1 (rulesOf c w)).1 c.start).2 ≤
      100 * X := by
    refine le_trans hST ?_
    have h1 : 3 * C * (10 * b ^ 2) * e + 1 + 1 ≤ 32 * (a * b ^ 2 * e) := by
      have : 3 * C * (10 * b ^ 2) * e ≤ 30 * (a * b ^ 2 * e) := by
        calc 3 * C * (10 * b ^ 2) * e ≤ 3 * a * (10 * b ^ 2) * e := by
              gcongr; omega
          _ = 30 * (a * b ^ 2 * e) := by ring
      have hb2 : 1 ≤ b ^ 2 := Nat.one_le_pow _ _ hb1
      have : 1 ≤ a * b ^ 2 * e := Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega)) (by omega))
      omega
    have h2 : c.start.length * (3 * C * (10 * b ^ 2) * e + 1 + 1) ≤
        32 * (a ^ 2 * b ^ 2 * e) := by
      calc c.start.length * (3 * C * (10 * b ^ 2) * e + 1 + 1)
          ≤ a * (32 * (a * b ^ 2 * e)) := Nat.mul_le_mul (by omega) h1
        _ = 32 * (a ^ 2 * b ^ 2 * e) := by ring
    have : 1 ≤ X := le_trans hb1 m010
    omega
  have : 1 ≤ X := le_trans hb1 m010
  omega

end Costs

end CodeCYK
end TCS1
end LeanCfgProject
