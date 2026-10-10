import LeanCfgProject.TCS1.V135CostedPrimitives
import Mathlib.Data.Finset.Card

/-!
# TCS #1 v144: a step-counted Horn-clause closure engine

This is the fixed-point engine used by every closure stage of the executable
SSBNF normalizer (nullable states, unit reachability, productive states,
reachable states).

**Input.**  A list `dom` of atoms (the domain) and a list `rules` of Horn
clauses `(head, body)`.  Every head is assumed to occur in `dom`.

**Algorithm.**  Starting from `marked = []`, one round computes

* `heads` := the heads of all rules whose body is contained in `marked`
  (one scan of all rules; each body atom is looked up in `marked`);
* `marked'` := the atoms of `dom` that occur in `heads`
  (one scan of `dom`; each atom is looked up in `heads`).

The engine performs `dom.length + 1` rounds.

**Cost model.**  The same as `V135CostedPrimitives`: values and step counts
are produced by the same recursion.  Atom equality is a *parameter*
`ceq : σ → σ → Bool × Nat` returning the decision and its own step count, so
that comparing structured atoms (for example suffix states, which are lists)
is charged per cell by the caller's comparison function.  Every list cell
visited or created and every loop iteration costs one step.  No `Finset`
operation is executed: `Finset` appears only in the *proof* that
`dom.length + 1` rounds suffice.

**Results.**
* `mem_hornC_iff`: the output is exactly the set of atoms derivable by the
  Horn clauses (`HornDerivable`).
* `hornC_cost_le`: at most `8 · (|dom| + 1)² · (|rules| + Σ|body| + 1) · (E + 1)`
  steps, where `E` bounds one atom comparison.
-/

namespace LeanCfgProject
namespace TCS1
namespace Horn

universe u

variable {σ : Type u} [DecidableEq σ]

/-- Atoms derivable by a finite list of Horn clauses. -/
inductive HornDerivable (rules : List (σ × List σ)) : σ → Prop
  | rule {x : σ} {body : List σ} :
      (x, body) ∈ rules →
      (∀ y, y ∈ body → HornDerivable rules y) →
      HornDerivable rules x

/-- Costed equality: the first component must be the decision. -/
def CeqCorrect (ceq : σ → σ → Bool × Nat) : Prop :=
  ∀ x y, (ceq x y).1 = decide (x = y)

/-- Uniform bound `E` on comparisons between atoms satisfying `D`. -/
def CeqBound (ceq : σ → σ → Bool × Nat) (D : σ → Prop) (E : Nat) : Prop :=
  ∀ x y, D x → D y → (ceq x y).2 ≤ E

section Defs

variable (ceq : σ → σ → Bool × Nat)

/-- Costed list membership. -/
def memC (x : σ) : List σ → Bool × Nat
  | [] => (false, 1)
  | y :: l =>
      if (ceq x y).1 then (true, (ceq x y).2 + 1)
      else ((memC x l).1, (ceq x y).2 + (memC x l).2 + 1)

/-- Costed test `body ⊆ marked`. -/
def allMemC (marked : List σ) : List σ → Bool × Nat
  | [] => (true, 1)
  | y :: b =>
      if (memC ceq y marked).1 then
        ((allMemC marked b).1, (memC ceq y marked).2 + (allMemC marked b).2 + 1)
      else (false, (memC ceq y marked).2 + 1)

/-- Heads of the rules whose bodies are contained in `marked`. -/
def headsC (marked : List σ) : List (σ × List σ) → List σ × Nat
  | [] => ([], 1)
  | r :: rs =>
      if (allMemC ceq marked r.2).1 then
        (r.1 :: (headsC marked rs).1,
          (allMemC ceq marked r.2).2 + (headsC marked rs).2 + 1)
      else
        ((headsC marked rs).1,
          (allMemC ceq marked r.2).2 + (headsC marked rs).2 + 1)

/-- Atoms of `dom` occurring in `H`. -/
def filterMemC (H : List σ) : List σ → List σ × Nat
  | [] => ([], 1)
  | x :: d =>
      if (memC ceq x H).1 then
        (x :: (filterMemC H d).1, (memC ceq x H).2 + (filterMemC H d).2 + 1)
      else
        ((filterMemC H d).1, (memC ceq x H).2 + (filterMemC H d).2 + 1)

/-- One round of the closure. -/
def roundC (dom : List σ) (rules : List (σ × List σ)) (marked : List σ) :
    List σ × Nat :=
  ((filterMemC ceq (headsC ceq marked rules).1 dom).1,
    (headsC ceq marked rules).2 +
      (filterMemC ceq (headsC ceq marked rules).1 dom).2 + 1)

/-- `k` rounds from the empty marking. -/
def iterC (dom : List σ) (rules : List (σ × List σ)) : Nat → List σ × Nat
  | 0 => ([], 1)
  | k + 1 =>
      ((roundC ceq dom rules (iterC dom rules k).1).1,
        (iterC dom rules k).2 + (roundC ceq dom rules (iterC dom rules k).1).2 + 1)

/-- The closure engine: `|dom| + 1` rounds. -/
def hornC (dom : List σ) (rules : List (σ × List σ)) : List σ × Nat :=
  iterC ceq dom rules (dom.length + 1)

end Defs

/-- Total body size of a rule list. -/
def bodySize (rules : List (σ × List σ)) : Nat :=
  (rules.map (fun r => r.2.length)).sum

section Values

variable {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq)
include hc

theorem memC_fst (x : σ) : ∀ l : List σ, (memC ceq x l).1 = decide (x ∈ l)
  | [] => by simp [memC]
  | y :: l => by
      have hxy := hc x y
      by_cases h : x = y
      · subst h
        have : (ceq x x).1 = true := by simp [hxy]
        simp [memC, this]
      · have : (ceq x y).1 = false := by simp [hxy, h]
        simp [memC, this, memC_fst x l, h]

theorem allMemC_fst (marked : List σ) :
    ∀ b : List σ, (allMemC ceq marked b).1 = decide (∀ y, y ∈ b → y ∈ marked)
  | [] => by simp [allMemC]
  | y :: b => by
      by_cases h : y ∈ marked
      · have : (memC ceq y marked).1 = true := by simp [memC_fst hc, h]
        simp [allMemC, this, allMemC_fst marked b, h]
      · have : (memC ceq y marked).1 = false := by simp [memC_fst hc, h]
        simp [allMemC, this, h]

theorem mem_headsC (marked : List σ) (x : σ) :
    ∀ rules : List (σ × List σ),
      x ∈ (headsC ceq marked rules).1 ↔
        ∃ body, (x, body) ∈ rules ∧ ∀ y, y ∈ body → y ∈ marked
  | [] => by simp [headsC]
  | r :: rs => by
      have ih := mem_headsC marked x rs
      by_cases h : ∀ y, y ∈ r.2 → y ∈ marked
      · have hb : (allMemC ceq marked r.2).1 = true := by
          rw [allMemC_fst hc]; exact decide_eq_true h
        have hh : (headsC ceq marked (r :: rs)).1 = r.1 :: (headsC ceq marked rs).1 := by
          simp [headsC, hb]
        rw [hh, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨body, hm, hall⟩)
          · exact ⟨r.2, by simp, h⟩
          · exact ⟨body, List.mem_cons_of_mem _ hm, hall⟩
        · rintro ⟨body, hm, hall⟩
          rcases List.mem_cons.mp hm with he | hm
          · left; rw [← he]
          · right; exact ⟨body, hm, hall⟩
      · have hb : (allMemC ceq marked r.2).1 = false := by
          rw [allMemC_fst hc]; exact decide_eq_false h
        have hh : (headsC ceq marked (r :: rs)).1 = (headsC ceq marked rs).1 := by
          simp [headsC, hb]
        rw [hh, ih]
        constructor
        · rintro ⟨body, hm, hall⟩
          exact ⟨body, List.mem_cons_of_mem _ hm, hall⟩
        · rintro ⟨body, hm, hall⟩
          rcases List.mem_cons.mp hm with he | hm
          · exact absurd (by rw [← he]; exact hall) h
          · exact ⟨body, hm, hall⟩

theorem mem_filterMemC (H : List σ) (x : σ) :
    ∀ dom : List σ, x ∈ (filterMemC ceq H dom).1 ↔ x ∈ dom ∧ x ∈ H
  | [] => by simp [filterMemC]
  | z :: d => by
      have ih := mem_filterMemC H x d
      by_cases h : z ∈ H
      · have hb : (memC ceq z H).1 = true := by simp [memC_fst hc, h]
        simp only [filterMemC, hb, if_true, List.mem_cons, ih]
        constructor
        · rintro (rfl | ⟨h1, h2⟩)
          · exact ⟨Or.inl rfl, h⟩
          · exact ⟨Or.inr h1, h2⟩
        · rintro ⟨rfl | h1, h2⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨h1, h2⟩
      · have hb : (memC ceq z H).1 = false := by simp [memC_fst hc, h]
        simp only [filterMemC, hb, Bool.false_eq_true, if_false, ih, List.mem_cons]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨Or.inr h1, h2⟩
        · rintro ⟨rfl | h1, h2⟩
          · exact absurd h2 h
          · exact ⟨h1, h2⟩

variable (dom : List σ) (rules : List (σ × List σ))

theorem mem_iterC_zero (x : σ) : x ∉ (iterC ceq dom rules 0).1 := by
  simp [iterC]

theorem mem_iterC_succ (k : Nat) (x : σ) :
    x ∈ (iterC ceq dom rules (k + 1)).1 ↔
      x ∈ dom ∧ ∃ body, (x, body) ∈ rules ∧
        ∀ y, y ∈ body → y ∈ (iterC ceq dom rules k).1 := by
  show x ∈ (filterMemC ceq (headsC ceq _ rules).1 dom).1 ↔ _
  rw [mem_filterMemC hc, mem_headsC hc]

theorem iterC_sub_dom (k : Nat) (x : σ) (h : x ∈ (iterC ceq dom rules k).1) :
    x ∈ dom := by
  cases k with
  | zero => exact absurd h (mem_iterC_zero hc dom rules x)
  | succ k => exact ((mem_iterC_succ hc dom rules k x).mp h).1

theorem iterC_mono_succ :
    ∀ (k : Nat) (x : σ), x ∈ (iterC ceq dom rules k).1 →
      x ∈ (iterC ceq dom rules (k + 1)).1
  | 0, x, h => absurd h (mem_iterC_zero hc dom rules x)
  | k + 1, x, h => by
      rw [mem_iterC_succ hc] at h ⊢
      obtain ⟨hd, body, hm, hall⟩ := h
      exact ⟨hd, body, hm, fun y hy => iterC_mono_succ k y (hall y hy)⟩

theorem iterC_mono {k j : Nat} (hkj : k ≤ j) (x : σ)
    (h : x ∈ (iterC ceq dom rules k).1) : x ∈ (iterC ceq dom rules j).1 := by
  induction hkj with
  | refl => exact h
  | step _ ih => exact iterC_mono_succ hc dom rules _ x ih

/-- Once two consecutive rounds agree, the marking never changes again. -/
theorem iterC_stable {k : Nat}
    (hk : ∀ x, x ∈ (iterC ceq dom rules k).1 ↔ x ∈ (iterC ceq dom rules (k + 1)).1) :
    ∀ j, k ≤ j → ∀ x,
      (x ∈ (iterC ceq dom rules j).1 ↔ x ∈ (iterC ceq dom rules k).1) := by
  intro j hkj
  induction hkj with
  | refl => intro x; exact Iff.rfl
  | @step j _ ih =>
      intro x
      rw [mem_iterC_succ hc]
      rw [hk x, mem_iterC_succ hc]
      constructor
      · rintro ⟨hd, body, hm, hall⟩
        exact ⟨hd, body, hm, fun y hy => (ih y).mp (hall y hy)⟩
      · rintro ⟨hd, body, hm, hall⟩
        exact ⟨hd, body, hm, fun y hy => (ih y).mpr (hall y hy)⟩

/-- The marked atoms after `k` rounds, as a finset (used only in proofs). -/
noncomputable def markedFinset (k : Nat) : Finset σ :=
  dom.toFinset.filter (fun x => x ∈ (iterC ceq dom rules k).1)

theorem mem_markedFinset (k : Nat) (x : σ) :
    x ∈ markedFinset (ceq := ceq) dom rules k ↔ x ∈ (iterC ceq dom rules k).1 := by
  unfold markedFinset
  rw [Finset.mem_filter, List.mem_toFinset]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨iterC_sub_dom hc dom rules k x h, h⟩

theorem markedFinset_card_le (k : Nat) :
    (markedFinset (ceq := ceq) dom rules k).card ≤ dom.length :=
  le_trans (Finset.card_filter_le _ _) (List.toFinset_card_le dom)

theorem markedFinset_count :
    ∀ k : Nat,
      (∃ j, j < k ∧
          markedFinset (ceq := ceq) dom rules j =
            markedFinset (ceq := ceq) dom rules (j + 1)) ∨
        k ≤ (markedFinset (ceq := ceq) dom rules k).card
  | 0 => Or.inr (Nat.zero_le _)
  | k + 1 => by
      rcases markedFinset_count k with ⟨j, hj, he⟩ | hle
      · exact Or.inl ⟨j, by omega, he⟩
      · by_cases he :
            markedFinset (ceq := ceq) dom rules k =
              markedFinset (ceq := ceq) dom rules (k + 1)
        · exact Or.inl ⟨k, by omega, he⟩
        · right
          have hsub : markedFinset (ceq := ceq) dom rules k ⊆
              markedFinset (ceq := ceq) dom rules (k + 1) := by
            intro x hx
            rw [mem_markedFinset hc] at hx ⊢
            exact iterC_mono_succ hc dom rules k x hx
          have hss : markedFinset (ceq := ceq) dom rules k ⊂
              markedFinset (ceq := ceq) dom rules (k + 1) :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hsub, he⟩
          have := Finset.card_lt_card hss
          omega

/-- After `|dom| + 1` rounds every later marking is contained in the result. -/
theorem iterC_final (m : Nat) (x : σ) (h : x ∈ (iterC ceq dom rules m).1) :
    x ∈ (hornC ceq dom rules).1 := by
  unfold hornC
  rcases markedFinset_count hc dom rules (dom.length + 1) with ⟨j, hj, he⟩ | hle
  · have hk : ∀ y, y ∈ (iterC ceq dom rules j).1 ↔
        y ∈ (iterC ceq dom rules (j + 1)).1 := by
      intro y
      rw [← mem_markedFinset hc, ← mem_markedFinset hc, he]
    by_cases hm : m ≤ dom.length + 1
    · exact iterC_mono hc dom rules hm x h
    · have h1 := (iterC_stable hc dom rules hk m (by omega) x).mp h
      exact (iterC_stable hc dom rules hk (dom.length + 1) (by omega) x).mpr h1
  · have := markedFinset_card_le hc dom rules (dom.length + 1)
    omega

theorem iterC_sound :
    ∀ (k : Nat) (x : σ), x ∈ (iterC ceq dom rules k).1 → HornDerivable rules x
  | 0, x, h => absurd h (mem_iterC_zero hc dom rules x)
  | k + 1, x, h => by
      obtain ⟨_, body, hm, hall⟩ := (mem_iterC_succ hc dom rules k x).mp h
      exact HornDerivable.rule hm (fun y hy => iterC_sound k y (hall y hy))

/-- **Correctness of the closure engine.** -/
theorem mem_hornC_iff
    (hdom : ∀ x body, (x, body) ∈ rules → x ∈ dom) (x : σ) :
    x ∈ (hornC ceq dom rules).1 ↔ HornDerivable rules x := by
  constructor
  · exact iterC_sound hc dom rules _ x
  · intro hd
    induction hd with
    | @rule x body hm _ ih =>
        apply iterC_final hc dom rules (dom.length + 1 + 1) x
        rw [mem_iterC_succ hc]
        exact ⟨hdom x body hm, body, hm, ih⟩

end Values

/-- Arithmetic behind the per-round bound. -/
theorem round_arith (B K R E h f : Nat)
    (hH : h ≤ B * (K * (E + 1) + 2) + 2 * R + 1)
    (hF : f ≤ K * (R * (E + 1) + 2) + 1) :
    h + f + 1 ≤ 6 * (K + 1) * (R + B + 1) * (E + 1) := by
  have hBK : B * K ≤ (K + 1) * (R + B + 1) :=
    calc B * K ≤ (R + B + 1) * (K + 1) := Nat.mul_le_mul (by omega) (by omega)
      _ = (K + 1) * (R + B + 1) := Nat.mul_comm _ _
  have hKR : K * R ≤ (K + 1) * (R + B + 1) := Nat.mul_le_mul (by omega) (by omega)
  have hBK' : B * K * (E + 1) ≤ (K + 1) * (R + B + 1) * (E + 1) :=
    Nat.mul_le_mul_right _ hBK
  have hKR' : K * R * (E + 1) ≤ (K + 1) * (R + B + 1) * (E + 1) :=
    Nat.mul_le_mul_right _ hKR
  have hlin : 2 * B + 2 * R + 2 * K + 3 ≤ 4 * ((K + 1) * (R + B + 1) * (E + 1)) := by
    have h1 : K + 1 ≤ (K + 1) * (R + B + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h1' : R + B + 1 ≤ (K + 1) * (R + B + 1) := Nat.le_mul_of_pos_left _ (by omega)
    have h2 : (K + 1) * (R + B + 1) ≤ (K + 1) * (R + B + 1) * (E + 1) :=
      Nat.le_mul_of_pos_right _ (by omega)
    omega
  have e1 : B * (K * (E + 1) + 2) = B * K * (E + 1) + 2 * B := by ring
  have e2 : K * (R * (E + 1) + 2) = K * R * (E + 1) + 2 * K := by ring
  have e3 : 6 * (K + 1) * (R + B + 1) * (E + 1) =
      6 * ((K + 1) * (R + B + 1) * (E + 1)) := by ring
  rw [e1] at hH
  rw [e2] at hF
  rw [e3]
  omega

/-- Every computed head is the head of some rule (no correctness hypothesis). -/
theorem headsC_sub (ceq : σ → σ → Bool × Nat) (marked : List σ) :
    ∀ (rules : List (σ × List σ)) (y : σ),
      y ∈ (headsC ceq marked rules).1 → ∃ r, r ∈ rules ∧ r.1 = y
  | [], y, h => by simp [headsC] at h
  | r :: rs, y, h => by
      unfold headsC at h
      split_ifs at h
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨r, by simp, rfl⟩
        · obtain ⟨r', hr', he⟩ := headsC_sub ceq marked rs y h
          exact ⟨r', List.mem_cons_of_mem _ hr', he⟩
      · obtain ⟨r', hr', he⟩ := headsC_sub ceq marked rs y h
        exact ⟨r', List.mem_cons_of_mem _ hr', he⟩

section Costs

variable {ceq : σ → σ → Bool × Nat} {D : σ → Prop} {E : Nat}
  (hb : CeqBound ceq D E)
include hb

theorem memC_snd_le (x : σ) (hx : D x) :
    ∀ l : List σ, (∀ y, y ∈ l → D y) → (memC ceq x l).2 ≤ l.length * (E + 1) + 1
  | [], _ => by simp [memC]
  | y :: l, hl => by
      have h1 := hb x y hx (hl y (by simp))
      have h2 := memC_snd_le x hx l (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      have e : (l.length + 1) * (E + 1) = l.length * (E + 1) + E + 1 := by ring
      unfold memC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega

theorem memC_snd_le' (x : σ) (hx : D x) (l : List σ) (hl : ∀ y, y ∈ l → D y)
    {K : Nat} (hK : l.length ≤ K) : (memC ceq x l).2 ≤ K * (E + 1) + 1 := by
  have := memC_snd_le hb x hx l hl
  have : l.length * (E + 1) ≤ K * (E + 1) := Nat.mul_le_mul_right _ hK
  omega

theorem allMemC_snd_le (marked : List σ) (hm : ∀ y, y ∈ marked → D y)
    {K : Nat} (hK : marked.length ≤ K) :
    ∀ b : List σ, (∀ y, y ∈ b → D y) →
      (allMemC ceq marked b).2 ≤ b.length * (K * (E + 1) + 2) + 1
  | [], _ => by simp [allMemC]
  | y :: b, hbD => by
      have h1 := memC_snd_le' hb y (hbD y (by simp)) marked hm hK
      have h2 := allMemC_snd_le marked hm hK b
        (fun z hz => hbD z (List.mem_cons_of_mem _ hz))
      have e : (b.length + 1) * (K * (E + 1) + 2) =
          b.length * (K * (E + 1) + 2) + K * (E + 1) + 2 := by ring
      unfold allMemC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega

theorem headsC_bound (marked : List σ) (hm : ∀ y, y ∈ marked → D y)
    {K : Nat} (hK : marked.length ≤ K) :
    ∀ rules : List (σ × List σ),
      (∀ r, r ∈ rules → ∀ y, y ∈ r.2 → D y) →
      (headsC ceq marked rules).1.length ≤ rules.length ∧
      (headsC ceq marked rules).2 ≤
        bodySize rules * (K * (E + 1) + 2) + 2 * rules.length + 1
  | [], _ => by simp [headsC, bodySize]
  | r :: rs, hr => by
      obtain ⟨ih1, ih2⟩ := headsC_bound marked hm hK rs
        (fun r' hr' => hr r' (List.mem_cons_of_mem _ hr'))
      have h1 := allMemC_snd_le hb marked hm hK r.2 (hr r (by simp))
      have hbs : bodySize (r :: rs) = r.2.length + bodySize rs := by
        simp [bodySize]
      have e : (r.2.length + bodySize rs) * (K * (E + 1) + 2) =
          r.2.length * (K * (E + 1) + 2) + bodySize rs * (K * (E + 1) + 2) := by ring
      unfold headsC
      split_ifs
      · simp only [List.length_cons]; rw [hbs, e]; omega
      · simp only [List.length_cons]; rw [hbs, e]; omega

theorem filterMemC_bound (H : List σ) (hH : ∀ y, y ∈ H → D y)
    {R : Nat} (hR : H.length ≤ R) :
    ∀ dom : List σ, (∀ y, y ∈ dom → D y) →
      (filterMemC ceq H dom).1.length ≤ dom.length ∧
      (∀ y, y ∈ (filterMemC ceq H dom).1 → y ∈ dom) ∧
      (filterMemC ceq H dom).2 ≤ dom.length * (R * (E + 1) + 2) + 1
  | [], _ => by simp [filterMemC]
  | z :: d, hd => by
      obtain ⟨ih1, ih2, ih3⟩ := filterMemC_bound H hH hR d
        (fun y hy => hd y (List.mem_cons_of_mem _ hy))
      have h1 := memC_snd_le' hb z (hd z (by simp)) H hH hR
      have e : (d.length + 1) * (R * (E + 1) + 2) =
          d.length * (R * (E + 1) + 2) + R * (E + 1) + 2 := by ring
      unfold filterMemC
      split_ifs
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · simp
          · exact List.mem_cons_of_mem _ (ih2 y hy)
        · simp only [List.length_cons]; rw [e]; omega
      · refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · intro y hy; exact List.mem_cons_of_mem _ (ih2 y hy)
        · simp only [List.length_cons]; rw [e]; omega

variable (dom : List σ) (rules : List (σ × List σ))

/-- The rule-side size measure `|rules| + Σ|body| + 1`. -/
def ruleMeasure : Nat := rules.length + bodySize rules + 1

theorem roundC_bound (hdomD : ∀ y, y ∈ dom → D y)
    (hrH : ∀ r, r ∈ rules → D r.1)
    (hrD : ∀ r, r ∈ rules → ∀ y, y ∈ r.2 → D y)
    (marked : List σ) (hm : ∀ y, y ∈ marked → y ∈ dom)
    (hmK : marked.length ≤ dom.length) :
    (∀ y, y ∈ (roundC ceq dom rules marked).1 → y ∈ dom) ∧
    (roundC ceq dom rules marked).1.length ≤ dom.length ∧
    (roundC ceq dom rules marked).2 ≤
      6 * (dom.length + 1) * ruleMeasure rules * (E + 1) := by
  have hmD : ∀ y, y ∈ marked → D y := fun y hy => hdomD y (hm y hy)
  obtain ⟨hH1, hH2⟩ := headsC_bound hb marked hmD hmK rules hrD
  have hHD : ∀ y, y ∈ (headsC ceq marked rules).1 → D y := by
    intro y hy
    obtain ⟨r, hr, rfl⟩ := headsC_sub (ceq := ceq) marked rules y hy
    exact hrH r hr
  obtain ⟨hF1, hF2, hF3⟩ := filterMemC_bound hb _ hHD hH1 dom hdomD
  refine ⟨hF2, hF1, ?_⟩
  show (headsC ceq marked rules).2 + (filterMemC ceq (headsC ceq marked rules).1 dom).2 + 1
    ≤ _
  exact round_arith _ _ _ _ _ _ hH2 hF3

theorem iterC_bound (hdomD : ∀ y, y ∈ dom → D y)
    (hrH : ∀ r, r ∈ rules → D r.1)
    (hrD : ∀ r, r ∈ rules → ∀ y, y ∈ r.2 → D y) :
    ∀ k : Nat,
      (∀ y, y ∈ (iterC ceq dom rules k).1 → y ∈ dom) ∧
      (iterC ceq dom rules k).1.length ≤ dom.length ∧
      (iterC ceq dom rules k).2 ≤
        k * (6 * (dom.length + 1) * ruleMeasure rules * (E + 1) + 1) + 1
  | 0 => by simp [iterC]
  | k + 1 => by
      obtain ⟨ih1, ih2, ih3⟩ := iterC_bound hdomD hrH hrD k
      obtain ⟨h1, h2, h3⟩ :=
        roundC_bound hb dom rules hdomD hrH hrD _ ih1 ih2
      refine ⟨h1, h2, ?_⟩
      show (iterC ceq dom rules k).2 +
          (roundC ceq dom rules (iterC ceq dom rules k).1).2 + 1 ≤ _
      have e : (k + 1) * (6 * (dom.length + 1) * ruleMeasure rules * (E + 1) + 1) =
          k * (6 * (dom.length + 1) * ruleMeasure rules * (E + 1) + 1) +
            6 * (dom.length + 1) * ruleMeasure rules * (E + 1) + 1 := by ring
      rw [e]
      omega

/-- **Cost of the closure engine**:
`≤ 8 · (|dom| + 1)² · (|rules| + Σ|body| + 1) · (E + 1)` steps. -/
theorem hornC_cost_le (hdomD : ∀ y, y ∈ dom → D y)
    (hrH : ∀ r, r ∈ rules → D r.1)
    (hrD : ∀ r, r ∈ rules → ∀ y, y ∈ r.2 → D y) :
    (hornC ceq dom rules).2 ≤
      8 * (dom.length + 1) ^ 2 * ruleMeasure rules * (E + 1) := by
  obtain ⟨_, _, h⟩ := iterC_bound hb dom rules hdomD hrH hrD (dom.length + 1)
  unfold hornC
  set K := dom.length
  set W := ruleMeasure rules with hW
  have hW1 : 1 ≤ W := by rw [hW]; unfold ruleMeasure; omega
  have hX : 1 ≤ (K + 1) * W * (E + 1) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero (by omega) (by omega))
      (by omega))
  have e : (K + 1) * (6 * (K + 1) * W * (E + 1) + 1) =
      6 * ((K + 1) * ((K + 1) * W * (E + 1))) + (K + 1) := by ring
  have e2 : 8 * (K + 1) ^ 2 * W * (E + 1) = 8 * ((K + 1) * ((K + 1) * W * (E + 1))) := by
    ring
  have h3 : K + 1 + 1 ≤ 2 * ((K + 1) * ((K + 1) * W * (E + 1))) := by
    have : K + 1 ≤ (K + 1) * ((K + 1) * W * (E + 1)) := Nat.le_mul_of_pos_right _ hX
    omega
  rw [e] at h
  rw [e2]
  omega

/-- The output of the engine consists of domain atoms. -/
theorem hornC_sub_dom (hdomD : ∀ y, y ∈ dom → D y)
    (hrH : ∀ r, r ∈ rules → D r.1)
    (hrD : ∀ r, r ∈ rules → ∀ y, y ∈ r.2 → D y) (y : σ)
    (hy : y ∈ (hornC ceq dom rules).1) : y ∈ dom :=
  (iterC_bound hb dom rules hdomD hrH hrD (dom.length + 1)).1 y hy

theorem hornC_length_le (hdomD : ∀ y, y ∈ dom → D y)
    (hrH : ∀ r, r ∈ rules → D r.1)
    (hrD : ∀ r, r ∈ rules → ∀ y, y ∈ r.2 → D y) :
    (hornC ceq dom rules).1.length ≤ dom.length :=
  (iterC_bound hb dom rules hdomD hrH hrD (dom.length + 1)).2.1

end Costs

end Horn
end TCS1
end LeanCfgProject
