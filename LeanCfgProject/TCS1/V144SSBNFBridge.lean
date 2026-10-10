import LeanCfgProject.TCS1.V144SSBNFNormalizer
import LeanCfgProject.TCS1.SeparatedStartUntypedBridge
import LeanCfgProject.TCS1.BinaryUnitElimination
import LeanCfgProject.TCS1.UnitFreeReachableTrim

/-!
# TCS #1 v144: the executable normalizer computes the existing semantic stages

`V144SSBNFNormalizer` computes lists by Horn closures.  This file proves that,
whenever the input `FrontCode` lists exactly the states and rules of a
semantic `BinaryNullableGrammar` on a subtype `{x // P x}` (`CodeMatches`),
every computed list is exactly the corresponding *existing* semantic object:

| computed list | existing predicate |
|---|---|
| `null` | `BinaryNullable` |
| `eunit` | `EpsilonElimUnitRule` |
| `ureach` | `UnitReach (EpsilonElimUnitRule _)` |
| `uterm`, `ubin` | `UnitFreeTerminalRule`, `UnitFreeBinaryRule` |
| `prod` | `ProductiveUnitFreeState` (`∃ w, UnitFreeDerives _ A w`) |
| `reach` | `ProductiveUnitFreeReachable` |
| output | `reducedSSBNFTerminalRule`, `reducedSSBNFBinaryRule`, `reducedSSBNFStartRule` |

and that derivations of the written output grammar are exactly the
derivations of the existing reduced SSBNF grammar (`codeDerives_iff`).
Nothing in this file is executed; it only relates the executable lists to the
semantic definitions.
-/

namespace LeanCfgProject
namespace TCS1
namespace SSBNFNorm

open Horn

universe u v

variable {σ : Type u} {α : Type v} [DecidableEq σ] {P : σ → Prop}

/-- The code lists exactly the states and rules of `Gs`. -/
structure CodeMatches (g : FrontCode σ α) (Gs : BinaryNullableGrammar {x // P x} α) :
    Prop where
  states : ∀ x, x ∈ g.states ↔ P x
  term : ∀ x a, (x, a) ∈ g.term ↔ ∃ hx : P x, Gs.terminalRule ⟨x, hx⟩ a
  bin : ∀ x y z, (x, y, z) ∈ g.bin ↔
    ∃ (hx : P x) (hy : P y) (hz : P z), Gs.binaryRule ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩
  unit : ∀ x y, (x, y) ∈ g.unit ↔
    ∃ (hx : P x) (hy : P y), Gs.unitRule ⟨x, hx⟩ ⟨y, hy⟩
  eps : ∀ x, x ∈ g.eps ↔ ∃ hx : P x, Gs.epsilonRule ⟨x, hx⟩

variable {g : FrontCode σ α} {Gs : BinaryNullableGrammar {x // P x} α}

omit [DecidableEq σ] in
theorem CodeMatches.wf (cm : CodeMatches g Gs) : WF g where
  term t ht := by
    obtain ⟨hx, _⟩ := (cm.term t.1 t.2).mp ht
    exact (cm.states _).mpr hx
  bin t ht := by
    obtain ⟨hx, hy, hz, _⟩ := (cm.bin t.1 t.2.1 t.2.2).mp ht
    exact ⟨(cm.states _).mpr hx, (cm.states _).mpr hy, (cm.states _).mpr hz⟩
  unit p hp := by
    obtain ⟨hx, hy, _⟩ := (cm.unit p.1 p.2).mp hp
    exact ⟨(cm.states _).mpr hx, (cm.states _).mpr hy⟩
  eps x hx := by
    obtain ⟨h, _⟩ := (cm.eps x).mp hx
    exact (cm.states _).mpr h

/-! ### Nullable states -/

omit [DecidableEq σ] in
theorem horn_null_sound (cm : CodeMatches g Gs) {x : σ}
    (h : HornDerivable (nullRules g) x) : ∃ hx : P x, BinaryNullable Gs ⟨x, hx⟩ := by
  induction h with
  | @rule x body hm _ ih =>
      simp only [nullRules, List.mem_append, List.mem_map] at hm
      rcases hm with ⟨z, hz, he⟩ | ⟨p, hp, he⟩ | ⟨t, ht, he⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        obtain ⟨hx, hr⟩ := (cm.eps z).mp hz
        exact ⟨hx, BinaryNullableDerives.epsilon hr⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        obtain ⟨hx, hy, hr⟩ := (cm.unit p.1 p.2).mp hp
        obtain ⟨_, d⟩ := ih p.2 (by simp)
        exact ⟨hx, BinaryNullableDerives.unit hr d⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        obtain ⟨hx, hy, hz, hr⟩ := (cm.bin t.1 t.2.1 t.2.2).mp ht
        obtain ⟨_, dB⟩ := ih t.2.1 (by simp)
        obtain ⟨_, dC⟩ := ih t.2.2 (by simp)
        exact ⟨hx, BinaryNullableDerives.binary hr dB dC⟩

omit [DecidableEq σ] in
theorem horn_null_complete (cm : CodeMatches g Gs) {X : {x // P x}} {w : List α}
    (d : BinaryNullableDerives Gs X w) : w = [] → HornDerivable (nullRules g) X.1 := by
  induction d with
  | terminal _ => intro h; cases h
  | @epsilon A h =>
      intro _
      refine HornDerivable.rule (body := []) ?_ (by simp)
      simp only [nullRules, List.mem_append, List.mem_map]
      exact Or.inl ⟨A.1, (cm.eps A.1).mpr ⟨A.2, h⟩, rfl⟩
  | @unit A B w h _ ih =>
      intro hw
      refine HornDerivable.rule (body := [B.1]) ?_ ?_
      · simp only [nullRules, List.mem_append, List.mem_map]
        exact Or.inr (Or.inl ⟨(A.1, B.1), (cm.unit A.1 B.1).mpr ⟨A.2, B.2, h⟩, rfl⟩)
      · intro y hy
        simp only [List.mem_singleton] at hy
        subst hy
        exact ih hw
  | @binary A B C wB wC h _ _ ihB ihC =>
      intro hw
      obtain ⟨hB, hC⟩ := List.append_eq_nil_iff.mp hw
      refine HornDerivable.rule (body := [B.1, C.1]) ?_ ?_
      · simp only [nullRules, List.mem_append, List.mem_map]
        exact Or.inr (Or.inr ⟨(A.1, B.1, C.1),
          (cm.bin A.1 B.1 C.1).mpr ⟨A.2, B.2, C.2, h⟩, rfl⟩)
      · intro y hy
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl
        · exact ihB hB
        · exact ihC hC

theorem mem_null_iff {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq)
    (cm : CodeMatches g Gs) (x : σ) :
    x ∈ (nullC ceq g).1 ↔ ∃ hx : P x, BinaryNullable Gs ⟨x, hx⟩ := by
  rw [mem_nullC hc cm.wf]
  constructor
  · exact horn_null_sound cm
  · rintro ⟨hx, d⟩
    exact horn_null_complete cm (X := ⟨x, hx⟩) d rfl

/-! ### ε-elimination -/

omit [DecidableEq σ] in
theorem epsElim_cases {X Z : {x // P x}} (h : EpsilonElimUnitRule Gs X Z) :
    Gs.unitRule X Z ∨ (∃ B, Gs.binaryRule X B Z ∧ BinaryNullable Gs B) ∨
      (∃ C, Gs.binaryRule X Z C ∧ BinaryNullable Gs C) := by
  cases h with
  | original h => exact Or.inl h
  | dropLeft hbin hnull => exact Or.inr (Or.inl ⟨_, hbin, hnull⟩)
  | dropRight hbin hnull => exact Or.inr (Or.inr ⟨_, hbin, hnull⟩)

theorem mem_eunit_iff {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq)
    (cm : CodeMatches g Gs) (x z : σ) :
    (x, z) ∈ (epsUnitC ceq g (nullC ceq g).1).1 ↔
      ∃ (hx : P x) (hz : P z), EpsilonElimUnitRule Gs ⟨x, hx⟩ ⟨z, hz⟩ := by
  rw [mem_epsUnitC hc]
  constructor
  · rintro (h | ⟨y, hy, hn⟩ | ⟨y, hy, hn⟩)
    · obtain ⟨hx, hz, hr⟩ := (cm.unit x z).mp h
      exact ⟨hx, hz, EpsilonElimUnitRule.original hr⟩
    · obtain ⟨hx, hy', hz, hr⟩ := (cm.bin x y z).mp hy
      obtain ⟨_, hnull⟩ := (mem_null_iff hc cm y).mp hn
      exact ⟨hx, hz, EpsilonElimUnitRule.dropLeft hr hnull⟩
    · obtain ⟨hx, hz, hy', hr⟩ := (cm.bin x z y).mp hy
      obtain ⟨_, hnull⟩ := (mem_null_iff hc cm y).mp hn
      exact ⟨hx, hz, EpsilonElimUnitRule.dropRight hr hnull⟩
  · rintro ⟨hx, hz, hr⟩
    rcases epsElim_cases hr with h | ⟨B, hbin, hnull⟩ | ⟨C, hbin, hnull⟩
    · exact Or.inl ((cm.unit x z).mpr ⟨hx, hz, h⟩)
    · exact Or.inr (Or.inl ⟨B.1, (cm.bin x B.1 z).mpr ⟨hx, B.2, hz, hbin⟩,
        (mem_null_iff hc cm B.1).mpr ⟨B.2, hnull⟩⟩)
    · exact Or.inr (Or.inr ⟨C.1, (cm.bin x z C.1).mpr ⟨hx, hz, C.2, hbin⟩,
        (mem_null_iff hc cm C.1).mpr ⟨C.2, hnull⟩⟩)

/-! ### Unit closure -/

section UnitClosure

variable {eunit : List (σ × σ)}
  (heu : ∀ x z, (x, z) ∈ eunit ↔
    ∃ (hx : P x) (hz : P z), EpsilonElimUnitRule Gs ⟨x, hx⟩ ⟨z, hz⟩)
include heu

omit [DecidableEq σ] in
theorem horn_unit_sound (x : σ) (hx : P x) {z : σ}
    (h : HornDerivable (unitRulesFrom eunit x) z) :
    ∃ hz : P z, UnitReach (EpsilonElimUnitRule Gs) ⟨x, hx⟩ ⟨z, hz⟩ := by
  induction h with
  | @rule z body hm _ ih =>
      simp only [unitRulesFrom, List.mem_cons, List.mem_map] at hm
      rcases hm with he | ⟨p, hp, he⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        exact ⟨hx, UnitReach.refl _⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        obtain ⟨hy, hz, hr⟩ := (heu p.1 p.2).mp hp
        obtain ⟨_, hreach⟩ := ih p.1 (by simp)
        exact ⟨hz, UnitReach.trans hreach (UnitReach.step hr (UnitReach.refl _))⟩

omit [DecidableEq σ] in
theorem horn_unit_prepend {A B : σ} (hAB : (A, B) ∈ eunit) {z : σ}
    (h : HornDerivable (unitRulesFrom eunit B) z) :
    HornDerivable (unitRulesFrom eunit A) z := by
  have hbase : HornDerivable (unitRulesFrom eunit A) A :=
    HornDerivable.rule (body := []) (by simp [unitRulesFrom]) (by simp)
  have hstep : ∀ p, p ∈ eunit → HornDerivable (unitRulesFrom eunit A) p.1 →
      HornDerivable (unitRulesFrom eunit A) p.2 := by
    intro p hp hd
    refine HornDerivable.rule (body := [p.1]) ?_ ?_
    · simp only [unitRulesFrom, List.mem_cons, List.mem_map]
      exact Or.inr ⟨p, hp, rfl⟩
    · intro y hy
      simp only [List.mem_singleton] at hy
      subst hy; exact hd
  induction h with
  | @rule z body hm _ ih =>
      simp only [unitRulesFrom, List.mem_cons, List.mem_map] at hm
      rcases hm with he | ⟨p, hp, he⟩
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        exact hstep _ hAB hbase
      · obtain ⟨h1, h2⟩ := Prod.mk.inj he
        subst h1; subst h2
        exact hstep p hp (ih p.1 (by simp))

omit [DecidableEq σ] in
theorem horn_unit_complete {X Z : {x // P x}}
    (h : UnitReach (EpsilonElimUnitRule Gs) X Z) :
    HornDerivable (unitRulesFrom eunit X.1) Z.1 := by
  induction h with
  | refl A =>
      exact HornDerivable.rule (body := []) (by simp [unitRulesFrom]) (by simp)
  | @step A B C hAB _ ih =>
      exact horn_unit_prepend heu ((heu A.1 B.1).mpr ⟨A.2, B.2, hAB⟩) ih

end UnitClosure

theorem mem_ureach_iff {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq)
    (cm : CodeMatches g Gs) (x z : σ) :
    (x, z) ∈ (unitClosureC ceq g.states (epsUnitC ceq g (nullC ceq g).1).1).1 ↔
      ∃ (hx : P x) (hz : P z),
        UnitReach (EpsilonElimUnitRule Gs) ⟨x, hx⟩ ⟨z, hz⟩ := by
  have heu := mem_eunit_iff hc cm
  rw [mem_unitClosureC hc _ _ (epsUnitC_wf hc cm.wf _) x z]
  constructor
  · rintro ⟨hxs, hd⟩
    have hx := (cm.states x).mp hxs
    obtain ⟨hz, hr⟩ := horn_unit_sound heu x hx hd
    exact ⟨hx, hz, hr⟩
  · rintro ⟨hx, hz, hr⟩
    exact ⟨(cm.states x).mpr hx, horn_unit_complete heu (X := ⟨x, hx⟩) (Z := ⟨z, hz⟩) hr⟩

/-! ### Unit elimination -/

theorem mem_uterm_iff {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq)
    (cm : CodeMatches g Gs) (x : σ) (a : α) :
    (x, a) ∈ (unitFreeTermC ceq g.term
        (unitClosureC ceq g.states (epsUnitC ceq g (nullC ceq g).1).1).1).1 ↔
      ∃ hx : P x, UnitFreeTerminalRule Gs ⟨x, hx⟩ a := by
  rw [mem_unitFreeTermC hc]
  constructor
  · rintro ⟨y, hy, ht⟩
    obtain ⟨hx, hy', hr⟩ := (mem_ureach_iff hc cm x y).mp hy
    obtain ⟨hy'', htr⟩ := (cm.term y a).mp ht
    exact ⟨hx, ⟨y, hy'⟩, hr, htr⟩
  · rintro ⟨hx, B, hr, htr⟩
    exact ⟨B.1, (mem_ureach_iff hc cm x B.1).mpr ⟨hx, B.2, hr⟩,
      (cm.term B.1 a).mpr ⟨B.2, htr⟩⟩

theorem mem_ubin_iff {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq)
    (cm : CodeMatches g Gs) (x c d : σ) :
    (x, c, d) ∈ (unitFreeBinC ceq g.bin
        (unitClosureC ceq g.states (epsUnitC ceq g (nullC ceq g).1).1).1).1 ↔
      ∃ (hx : P x) (hc' : P c) (hd : P d),
        UnitFreeBinaryRule Gs ⟨x, hx⟩ ⟨c, hc'⟩ ⟨d, hd⟩ := by
  rw [mem_unitFreeBinC hc]
  constructor
  · rintro ⟨y, hy, ht⟩
    obtain ⟨hx, hy', hr⟩ := (mem_ureach_iff hc cm x y).mp hy
    obtain ⟨_, hc', hd, hbr⟩ := (cm.bin y c d).mp ht
    exact ⟨hx, hc', hd, ⟨y, hy'⟩, hr, hbr⟩
  · rintro ⟨hx, hc', hd, B, hr, hbr⟩
    exact ⟨B.1, (mem_ureach_iff hc cm x B.1).mpr ⟨hx, B.2, hr⟩,
      (cm.bin B.1 c d).mpr ⟨B.2, hc', hd, hbr⟩⟩

/-! ### Productive states -/

section Productive

variable {uterm : List (σ × α)} {ubin : List (σ × σ × σ)}
  (hut : ∀ x a, (x, a) ∈ uterm ↔ ∃ hx : P x, UnitFreeTerminalRule Gs ⟨x, hx⟩ a)
  (hub : ∀ x c d, (x, c, d) ∈ ubin ↔
    ∃ (hx : P x) (hc' : P c) (hd : P d), UnitFreeBinaryRule Gs ⟨x, hx⟩ ⟨c, hc'⟩ ⟨d, hd⟩)
include hut hub

omit [DecidableEq σ] in
theorem horn_prod_iff (x : σ) :
    HornDerivable (prodRules uterm ubin) x ↔
      ∃ hx : P x, ∃ w, UnitFreeDerives Gs ⟨x, hx⟩ w := by
  constructor
  · intro h
    induction h with
    | @rule x body hm _ ih =>
        simp only [prodRules, List.mem_append, List.mem_map] at hm
        rcases hm with ⟨p, hp, he⟩ | ⟨t, ht, he⟩
        · obtain ⟨h1, h2⟩ := Prod.mk.inj he
          subst h1; subst h2
          obtain ⟨hx, hr⟩ := (hut p.1 p.2).mp hp
          exact ⟨hx, [p.2], UnitFreeDerives.terminal hr⟩
        · obtain ⟨h1, h2⟩ := Prod.mk.inj he
          subst h1; subst h2
          obtain ⟨hx, _, _, hr⟩ := (hub t.1 t.2.1 t.2.2).mp ht
          obtain ⟨_, wC, dC⟩ := ih t.2.1 (by simp)
          obtain ⟨_, wD, dD⟩ := ih t.2.2 (by simp)
          exact ⟨hx, wC ++ wD, UnitFreeDerives.binary hr dC dD⟩
  · rintro ⟨hx, w, d⟩
    have key : ∀ {X : {x // P x}} {w : List α}, UnitFreeDerives Gs X w →
        HornDerivable (prodRules uterm ubin) X.1 := by
      intro X w d
      induction d with
      | @terminal A a h =>
          refine HornDerivable.rule (body := []) ?_ (by simp)
          simp only [prodRules, List.mem_append, List.mem_map]
          exact Or.inl ⟨(A.1, a), (hut A.1 a).mpr ⟨A.2, h⟩, rfl⟩
      | @binary A C D wC wD h _ _ ihC ihD =>
          refine HornDerivable.rule (body := [C.1, D.1]) ?_ ?_
          · simp only [prodRules, List.mem_append, List.mem_map]
            exact Or.inr ⟨(A.1, C.1, D.1), (hub A.1 C.1 D.1).mpr ⟨A.2, C.2, D.2, h⟩, rfl⟩
          · intro y hy
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
            rcases hy with rfl | rfl
            · exact ihC
            · exact ihD
    exact key (X := ⟨x, hx⟩) d

end Productive

/-! ### Reachable states -/

section Reachable

variable {prod : List σ} {pbin : List (σ × σ × σ)}
  (hprod : ∀ x, x ∈ prod ↔ ∃ hx : P x, ∃ w, UnitFreeDerives Gs ⟨x, hx⟩ w)
  (hpb : ∀ x c d, (x, c, d) ∈ pbin ↔
    (∃ (hx : P x) (hc' : P c) (hd : P d), UnitFreeBinaryRule Gs ⟨x, hx⟩ ⟨c, hc'⟩ ⟨d, hd⟩) ∧
      x ∈ prod ∧ c ∈ prod ∧ d ∈ prod)
  (start : ProductiveUnitFreeState Gs) {s : σ} (hs : start.1.1 = s)
include hprod hpb hs

omit [DecidableEq σ] in
theorem horn_reach_iff (x : σ) :
    HornDerivable (reachRules s pbin) x ↔
      ∃ X : ProductiveUnitFreeState Gs, X.1.1 = x ∧ ProductiveUnitFreeReachable Gs start X := by
  constructor
  · intro h
    induction h with
    | @rule x body hm _ ih =>
        simp only [reachRules, List.mem_cons, List.mem_flatMap] at hm
        rcases hm with he | ⟨t, ht, hm⟩
        · obtain ⟨h1, h2⟩ := Prod.mk.inj he
          subst h1; subst h2
          exact ⟨start, hs, ProductiveUnitFreeReachable.start⟩
        · obtain ⟨⟨hx, hc', hd, hr⟩, hpx, hpc, hpd⟩ := (hpb t.1 t.2.1 t.2.2).mp ht
          obtain ⟨X, hX, hreach⟩ := ih t.1 (by
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
            rcases hm with he | he <;> (obtain ⟨_, h2⟩ := Prod.mk.inj he; rw [h2]; simp))
          obtain ⟨_, wc, dc⟩ := (hprod _).mp hpc
          obtain ⟨_, wd, dd⟩ := (hprod _).mp hpd
          let C' : ProductiveUnitFreeState Gs := ⟨⟨t.2.1, hc'⟩, ⟨wc, dc⟩⟩
          let D' : ProductiveUnitFreeState Gs := ⟨⟨t.2.2, hd⟩, ⟨wd, dd⟩⟩
          have hrule : (productiveUnitFreeGrammar Gs).binaryRule X C' D' := by
            show UnitFreeBinaryRule Gs X.1 ⟨t.2.1, hc'⟩ ⟨t.2.2, hd⟩
            have : X.1 = ⟨t.1, hx⟩ := Subtype.ext hX
            rw [this]; exact hr
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
          rcases hm with he | he
          · obtain ⟨h1, h2⟩ := Prod.mk.inj he
            subst h1; subst h2
            exact ⟨C', rfl, ProductiveUnitFreeReachable.left hreach hrule⟩
          · obtain ⟨h1, h2⟩ := Prod.mk.inj he
            subst h1; subst h2
            exact ⟨D', rfl, ProductiveUnitFreeReachable.right hreach hrule⟩
  · rintro ⟨X, rfl, hX⟩
    induction hX with
    | start =>
        refine HornDerivable.rule (body := []) ?_ (by simp)
        rw [← hs]; simp [reachRules]
    | @left A B C _ h ih =>
        refine HornDerivable.rule (body := [A.1.1]) ?_ ?_
        · simp only [reachRules, List.mem_cons, List.mem_flatMap]
          refine Or.inr ⟨(A.1.1, B.1.1, C.1.1), ?_, by simp⟩
          refine (hpb _ _ _).mpr ⟨⟨A.1.2, B.1.2, C.1.2, h⟩, ?_, ?_, ?_⟩
          · exact (hprod _).mpr ⟨A.1.2, A.2⟩
          · exact (hprod _).mpr ⟨B.1.2, B.2⟩
          · exact (hprod _).mpr ⟨C.1.2, C.2⟩
        · intro y hy
          simp only [List.mem_singleton] at hy
          subst hy; exact ih
    | @right A B C _ h ih =>
        refine HornDerivable.rule (body := [A.1.1]) ?_ ?_
        · simp only [reachRules, List.mem_cons, List.mem_flatMap]
          refine Or.inr ⟨(A.1.1, B.1.1, C.1.1), ?_, by simp⟩
          refine (hpb _ _ _).mpr ⟨⟨A.1.2, B.1.2, C.1.2, h⟩, ?_, ?_, ?_⟩
          · exact (hprod _).mpr ⟨A.1.2, A.2⟩
          · exact (hprod _).mpr ⟨B.1.2, B.2⟩
          · exact (hprod _).mpr ⟨C.1.2, C.2⟩
        · intro y hy
          simp only [List.mem_singleton] at hy
          subst hy; exact ih

end Reachable


/-! ### The whole trace -/

section Output

variable {ceq : σ → σ → Bool × Nat} (hc : CeqCorrect ceq) (cm : CodeMatches g Gs)
  (start : ProductiveUnitFreeState Gs) {s : σ} (hs : start.1.1 = s)

include hc cm in
theorem trace_uterm_iff (x : σ) (a : α) :
    (x, a) ∈ (normalizeTrace ceq g s).uterm ↔
      ∃ hx : P x, UnitFreeTerminalRule Gs ⟨x, hx⟩ a :=
  mem_uterm_iff hc cm x a

include hc cm in
theorem trace_ubin_iff (x c d : σ) :
    (x, c, d) ∈ (normalizeTrace ceq g s).ubin ↔
      ∃ (hx : P x) (hc' : P c) (hd : P d),
        UnitFreeBinaryRule Gs ⟨x, hx⟩ ⟨c, hc'⟩ ⟨d, hd⟩ :=
  mem_ubin_iff hc cm x c d

include hc cm in
theorem trace_prod_iff (x : σ) :
    x ∈ (normalizeTrace ceq g s).prod ↔ ∃ hx : P x, ∃ w, UnitFreeDerives Gs ⟨x, hx⟩ w := by
  rw [trace_prod]
  have hut := trace_uterm_iff (s := s) hc cm
  have hub := trace_ubin_iff (s := s) hc cm
  rw [mem_prod hc g.states _ _ ?_ ?_ x]
  · exact horn_prod_iff hut hub x
  · intro p hp
    obtain ⟨hx, _⟩ := (hut p.1 p.2).mp hp
    exact (cm.states _).mpr hx
  · intro t ht
    obtain ⟨hx, _⟩ := (hub t.1 t.2.1 t.2.2).mp ht
    exact (cm.states _).mpr hx

include hc cm in
theorem trace_pbin_iff (x c d : σ) :
    (x, c, d) ∈ (normalizeTrace ceq g s).pbin ↔
      (∃ (hx : P x) (hc' : P c) (hd : P d),
        UnitFreeBinaryRule Gs ⟨x, hx⟩ ⟨c, hc'⟩ ⟨d, hd⟩) ∧
      x ∈ (normalizeTrace ceq g s).prod ∧ c ∈ (normalizeTrace ceq g s).prod ∧
        d ∈ (normalizeTrace ceq g s).prod := by
  rw [trace_pbin, mem_prodBinC hc, trace_ubin_iff hc cm]

include hc cm hs in
theorem trace_reach_iff (x : σ) :
    x ∈ (normalizeTrace ceq g s).reach ↔
      ∃ X : ProductiveUnitFreeState Gs, X.1.1 = x ∧ ProductiveUnitFreeReachable Gs start X := by
  rw [trace_reach]
  have hsS : s ∈ g.states := by rw [← hs]; exact (cm.states _).mpr start.1.2
  rw [mem_reach hc g.states s _ hsS ?_ x]
  · exact horn_reach_iff (trace_prod_iff (s := s) hc cm) (trace_pbin_iff (s := s) hc cm)
      start hs x
  · intro t ht
    have ht' : (t.1, t.2.1, t.2.2) ∈ (normalizeTrace ceq g s).pbin := ht
    obtain ⟨⟨_, hc', hd, _⟩, _⟩ := (trace_pbin_iff (s := s) hc cm t.1 t.2.1 t.2.2).mp ht'
    exact ⟨(cm.states _).mpr hc', (cm.states _).mpr hd⟩

include hc cm hs in
theorem trace_start_productive : (memC ceq s (normalizeTrace ceq g s).prod).1 = true := by
  rw [memC_fst hc, decide_eq_true_iff, trace_prod_iff hc cm]
  subst hs
  exact ⟨start.1.2, start.2⟩

include hc cm hs in
/-- The written output, when the start is productive. -/
theorem trace_out_eq :
    (normalizeTrace ceq g s).out =
      { nonterminals := (normalizeTrace ceq g s).reach,
        terminal := (outTermC ceq (normalizeTrace ceq g s).reach
          (normalizeTrace ceq g s).uterm).1,
        binary := (outBinC ceq (normalizeTrace ceq g s).reach
          (normalizeTrace ceq g s).pbin).1,
        start := some s,
        epsilon := (memC ceq s (normalizeTrace ceq g s).null).1 } := by
  rw [trace_out, if_pos (trace_start_productive hc cm start hs)]

/-- Reduced states are determined by their underlying raw state. -/
theorem reduced_ext {X Y : ReducedUnitFreeState Gs start} (h : X.1.1.1 = Y.1.1.1) : X = Y :=
  Subtype.ext (Subtype.ext (Subtype.ext h))

include hc cm hs in
theorem out_nonterminal_iff (x : σ) :
    x ∈ (normalizeTrace ceq g s).out.nonterminals ↔
      ∃ X : ReducedUnitFreeState Gs start, X.1.1.1 = x := by
  rw [trace_out_eq hc cm start hs]
  show x ∈ (normalizeTrace ceq g s).reach ↔ _
  rw [trace_reach_iff hc cm start hs]
  constructor
  · rintro ⟨X, hX, hr⟩; exact ⟨⟨X, hr⟩, hX⟩
  · rintro ⟨X, hX⟩; exact ⟨X.1, hX, X.2⟩

include hc cm hs in
theorem out_terminal_iff (x : σ) (a : α) :
    (x, a) ∈ (normalizeTrace ceq g s).out.terminal ↔
      ∃ X : ReducedUnitFreeState Gs start, X.1.1.1 = x ∧ reducedSSBNFTerminalRule Gs start X a := by
  rw [trace_out_eq hc cm start hs]
  show (x, a) ∈ (outTermC ceq _ _).1 ↔ _
  rw [mem_outTermC hc, trace_uterm_iff hc cm, trace_reach_iff hc cm start hs]
  constructor
  · rintro ⟨⟨hx, hr⟩, X, hX, hreach⟩
    refine ⟨⟨X, hreach⟩, hX, ?_⟩
    show UnitFreeTerminalRule Gs X.1 a
    have : X.1 = ⟨x, hx⟩ := Subtype.ext hX
    rw [this]; exact hr
  · rintro ⟨X, hX, hr⟩
    subst hX
    exact ⟨⟨X.1.1.2, hr⟩, X.1, rfl, X.2⟩

include hc cm hs in
theorem out_binary_iff (x y z : σ) :
    (x, y, z) ∈ (normalizeTrace ceq g s).out.binary ↔
      ∃ X Y Z : ReducedUnitFreeState Gs start, X.1.1.1 = x ∧ Y.1.1.1 = y ∧ Z.1.1.1 = z ∧
        reducedSSBNFBinaryRule Gs start X Y Z := by
  rw [trace_out_eq hc cm start hs]
  show (x, y, z) ∈ (outBinC ceq _ _).1 ↔ _
  rw [mem_outBinC hc, trace_pbin_iff hc cm, trace_reach_iff hc cm start hs]
  constructor
  · rintro ⟨⟨⟨hx, hy, hz, hr⟩, _, hpy, hpz⟩, X, hX, hreach⟩
    obtain ⟨_, wy, dy⟩ := (trace_prod_iff (s := s) hc cm y).mp hpy
    obtain ⟨_, wz, dz⟩ := (trace_prod_iff (s := s) hc cm z).mp hpz
    let Y' : ProductiveUnitFreeState Gs := ⟨⟨y, hy⟩, ⟨wy, dy⟩⟩
    let Z' : ProductiveUnitFreeState Gs := ⟨⟨z, hz⟩, ⟨wz, dz⟩⟩
    have hrule : (productiveUnitFreeGrammar Gs).binaryRule X Y' Z' := by
      show UnitFreeBinaryRule Gs X.1 ⟨y, hy⟩ ⟨z, hz⟩
      have : X.1 = ⟨x, hx⟩ := Subtype.ext hX
      rw [this]; exact hr
    exact ⟨⟨X, hreach⟩, ⟨Y', ProductiveUnitFreeReachable.left hreach hrule⟩,
      ⟨Z', ProductiveUnitFreeReachable.right hreach hrule⟩, hX, rfl, rfl, hrule⟩
  · rintro ⟨X, Y, Z, rfl, rfl, rfl, hr⟩
    refine ⟨⟨⟨X.1.1.2, Y.1.1.2, Z.1.1.2, hr⟩, ?_, ?_, ?_⟩, X.1, rfl, X.2⟩
    · exact (trace_prod_iff (s := s) hc cm _).mpr ⟨X.1.1.2, X.1.2⟩
    · exact (trace_prod_iff (s := s) hc cm _).mpr ⟨Y.1.1.2, Y.1.2⟩
    · exact (trace_prod_iff (s := s) hc cm _).mpr ⟨Z.1.1.2, Z.1.2⟩

include hc cm hs in
theorem out_start_eq : (normalizeTrace ceq g s).out.start = some s := by
  rw [trace_out_eq hc cm start hs]

include hc cm hs in
theorem out_epsilon_iff :
    (normalizeTrace ceq g s).out.epsilon = true ↔ BinaryNullable Gs start.1 := by
  rw [trace_out_eq hc cm start hs]
  show (memC ceq s (normalizeTrace ceq g s).null).1 = true ↔ _
  rw [memC_fst hc, decide_eq_true_iff, trace_null, mem_null_iff hc cm]
  subst hs
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨start.1.2, h⟩

/-! ### Derivations of the written grammar -/

/-- Terminal rules of the written output, read as a grammar on raw states. -/
def codeTerminalRule (c : SSBNFCode σ α) : σ → α → Prop := fun x a => (x, a) ∈ c.terminal

/-- Binary rules of the written output. -/
def codeBinaryRule (c : SSBNFCode σ α) : σ → σ → σ → Prop :=
  fun x y z => (x, y, z) ∈ c.binary

/-- Start rule of the written output. -/
def codeStartRule (c : SSBNFCode σ α) : σ → Prop := fun x => c.start = some x

include hc cm hs in
theorem codeDerives_iff (x : σ) (w : Word α) :
    UntypedDerives (codeTerminalRule (normalizeTrace ceq g s).out)
        (codeBinaryRule (normalizeTrace ceq g s).out) x w ↔
      ∃ X : ReducedUnitFreeState Gs start, X.1.1.1 = x ∧
        UntypedDerives (reducedSSBNFTerminalRule Gs start)
          (reducedSSBNFBinaryRule Gs start) X w := by
  constructor
  · intro d
    induction d with
    | @terminal x a h =>
        obtain ⟨X, hX, hr⟩ := (out_terminal_iff hc cm start hs x a).mp h
        exact ⟨X, hX, UntypedDerives.terminal hr⟩
    | @binary x y z wB wC h _ _ ihB ihC =>
        obtain ⟨X, Y, Z, hX, hY, hZ, hr⟩ := (out_binary_iff hc cm start hs x y z).mp h
        obtain ⟨Y', hY', dB⟩ := ihB
        obtain ⟨Z', hZ', dC⟩ := ihC
        have e1 : Y' = Y := reduced_ext start (hY'.trans hY.symm)
        have e2 : Z' = Z := reduced_ext start (hZ'.trans hZ.symm)
        subst e1; subst e2
        exact ⟨X, hX, UntypedDerives.binary hr dB dC⟩
  · rintro ⟨X, rfl, d⟩
    induction d with
    | @terminal X a h =>
        exact UntypedDerives.terminal ((out_terminal_iff hc cm start hs _ a).mpr ⟨X, rfl, h⟩)
    | @binary X Y Z wB wC h _ _ ihB ihC =>
        exact UntypedDerives.binary
          ((out_binary_iff hc cm start hs _ _ _).mpr ⟨X, Y, Z, rfl, rfl, rfl, h⟩) ihB ihC

include hc cm hs in
/-- The written output has exactly the start language of the existing reduced grammar. -/
theorem codeStartLanguage_eq :
    UntypedStartLanguage (codeTerminalRule (normalizeTrace ceq g s).out)
        (codeBinaryRule (normalizeTrace ceq g s).out)
        (codeStartRule (normalizeTrace ceq g s).out)
        ((normalizeTrace ceq g s).out.epsilon = true) =
      UntypedStartLanguage (reducedSSBNFTerminalRule Gs start)
        (reducedSSBNFBinaryRule Gs start) (reducedSSBNFStartRule Gs start)
        (BinaryNullable Gs start.1) := by
  ext w
  show UntypedStartDerives _ _ _ _ w ↔ UntypedStartDerives _ _ _ _ w
  constructor
  · intro h
    cases h with
    | @nonempty x w hstart d =>
        have hx : x = s := by
          have : (normalizeTrace ceq g s).out.start = some x := hstart
          rw [out_start_eq hc cm start hs] at this
          exact (Option.some.inj this).symm
        obtain ⟨X, hX, d'⟩ := (codeDerives_iff hc cm start hs x w).mp d
        have hXs : X = reducedUnitFreeStart Gs start := by
          apply reduced_ext start
          exact (hX.trans hx).trans hs.symm
        exact UntypedStartDerives.nonempty hXs d'
    | epsilon heps =>
        exact UntypedStartDerives.epsilon ((out_epsilon_iff hc cm start hs).mp heps)
  · intro h
    cases h with
    | @nonempty X w hstart d =>
        have hX : X.1.1.1 = s := by
          rw [show X = reducedUnitFreeStart Gs start from hstart]; exact hs
        refine UntypedStartDerives.nonempty (A := s) ?_ ?_
        · exact out_start_eq hc cm start hs
        · exact (codeDerives_iff hc cm start hs s w).mpr ⟨X, hX, d⟩
    | epsilon heps =>
        exact UntypedStartDerives.epsilon ((out_epsilon_iff hc cm start hs).mpr heps)

/-- Reachability in the written output grammar from its start state. -/
inductive CodeReachable (c : SSBNFCode σ α) (s : σ) : σ → Prop
  | start : CodeReachable c s s
  | left {x y z : σ} : CodeReachable c s x → (x, y, z) ∈ c.binary → CodeReachable c s y
  | right {x y z : σ} : CodeReachable c s x → (x, y, z) ∈ c.binary → CodeReachable c s z

include hc cm hs in
/-- Every written nonterminal is reachable from the start in the written grammar. -/
theorem out_reachable (x : σ) (hx : x ∈ (normalizeTrace ceq g s).out.nonterminals) :
    CodeReachable (normalizeTrace ceq g s).out s x := by
  obtain ⟨X, rfl⟩ := (out_nonterminal_iff hc cm start hs x).mp hx
  have key : ∀ Y : ProductiveUnitFreeState Gs, ProductiveUnitFreeReachable Gs start Y →
      CodeReachable (normalizeTrace ceq g s).out s Y.1.1 := by
    intro Y hY
    induction hY with
    | start => rw [hs]; exact CodeReachable.start
    | @left A B C hA h ih =>
        exact CodeReachable.left ih ((out_binary_iff hc cm start hs _ _ _).mpr
          ⟨⟨A, hA⟩, ⟨B, ProductiveUnitFreeReachable.left hA h⟩,
            ⟨C, ProductiveUnitFreeReachable.right hA h⟩, rfl, rfl, rfl, h⟩)
    | @right A B C hA h ih =>
        exact CodeReachable.right ih ((out_binary_iff hc cm start hs _ _ _).mpr
          ⟨⟨A, hA⟩, ⟨B, ProductiveUnitFreeReachable.left hA h⟩,
            ⟨C, ProductiveUnitFreeReachable.right hA h⟩, rfl, rfl, rfl, h⟩)
  exact key X.1 X.2

end Output

end SSBNFNorm
end TCS1
end LeanCfgProject
