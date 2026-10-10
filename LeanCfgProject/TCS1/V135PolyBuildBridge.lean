import LeanCfgProject.TCS1.V135PolyBuildAlgorithm
import LeanCfgProject.TCS1.V128SubstringEffectiveBinaryTable

/-!
# TCS #1 v135: `thm:poly-build` — the executable constructor is `B_h`

This module connects the step-counted constructor of
`V135PolyBuildAlgorithm.lean` with the previously verified objects:

* **Theorem A (rule exactness).**  For a sample `K = ws.toFinset`, the emitted
  rules of `constructV116 (fun a => H.h [a]) ws` are exactly the rows of the
  verified v116 tables: (B) `v116EffectiveBinaryWordTable` (= the actual (B)
  table by `v116EffectiveBinaryWordTable_eq_actual`), (U) `v116UnaryRuleTable`,
  (L) `v116LexicalRuleTable`, (S) `v116StartRuleTable`, (ε)
  `v116EpsilonStartTable`; the declared nonterminals are exactly the observed
  factors.
* **Theorem B (language).**  The grammar *as written by the constructor*,
  read as a CFG over its literal nonterminal names, generates exactly
  `BatchLanguage H K` (via `finiteSubstringBatchLanguage_eq_batchLanguage`).
* **Theorem C (time).**  Its step count is at most `1400 · (n_K + 1)^4` when
  `ws` lists `K` without repetition (`n_K = ‖K‖`).
* `thm_polyBuild`: the paper-facing combination for every finite sample `K`.
-/

namespace LeanCfgProject
namespace TCS1
namespace PolyBuild

set_option linter.unusedSectionVars false

universe u v

section Bridge

variable {α : Type u} [Fintype α] [DecidableEq α]
variable {M : Type v} [Monoid M] [Fintype M] [DecidableEq M]

/-- The constructor run with the letter types of the fixed typing `H`. -/
def constructV116H (H : FixedFiniteMonoidHom α M) (ws : List (Word α)) :
    V116GrammarCode α :=
  constructV116 (fun a => H.h [a]) ws

/-- Its step count. -/
def constructV116HCost (H : FixedFiniteMonoidHom α M) (ws : List (Word α)) : Nat :=
  constructV116Cost (fun a => H.h [a]) ws

theorem occursIn_iff_observed (ws : List (Word α)) (x p q : Word α) :
    OccursIn ws x p q ↔ Observed ws.toFinset x p q := by
  unfold OccursIn Observed
  rw [List.mem_toFinset]

theorem exists_occursIn_iff (ws : List (Word α)) (x : Word α) :
    (∃ p q, OccursIn ws x p q) ↔ ∃ p q, Observed ws.toFinset x p q := by
  simp only [occursIn_iff_observed]

/-! ### Theorem A: rule exactness against the verified tables -/

theorem constructV116H_binary_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x y z : Word α) :
    (x, y, z) ∈ (constructV116H H ws).binary ↔
      (x, (y, z)) ∈ v116EffectiveBinaryWordTable ws.toFinset := by
  rw [constructV116H, mem_binary, v116EffectiveBinaryWordTable_iff,
    exists_occursIn_iff]

theorem constructV116H_binary_iff_actual (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x y z : Word α) :
    (x, y, z) ∈ (constructV116H H ws).binary ↔
      (x, (y, z)) ∈ (v116BinaryRuleTable ws.toFinset).image
        (v116BinaryProductionWordCode (K := ws.toFinset)) := by
  rw [constructV116H_binary_iff, v116EffectiveBinaryWordTable_eq_actual]

theorem substringUnaryRelated_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x y : Word α) :
    SubstringUnaryRelated H ws.toFinset x y ↔
      H.h x = H.h y ∧ ∃ p q, OccursIn ws x p q ∧ OccursIn ws y p q := by
  unfold SubstringUnaryRelated
  simp only [occursIn_iff_observed]

theorem constructV116H_unary_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x y : Word α) :
    (x, y) ∈ (constructV116H H ws).unary ↔
      (x, y) ∈ v116UnaryRuleTable H ws.toFinset := by
  rw [constructV116H, mem_unary H.h H.map_nil H.map_append]
  constructor
  · intro h
    exact v116UnaryRuleTable_complete H ws.toFinset
      ((substringUnaryRelated_iff H ws x y).2 h)
  · intro h
    exact (substringUnaryRelated_iff H ws x y).1
      (v116UnaryRuleTable_sound H ws.toFinset h)

theorem constructV116H_lexical_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x : Word α) (a : α) :
    (x, a) ∈ (constructV116H H ws).lexical ↔
      ∃ A : ObservedSubstringNonterminal ws.toFinset,
        (A, a) ∈ v116LexicalRuleTable ws.toFinset ∧ A.1 = x := by
  rw [constructV116H, mem_lexical]
  constructor
  · rintro ⟨rfl, p, q, hocc⟩
    refine ⟨⟨[a], p, q, (occursIn_iff_observed ws [a] p q).1 hocc⟩, ?_, rfl⟩
    exact (v116LexicalRuleTable_iff H ws.toFinset _ a).2 rfl
  · rintro ⟨A, hA, rfl⟩
    have h1 : A.1 = [a] := (v116LexicalRuleTable_iff H ws.toFinset A a).1 hA
    obtain ⟨p, q, hobs⟩ := A.2
    refine ⟨h1, p, q, ?_⟩
    rw [← h1]
    exact (occursIn_iff_observed ws A.1 p q).2 hobs

theorem constructV116H_start_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x : Word α) :
    x ∈ (constructV116H H ws).start ↔
      ∃ A : ObservedSubstringNonterminal ws.toFinset,
        A ∈ v116StartRuleTable ws.toFinset ∧ A.1 = x := by
  rw [constructV116H, mem_start]
  constructor
  · rintro ⟨hx, hne⟩
    refine ⟨⟨x, [], [], hne, by simpa [List.mem_toFinset] using hx⟩, ?_, rfl⟩
    exact (v116StartRuleTable_iff ws.toFinset _).2
      (List.mem_toFinset.2 hx)
  · rintro ⟨A, hA, rfl⟩
    have h := (v116StartRuleTable_iff ws.toFinset A).1 hA
    exact ⟨List.mem_toFinset.1 h, observedSubstring_ne_nil ws.toFinset A⟩

theorem constructV116H_epsilon_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) :
    (constructV116H H ws).epsilon = true ↔
      () ∈ v116EpsilonStartTable ws.toFinset := by
  rw [constructV116H, epsilon_iff, v116EpsilonStartTable_iff, List.mem_toFinset]

theorem constructV116H_nonterminals_iff (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) (x : Word α) :
    x ∈ (constructV116H H ws).nonterminals ↔
      ∃ p q, Observed ws.toFinset x p q := by
  rw [constructV116H, mem_nonterminals, exists_occursIn_iff]

/-! ### Theorem B: the written grammar generates `BatchLanguage H K` -/

/-- The emitted code read as a CFG whose nonterminals are its literal names. -/
def codeGrammar (g : V116GrammarCode α) : BinaryNullableGrammar (Word α) α where
  terminalRule x a := (x, a) ∈ g.lexical
  binaryRule x y z := (x, y, z) ∈ g.binary
  epsilonRule _ := False
  unitRule x y := (x, y) ∈ g.unary

/-- Language of the emitted code with its start rules and ε flag. -/
def codeLanguage (g : V116GrammarCode α) : Set (Word α) :=
  {w | (∃ x, x ∈ g.start ∧ BinaryNullableDerives (codeGrammar g) x w) ∨
    (w = [] ∧ g.epsilon = true)}

theorem code_to_finite (H : FixedFiniteMonoidHom α M) (ws : List (Word α))
    {x : Word α} {w : List α}
    (d : BinaryNullableDerives (codeGrammar (constructV116H H ws)) x w) :
    ∀ hx : ∃ p q, Observed ws.toFinset x p q,
      BinaryNullableDerives (finiteSubstringGrammar H ws.toFinset) ⟨x, hx⟩ w := by
  induction d with
  | @terminal x a h =>
      intro hx
      have h' : (x, a) ∈ (constructV116H H ws).lexical := h
      rw [constructV116H, mem_lexical] at h'
      exact BinaryNullableDerives.terminal h'.1
  | epsilon h => exact absurd h id
  | @unit x y w' h d ih =>
      intro hx
      have h' : (x, y) ∈ (constructV116H H ws).unary := h
      rw [constructV116H, mem_unary H.h H.map_nil H.map_append] at h'
      have hrel := (substringUnaryRelated_iff H ws x y).2 h'
      obtain ⟨p, q, _, hy⟩ := hrel.2
      have hu : (finiteSubstringGrammar H ws.toFinset).unitRule ⟨x, hx⟩ ⟨y, p, q, hy⟩ :=
        hrel
      exact BinaryNullableDerives.unit hu (ih ⟨p, q, hy⟩)
  | @binary x y z wy wz h dy dz ihy ihz =>
      intro hx
      have h' : (x, y, z) ∈ (constructV116H H ws).binary := h
      rw [constructV116H, mem_binary] at h'
      obtain ⟨hxyz, hy, hz, -⟩ := h'
      obtain ⟨p, q, hxne, hpxq⟩ := hx
      subst hxyz
      have hy' : Observed ws.toFinset y p (z ++ q) :=
        ⟨hy, by simpa only [List.append_assoc] using hpxq⟩
      have hz' : Observed ws.toFinset z (p ++ y) q :=
        ⟨hz, by simpa only [List.append_assoc] using hpxq⟩
      let B' : ObservedSubstringNonterminal ws.toFinset := ⟨y, p, z ++ q, hy'⟩
      let C' : ObservedSubstringNonterminal ws.toFinset := ⟨z, p ++ y, q, hz'⟩
      have hrule : (finiteSubstringGrammar H ws.toFinset).binaryRule
          ⟨y ++ z, p, q, hxne, hpxq⟩ B' C' := rfl
      exact BinaryNullableDerives.binary hrule (ihy ⟨p, z ++ q, hy'⟩)
        (ihz ⟨p ++ y, q, hz'⟩)

theorem finite_to_code (H : FixedFiniteMonoidHom α M) (ws : List (Word α))
    {A : ObservedSubstringNonterminal ws.toFinset} {w : List α}
    (d : BinaryNullableDerives (finiteSubstringGrammar H ws.toFinset) A w) :
    BinaryNullableDerives (codeGrammar (constructV116H H ws)) A.1 w := by
  induction d with
  | @terminal A a h =>
      apply BinaryNullableDerives.terminal
      show (A.1, a) ∈ (constructV116H H ws).lexical
      rw [constructV116H, mem_lexical]
      have h1 : A.1 = [a] := h
      obtain ⟨p, q, hobs⟩ := A.2
      refine ⟨h1, p, q, ?_⟩
      rw [← h1]
      exact (occursIn_iff_observed ws A.1 p q).2 hobs
  | epsilon h => exact absurd h id
  | @unit A B w' h d ih =>
      refine BinaryNullableDerives.unit ?_ ih
      show (A.1, B.1) ∈ (constructV116H H ws).unary
      rw [constructV116H, mem_unary H.h H.map_nil H.map_append]
      exact (substringUnaryRelated_iff H ws A.1 B.1).1 h
  | @binary A B C wB wC h dB dC ihB ihC =>
      refine BinaryNullableDerives.binary ?_ ihB ihC
      show (A.1, B.1, C.1) ∈ (constructV116H H ws).binary
      rw [constructV116H, mem_binary]
      obtain ⟨p, q, hobs⟩ := A.2
      exact ⟨h, observedSubstring_ne_nil _ B, observedSubstring_ne_nil _ C,
        p, q, (occursIn_iff_observed ws A.1 p q).2 hobs⟩

/-- **Theorem B.**  The grammar written by the constructor generates exactly
the language of the reconstruction operator `B_h(K)`. -/
theorem constructV116H_language (H : FixedFiniteMonoidHom α M)
    (ws : List (Word α)) :
    codeLanguage (constructV116H H ws) = BatchLanguage H ws.toFinset := by
  rw [← finiteSubstringBatchLanguage_eq_batchLanguage]
  ext w
  constructor
  · rintro (⟨x, hx, d⟩ | ⟨rfl, he⟩)
    · rw [constructV116H, mem_start] at hx
      have hobs : ∃ p q, Observed ws.toFinset x p q :=
        ⟨[], [], hx.2, by simpa [List.mem_toFinset] using hx.1⟩
      exact Or.inl ⟨⟨x, hobs⟩, List.mem_toFinset.2 hx.1, code_to_finite H ws d hobs⟩
    · rw [constructV116H, epsilon_iff] at he
      exact Or.inr ⟨rfl, List.mem_toFinset.2 he⟩
  · rintro (⟨A, hA, d⟩ | ⟨rfl, he⟩)
    · refine Or.inl ⟨A.1, ?_, finite_to_code H ws d⟩
      rw [constructV116H, mem_start]
      exact ⟨List.mem_toFinset.1 hA, observedSubstring_ne_nil _ A⟩
    · refine Or.inr ⟨rfl, ?_⟩
      rw [constructV116H, epsilon_iff]
      exact List.mem_toFinset.1 he

/-! ### Theorem C and the paper-facing statement -/

theorem inputNorm_eq_sampleNorm {ws : List (Word α)} (hnd : ws.Nodup) :
    inputNorm ws = reconstructionSampleNorm ws.toFinset := by
  unfold inputNorm reconstructionSampleNorm
  rw [List.sum_toFinset _ hnd]

/-- **Theorem C.** Quartic step bound in the sample norm `‖K‖`. -/
theorem constructV116HCost_le (H : FixedFiniteMonoidHom α M)
    {ws : List (Word α)} (hnd : ws.Nodup) :
    constructV116HCost H ws ≤ 1400 * (reconstructionSampleNorm ws.toFinset + 1) ^ 4 := by
  rw [← inputNorm_eq_sampleNorm hnd]
  exact constructV116Cost_le _ ws

/--
**`thm:poly-build` (v135), paper-facing.**  For a fixed finite-monoid typing
`H` (with decidable equality on `M`), every finite sample `K`, listed by any
duplicate-free list `ws`, is mapped by the executable constructor to a
grammar code that

1. declares exactly the observed factors as nonterminals and emits exactly
   the verified v116 (B), (U), (L), (S), (ε) rules;
2. generates exactly `BatchLanguage H K`, the language of `B_h(K)`;
3. is produced in at most `1400 · (‖K‖ + 1)^4` counted steps (cost model of
   `V135CostedPrimitives`), an absolute constant independent of `H`, `Σ`, `M`.

Every finite sample admits such a listing (`K.toList`).
-/
theorem thm_polyBuild (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) (ws : List (Word α))
    (hnd : ws.Nodup) (hK : ws.toFinset = K) :
    (∀ x, x ∈ (constructV116H H ws).nonterminals ↔ ∃ p q, Observed K x p q) ∧
    (∀ x y z, (x, y, z) ∈ (constructV116H H ws).binary ↔
      (x, (y, z)) ∈ v116EffectiveBinaryWordTable K) ∧
    (∀ x y, (x, y) ∈ (constructV116H H ws).unary ↔
      (x, y) ∈ v116UnaryRuleTable H K) ∧
    (∀ x a, (x, a) ∈ (constructV116H H ws).lexical ↔
      ∃ A : ObservedSubstringNonterminal K,
        (A, a) ∈ v116LexicalRuleTable K ∧ A.1 = x) ∧
    (∀ x, x ∈ (constructV116H H ws).start ↔
      ∃ A : ObservedSubstringNonterminal K,
        A ∈ v116StartRuleTable K ∧ A.1 = x) ∧
    ((constructV116H H ws).epsilon = true ↔ () ∈ v116EpsilonStartTable K) ∧
    codeLanguage (constructV116H H ws) = BatchLanguage H K ∧
    constructV116HCost H ws ≤ 1400 * (reconstructionSampleNorm K + 1) ^ 4 := by
  subst hK
  exact ⟨constructV116H_nonterminals_iff H ws,
    constructV116H_binary_iff H ws,
    constructV116H_unary_iff H ws,
    constructV116H_lexical_iff H ws,
    constructV116H_start_iff H ws,
    constructV116H_epsilon_iff H ws,
    constructV116H_language H ws,
    constructV116HCost_le H hnd⟩

/-- Every finite sample has a duplicate-free listing. -/
theorem exists_nodup_listing (K : Finset (Word α)) :
    ∃ ws : List (Word α), ws.Nodup ∧ ws.toFinset = K :=
  ⟨K.toList, K.nodup_toList, K.toList_toFinset⟩

end Bridge

end PolyBuild
end TCS1
end LeanCfgProject
