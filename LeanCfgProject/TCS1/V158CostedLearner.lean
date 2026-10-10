import LeanCfgProject.TCS1.V158CodeCYK
import LeanCfgProject.TCS1.V135CorIltV116
import LeanCfgProject.TCS1.ConcreteLearnerComplexity

/-!
# TCS #1 v158: an executable conservative learner with counted update cost

`thm:main`(iii) / `cor:ilt`: a conservative learner that identifies every target
in the class in the limit from positive data, with polynomial time per update.

**Learner state** (`State`): explicit lists
* `data` — the distinct positive examples seen so far;
* `cur` — the sample `K` of the current hypothesis;
* `code` — the v116 grammar code written for `cur` (`constructV116H`).

**Update** with a new example `w` (`updateC`), every operation counted:
1. membership test of `w` in the current written grammar (`CodeCYK.codeMemberC`,
   a CYK chart computed as a Horn closure);
2. duplicate test of `w` against `data` (`wordMemC`, letter-by-letter word
   comparison) and, if new, appending `w` (`appendC`, one step per copied cell);
3. *keep* (if `w` is generated): `cur` and `code` are unchanged;
   *rebuild* (otherwise): `cur := data` (shared, not copied) and the grammar is
   written again by the executable v116 constructor (`constructV116C`).
No `Finset` operation and no `Finset.toList` is used by the learner.

**Results.**
* `stateAt_spec`: after `n` examples, `data` lists `concreteAccumulatedSample datum n`
  without duplicates, `cur` lists the existing semantic hypothesis
  `materializedConservativeHypothesis H datum n` without duplicates, and `code`
  is the v116 code of `cur`; hence the written grammar generates
  `BatchLanguage H K_n` (`code_language`).  The learner therefore runs the
  existing semantic conservative learner exactly, with the samples kept as
  lists in arrival order (`cur` is *not* a canonical listing; only its set is
  the semantic hypothesis).
* `updateC_conservative`: if `w` is generated, the written grammar is unchanged.
* `costedLearner_gold`: Gold identification with syntactic stabilization of the
  written grammar code, transferred from the existing materialized learner.
* `updateCost_le`: every update costs at most `C · (P + 1)^20` steps, `P` the
  encoded size of all positive data seen so far (`positiveDataPrefixNorm`), for
  an absolute numeral `C`.
-/

namespace LeanCfgProject
namespace TCS1
namespace CostedLearner

open PolyBuild Horn SSBNFNorm CodeCYK

universe u v w q

section Learner

variable {α : Type v} [Fintype α] [DecidableEq α]
variable {M : Type q} [Monoid M] [Fintype M] [DecidableEq M]

/-- The learner state. -/
structure State (α : Type v) where
  data : List (Word α)
  cur : List (Word α)
  code : V116GrammarCode α

/-- Costed membership of a word in a list of words. -/
def wordMemC (w : Word α) : List (Word α) → Bool × Nat
  | [] => (false, 1)
  | v :: vs =>
      if (eqC w v).1 then (true, (eqC w v).2 + 1)
      else ((wordMemC w vs).1, (eqC w v).2 + (wordMemC w vs).2 + 1)

theorem wordMemC_fst (w : Word α) : ∀ l : List (Word α), (wordMemC w l).1 = decide (w ∈ l)
  | [] => by simp [wordMemC]
  | v :: vs => by
      unfold wordMemC
      by_cases h : w = v
      · subst h
        have : (eqC w w).1 = true := by rw [eqC_fst]; simp
        simp [this]
      · have : (eqC w v).1 = false := by rw [eqC_fst]; simp [h]
        simp [this, wordMemC_fst w vs, h]

theorem wordMemC_snd_le (w : Word α) :
    ∀ l : List (Word α), (wordMemC w l).2 ≤ l.length * (w.length + 2) + 1
  | [] => by simp [wordMemC]
  | v :: vs => by
      have h1 := eqC_snd_le w v
      have h2 := wordMemC_snd_le w vs
      have e : (vs.length + 1) * (w.length + 2) = vs.length * (w.length + 2) + w.length + 2 := by
        ring
      unfold wordMemC
      split_ifs
      · simp only [List.length_cons]; rw [e]; omega
      · simp only [List.length_cons]; rw [e]; omega

variable (H : FixedFiniteMonoidHom α M)

/-- Initial state: no data, empty hypothesis, the code of the empty sample. -/
def init : State α := ⟨[], [], constructV116H H []⟩

/-- New data list after `w`. -/
def newData (s : State α) (w : Word α) : List (Word α) :=
  if (wordMemC w s.data).1 then s.data else (appendC s.data [w]).1

/-- **One update, with its step count.** -/
def updateC (s : State α) (w : Word α) : State α × Nat :=
  if (codeMemberC s.code w).1 then
    (⟨newData s w, s.cur, s.code⟩,
      (codeMemberC s.code w).2 + (wordMemC w s.data).2 +
        (if (wordMemC w s.data).1 then 0 else (appendC s.data [w]).2) + 1)
  else
    (⟨newData s w, newData s w, (constructV116C (fun a => H.h [a]) (newData s w)).1⟩,
      (codeMemberC s.code w).2 + (wordMemC w s.data).2 +
        (if (wordMemC w s.data).1 then 0 else (appendC s.data [w]).2) +
        (constructV116C (fun a => H.h [a]) (newData s w)).2 + 1)

/-- The state after the examples `datum 1, …, datum n`. -/
def stateAt (datum : Nat → Word α) : Nat → State α
  | 0 => init H
  | n + 1 => (updateC H (stateAt datum n) (datum (n + 1))).1

/-- Step count of the `(n+1)`-st update. -/
def updateCost (datum : Nat → Word α) (n : Nat) : Nat :=
  (updateC H (stateAt H datum n) (datum (n + 1))).2

/-! ### The learner runs the existing semantic learner -/

theorem newData_spec (s : State α) (w : Word α) (hnd : s.data.Nodup) :
    (newData s w).Nodup ∧ (newData s w).toFinset = insert w s.data.toFinset := by
  unfold newData
  rw [wordMemC_fst]
  by_cases h : w ∈ s.data
  · simp only [h, decide_true, if_true]
    exact ⟨hnd, by rw [Finset.insert_eq_of_mem (List.mem_toFinset.mpr h)]⟩
  · simp only [h, decide_false, Bool.false_eq_true, if_false, appendC_fst]
    refine ⟨List.Nodup.append hnd (List.nodup_singleton w) ?_, ?_⟩
    · intro x hx hy
      simp only [List.mem_singleton] at hy
      subst hy
      exact h hx
    · ext x
      simp [or_comm]

theorem updateC_code_member (s : State α) (w : Word α) (hm : (codeMemberC s.code w).1 = true) :
    (updateC H s w).1 = ⟨newData s w, s.cur, s.code⟩ := by
  simp [updateC, hm]

theorem updateC_code_nonmember (s : State α) (w : Word α)
    (hm : (codeMemberC s.code w).1 = false) :
    (updateC H s w).1 =
      ⟨newData s w, newData s w, constructV116H H (newData s w)⟩ := by
  simp [updateC, hm, constructV116H, constructV116]

/-- **Invariant**: the explicit lists represent the semantic learner's sets. -/
theorem stateAt_spec (datum : Nat → Word α) :
    ∀ n,
      (stateAt H datum n).data.Nodup ∧
      (stateAt H datum n).data.toFinset = concreteAccumulatedSample datum n ∧
      (stateAt H datum n).cur.Nodup ∧
      (stateAt H datum n).cur.toFinset = materializedConservativeHypothesis H datum n ∧
      (stateAt H datum n).code = constructV116H H (stateAt H datum n).cur
  | 0 => by simp [stateAt, init]
  | n + 1 => by
      obtain ⟨hd1, hd2, hc1, hc2, hc3⟩ := stateAt_spec datum n
      set s := stateAt H datum n with hs
      set w := datum (n + 1) with hw
      have hstep : stateAt H datum (n + 1) = (updateC H s w).1 := rfl
      obtain ⟨hn1, hn2⟩ := newData_spec s w hd1
      have hacc : concreteAccumulatedSample datum (n + 1) = insert w (concreteAccumulatedSample datum n) :=
        rfl
      have hK : materializedConservativeHypothesis H datum (n + 1) =
          materializedConservativeUpdate H (materializedConservativeHypothesis H datum n)
            (concreteAccumulatedSample datum (n + 1)) w := rfl
      have hlang : (codeMemberC s.code w).1 = true ↔
          w ∈ BatchLanguage H (materializedConservativeHypothesis H datum n) := by
        rw [codeMemberC_correct, hc3, constructV116H_language, hc2]
      rw [hstep]
      cases hm : (codeMemberC s.code w).1 with
      | true =>
          rw [updateC_code_member H s w hm]
          have hgen := hlang.mp hm
          rw [hK, materializedConservativeUpdate_keep H _ _ w hgen]
          refine ⟨hn1, ?_, hc1, hc2, hc3⟩
          show (newData s w).toFinset = _
          rw [hn2, hd2, hacc]
      | false =>
          rw [updateC_code_nonmember H s w hm]
          have hmiss : w ∉ BatchLanguage H (materializedConservativeHypothesis H datum n) := by
            intro h; rw [← hlang] at h; rw [hm] at h; cases h
          rw [hK, materializedConservativeUpdate_rebuild H _ _ w hmiss]
          refine ⟨hn1, ?_, hn1, ?_, rfl⟩
          · show (newData s w).toFinset = _
            rw [hn2, hd2, hacc]
          · show (newData s w).toFinset = _
            rw [hn2, hd2, hacc]

/-- The written grammar generates the semantic hypothesis language. -/
theorem code_language (datum : Nat → Word α) (n : Nat) :
    codeLanguage (stateAt H datum n).code =
      BatchLanguage H (materializedConservativeHypothesis H datum n) := by
  obtain ⟨_, _, _, hc2, hc3⟩ := stateAt_spec H datum n
  rw [hc3, constructV116H_language, hc2]

/-- **Conservativeness**: a generated example leaves the written grammar unchanged. -/
theorem updateC_conservative (s : State α) (w : Word α) (hw : w ∈ codeLanguage s.code) :
    (updateC H s w).1.code = s.code ∧ (updateC H s w).1.cur = s.cur := by
  have hm : (codeMemberC s.code w).1 = true := (codeMemberC_correct s.code w).mpr hw
  rw [updateC_code_member H s w hm]
  exact ⟨rfl, rfl⟩

/-- If the semantic hypothesis does not change, neither does the written grammar. -/
theorem stateAt_stable_of_hyp (datum : Nat → Word α) (n : Nat)
    (hst : materializedConservativeHypothesis H datum (n + 1) =
      materializedConservativeHypothesis H datum n) :
    (stateAt H datum (n + 1)).code = (stateAt H datum n).code ∧
      (stateAt H datum (n + 1)).cur = (stateAt H datum n).cur := by
  obtain ⟨hd1, hd2, hc1, hc2, hc3⟩ := stateAt_spec H datum n
  have hstep : stateAt H datum (n + 1) = (updateC H (stateAt H datum n) (datum (n + 1))).1 := rfl
  cases hm : (codeMemberC (stateAt H datum n).code (datum (n + 1))).1 with
  | true =>
      rw [hstep, updateC_code_member H _ _ hm]
      exact ⟨rfl, rfl⟩
  | false =>
      exfalso
      have hmiss : datum (n + 1) ∉
          BatchLanguage H (materializedConservativeHypothesis H datum n) := by
        intro h
        have : (codeMemberC (stateAt H datum n).code (datum (n + 1))).1 = true := by
          rw [codeMemberC_correct, hc3, constructV116H_language, hc2]; exact h
        rw [hm] at this; cases this
      have hreb : materializedConservativeHypothesis H datum (n + 1) =
          concreteAccumulatedSample datum (n + 1) :=
        materializedConservativeUpdate_rebuild H _ _ _ hmiss
      have hin : datum (n + 1) ∈ materializedConservativeHypothesis H datum n := by
        rw [← hst, hreb]
        exact Finset.mem_insert_self _ _
      exact hmiss (sample_consistency H _ hin)

/-- **Gold identification of the costed learner**, with syntactic stabilization
of the written grammar code. -/
theorem costedLearner_gold {N : Type u} {P : Type w} [Fintype N] [Fintype P] [DecidableEq N]
    (G : IndexedMixedCFG N α P) (S : N)
    (hsub : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S))
    (datum : Nat → Word α)
    (hpos : ∀ n, datum n ∈ MixedNonterminalLanguage G.toMixedRules S)
    (hcov : ∀ x, x ∈ MixedNonterminalLanguage G.toMixedRules S →
      ∃ n, x ∈ concreteAccumulatedSample datum n) :
    ∃ m, (∀ j, (stateAt H datum (m + j)).code = (stateAt H datum m).code) ∧
      codeLanguage (stateAt H datum m).code = MixedNonterminalLanguage G.toMixedRules S := by
  have hEqL := leastClosedLanguage_eq_mixedNonterminalLanguage G.toMixedRules S
  have hsub' : FixedHSubstitutable H (LeastClosedLanguage G.toMixedRules S) := by
    rw [hEqL]; exact hsub
  have hpos' : ∀ n, datum n ∈ LeastClosedLanguage G.toMixedRules S := by
    intro n; rw [hEqL]; exact hpos n
  have hcov' : ∀ x, x ∈ LeastClosedLanguage G.toMixedRules S →
      ∃ n, x ∈ concreteAccumulatedSample datum n := by
    intro x hx; rw [hEqL] at hx; exact hcov x hx
  obtain ⟨_, _, _, hgold⟩ :=
    indexedFixedH_learning_materialized_core H G S hsub' datum hpos' hcov'
  rw [hEqL] at hgold
  -- a stable semantic hypothesis from some point on
  have key : ∃ m, (∀ j, materializedConservativeHypothesis H datum (m + j) =
      materializedConservativeHypothesis H datum m) ∧
      BatchLanguage H (materializedConservativeHypothesis H datum m) =
        MixedNonterminalLanguage G.toMixedRules S := by
    obtain ⟨n₀, h⟩ := hgold
    rcases h with ⟨hL, hst⟩ | ⟨n, _, _, hL, hst⟩
    · exact ⟨n₀, hst, hL⟩
    · exact ⟨n + 1, hst, hL⟩
  obtain ⟨m, hst, hL⟩ := key
  refine ⟨m, ?_, by rw [code_language, hL]⟩
  intro j
  induction j with
  | zero => rfl
  | succ j ih =>
      have h1 := hst (j + 1)
      have h2 := hst j
      have hstep := (stateAt_stable_of_hyp H datum (m + j) (by
        rw [show m + j + 1 = m + (j + 1) by omega, h1, h2])).1
      rw [show m + (j + 1) = m + j + 1 by omega, hstep, ih]

/-! ### Update cost -/

theorem forListC_len_le_cost {β γ : Type*} (f : β → List γ × Nat) (l : List β)
    (h : ∀ b, b ∈ l → (f b).1.length ≤ (f b).2) :
    (forListC f l).1.length ≤ (forListC f l).2 :=
  (forListC_bound f (fun b => (f b).2) l (fun b hb => ⟨h b hb, le_refl _⟩)).1

/-- Every rule list written by the constructor is at most its step count. -/
theorem constructV116C_lists_le (ha : α → M) (ws : List (Word α)) :
    (constructV116C ha ws).1.lexical.length ≤ (constructV116C ha ws).2 ∧
    (constructV116C ha ws).1.unary.length ≤ (constructV116C ha ws).2 ∧
    (constructV116C ha ws).1.binary.length ≤ (constructV116C ha ws).2 ∧
    (constructV116C ha ws).1.start.length ≤ (constructV116C ha ws).2 := by
  have hB := forListC_len_le_cost binaryWord ws (fun w _ => (binaryWord_bound w).1)
  have hL := forListC_len_le_cost lexicalWord ws (fun w _ => (lexicalWord_bound w).1)
  have hU := forListC_len_le_cost (fun w => forListC (fun w' => unaryPair ha w w') ws) ws
    (fun w _ => forListC_len_le_cost _ ws (fun w' _ => (unaryPair_bound ha w w').1))
  have hS := forListC_len_le_cost startBody ws (fun w _ => by
    cases w <;> simp [startBody, startEmit])
  show (forListC lexicalWord ws).1.length ≤ _ ∧
    (forListC (fun w => forListC (fun w' => unaryPair ha w w') ws) ws).1.length ≤ _ ∧
    (forListC binaryWord ws).1.length ≤ _ ∧ (forListC startBody ws).1.length ≤ _
  simp only [constructV116C]
  refine ⟨by omega, by omega, by omega, by omega⟩

theorem occursIn_length_le {ws : List (Word α)} {x p q : Word α} (h : OccursIn ws x p q) :
    x.length ≤ inputNorm ws := by
  have := le_inputNorm h.2
  simp only [List.length_append] at this
  omega

/-- Names in the written code are no longer than the sample norm. -/
theorem constructV116H_nameBound (ws : List (Word α)) :
    NameBound (constructV116H H ws) (inputNorm ws) where
  lexical p hp := by
    have hp' : (p.1, p.2) ∈ (constructV116 (fun a => H.h [a]) ws).lexical := hp
    obtain ⟨hx, p0, q0, hocc⟩ := (mem_lexical _ ws p.1 p.2).mp hp'
    rw [hx]
    exact occursIn_length_le hocc
  unary p hp := by
    have hp' : (p.1, p.2) ∈ (constructV116 (fun a => H.h [a]) ws).unary := hp
    obtain ⟨_, p0, q0, h1, h2⟩ := (mem_unary H.h H.map_nil H.map_append ws p.1 p.2).mp hp'
    exact ⟨occursIn_length_le h1, occursIn_length_le h2⟩
  binary t ht := by
    have ht' : (t.1, t.2.1, t.2.2) ∈ (constructV116 (fun a => H.h [a]) ws).binary := ht
    obtain ⟨he, _, _, p0, q0, hocc⟩ := (mem_binary _ ws t.1 t.2.1 t.2.2).mp ht'
    have := occursIn_length_le hocc
    rw [he, List.length_append] at this
    rw [he, List.length_append]
    omega
  start x hx := by
    have hx' : x ∈ (constructV116 (fun a => H.h [a]) ws).start := hx
    obtain ⟨hmem, _⟩ := (mem_start _ ws x).mp hx'
    have := le_inputNorm hmem
    omega

theorem constructV116H_codeSize (ws : List (Word α)) :
    CodeSize (constructV116H H ws) (1400 * (inputNorm ws + 1) ^ 4) := by
  obtain ⟨h1, h2, h3, h4⟩ := constructV116C_lists_le (fun a => H.h [a]) ws
  have hc := constructV116Cost_le (fun a => H.h [a]) ws
  unfold constructV116Cost at hc
  exact ⟨le_trans h1 hc, le_trans h2 hc, le_trans h3 hc, le_trans h4 hc⟩

/-- Sample norms of nodup lists listing the learner's sets. -/
theorem inputNorm_cur_le (datum : Nat → Word α) (n : Nat) :
    inputNorm (stateAt H datum n).cur ≤ positiveDataPrefixNorm datum n := by
  obtain ⟨_, _, hc1, hc2, _⟩ := stateAt_spec H datum n
  rw [inputNorm_eq_sampleNorm hc1, hc2, materializedConservativeHypothesis_eq_executable,
    executableConservativeHypothesis_eq_concrete]
  exact concreteConservativeHypothesis_norm_le_prefix H datum n

theorem inputNorm_data_le (datum : Nat → Word α) (n : Nat) :
    inputNorm (stateAt H datum n).data ≤ positiveDataPrefixNorm datum n := by
  obtain ⟨hd1, hd2, _, _, _⟩ := stateAt_spec H datum n
  rw [inputNorm_eq_sampleNorm hd1, hd2]
  exact concreteAccumulatedSample_norm_le_prefix datum n

theorem length_le_inputNorm (ws : List (Word α)) : ws.length ≤ inputNorm ws := by
  unfold inputNorm
  exact length_le_sum_map_succ ws (fun w => w.length)

/--
**Update cost.**  The `(n+1)`-st update (membership test in the written grammar,
duplicate test, list append, and possibly writing a new grammar) takes at most
`4·10¹⁶ · (P + 1)^20` steps, `P` the encoded size of the positive data
`datum 1, …, datum (n+1)` seen so far.
-/
theorem updateCost_le (datum : Nat → Word α) (n : Nat) :
    updateCost H datum n ≤
      40000000000000000 * (positiveDataPrefixNorm datum (n + 1) + 1) ^ 20 := by
  set P := positiveDataPrefixNorm datum (n + 1) with hP
  set s := stateAt H datum n with hs
  set w := datum (n + 1) with hw
  obtain ⟨hd1, hd2, hc1, hc2, hc3⟩ := stateAt_spec H datum n
  have hPn : positiveDataPrefixNorm datum (n + 1) =
      positiveDataPrefixNorm datum n + (w.length + 1) := rfl
  have hcur := inputNorm_cur_le H datum n
  have hdat := inputNorm_data_le H datum n
  have hdl := length_le_inputNorm s.data
  -- membership test
  set Cc := 1400 * (inputNorm s.cur + 1) ^ 4 with hCc
  have hsz : CodeSize s.code Cc := by rw [hc3]; exact constructV116H_codeSize H s.cur
  have hnb : NameBound s.code (inputNorm s.cur) := by rw [hc3]; exact constructV116H_nameBound H s.cur
  have hmem := codeMemberC_cost_le w hsz hnb
  -- duplicate test and append
  have hwm := wordMemC_snd_le w s.data
  have hap : (appendC s.data [w]).2 = s.data.length + 1 := appendC_snd _ _
  -- rebuild
  obtain ⟨hn1, hn2⟩ := newData_spec s w hd1
  have hnd : inputNorm (newData s w) ≤ P := by
    rw [inputNorm_eq_sampleNorm hn1, hn2, hd2]
    have := concreteAccumulatedSample_norm_le_prefix datum (n + 1)
    exact this
  have hreb := constructV116Cost_le (fun a => H.h [a]) (newData s w)
  unfold constructV116Cost at hreb
  -- monomials in P
  have hP1 : 1 ≤ P + 1 := by omega
  have hcP : inputNorm s.cur ≤ P := by omega
  have hwP : w.length + 1 ≤ P + 1 := by omega
  have hCc : Cc + 1 ≤ 1401 * (P + 1) ^ 4 := by
    have : (inputNorm s.cur + 1) ^ 4 ≤ (P + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have : 1 ≤ (P + 1) ^ 4 := Nat.one_le_pow _ _ hP1
    omega
  have hm2 : (codeMemberC s.code w).2 ≤ 21999073608000000 * (P + 1) ^ 20 := by
    refine le_trans hmem ?_
    calc 2000000 * ((Cc + 1) ^ 3 * (w.length + 1) ^ 7 * (inputNorm s.cur + 4))
        ≤ 2000000 * ((1401 * (P + 1) ^ 4) ^ 3 * (P + 1) ^ 7 * (4 * (P + 1))) := by
          gcongr <;> omega
      _ = 21999073608000000 * (P + 1) ^ 20 := by ring
  have hX1 : P + 1 ≤ (P + 1) ^ 20 := by
    calc P + 1 = (P + 1) ^ 1 := (pow_one _).symm
      _ ≤ (P + 1) ^ 20 := Nat.pow_le_pow_right hP1 (by omega)
  have hX2 : (P + 1) * (P + 1) ≤ (P + 1) ^ 20 := by
    calc (P + 1) * (P + 1) = (P + 1) ^ 2 := by ring
      _ ≤ (P + 1) ^ 20 := Nat.pow_le_pow_right hP1 (by omega)
  have hX4 : (P + 1) ^ 4 ≤ (P + 1) ^ 20 := Nat.pow_le_pow_right hP1 (by omega)
  have hwm' : (wordMemC w s.data).2 ≤ 2 * ((P + 1) * (P + 1)) := by
    refine le_trans hwm ?_
    have : s.data.length * (w.length + 2) ≤ (P + 1) * (P + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have : 1 ≤ (P + 1) * (P + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hreb' : (constructV116C (fun a => H.h [a]) (newData s w)).2 ≤ 1400 * (P + 1) ^ 4 := by
    refine le_trans hreb ?_
    have : (inputNorm (newData s w) + 1) ^ 4 ≤ (P + 1) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  show (updateC H s w).2 ≤ _
  unfold updateC
  split_ifs <;> simp only [] <;> omega

end Learner

end CostedLearner
end TCS1
end LeanCfgProject
