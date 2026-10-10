import LeanCfgProject.TCS1.V144SSBNFBridge
import LeanCfgProject.TCS1.Proposition74IndexedPackage

/-!
# TCS #1 v144: executable front end (fresh-start convention, terminal isolation, binarization)

Input: explicit lists `nts` (nonterminals), `alph` (letters) and `prs`
(productions `(A, rhs)`).  The front end writes the binary grammar with ε and
unit rules of the existing semantic front end `frontEndBinaryGrammar`
(terminal isolation by wrapper states `old (inr a)`, then binarization by
suffix states `suffix xs`), restricted to the existing finite support
`indexedClosedFrontSupport`.

* states: `old (inl A)` for `A ∈ nts`, `old (inr a)` for `a ∈ alph`, and
  `suffix (rhs.drop i)` for every production and every `i < |rhs|`;
* terminal rules: `old (inl A) → a` for `A → a`, and `old (inr a) → a`;
* binary rules: `old (inl A) → old B old C` for `A → B C`,
  `old (inl A) → old B suffix(C D …)` for longer right-hand sides, and for
  each suffix state `suffix [B, C] → old B old C`,
  `suffix (B :: C :: D :: rest) → old B suffix (C :: D :: rest)`;
* unit rules: `old (inl A) → old (inl B)` for `A → B`, `suffix [B] → old B`;
* ε rules: `old (inl A)` for `A → ε`.

**Cost model** (as in `V144SSBNFNormalizer`).  A suffix state is a pointer to
a tail of the input right-hand side: walking the right-hand side visits one
cell per suffix (2 steps: visit and output cell).  Examining the first three
cells of a right-hand side or suffix and emitting one constant-size rule
record costs a constant (2–5 steps).  State comparison `stateEqC` compares
two `old` states in one step (symbol comparison: word-RAM unit cost for
nonterminal/letter indices) and two suffix states cell by cell
(`PolyBuild.eqC`).

`codeMatches_indexed`: for complete listings of an `IndexedMixedCFG`, the
written code lists exactly the states and rules of the existing finite
front-end grammar `indexedFiniteFrontEndGrammar G`.
-/

namespace LeanCfgProject
namespace TCS1
namespace SSBNFNorm

open Horn PolyBuild

universe u v w

section StateEq

variable {N : Type u} {α : Type v} [DecidableEq N] [DecidableEq α]

/-- Costed comparison of front-end states. -/
def stateEqC : FrontEndState N α → FrontEndState N α → Bool × Nat
  | BinarizedState.old X, BinarizedState.old Y => (decide (X = Y), 1)
  | BinarizedState.suffix xs, BinarizedState.suffix ys => eqC xs ys
  | BinarizedState.old _, BinarizedState.suffix _ => (false, 1)
  | BinarizedState.suffix _, BinarizedState.old _ => (false, 1)

theorem stateEqC_correct : CeqCorrect (stateEqC (N := N) (α := α)) := by
  intro x y
  cases x <;> cases y <;> simp [stateEqC, eqC_fst]

/-- Length of the suffix carried by a state (0 for old states). -/
def stateLen : FrontEndState N α → Nat
  | BinarizedState.old _ => 0
  | BinarizedState.suffix xs => xs.length

theorem stateEqC_snd_le (x y : FrontEndState N α) :
    (stateEqC x y).2 ≤ stateLen x + 1 := by
  cases x <;> cases y <;> simp [stateEqC, stateLen]
  exact eqC_snd_le _ _

end StateEq

section Defs

variable {N : Type u} {α : Type v}

/-- One suffix state per nonempty tail (tails are shared pointers). -/
def suffixStatesC : List (MixedSymbol N α) → List (FrontEndState N α) × Nat
  | [] => ([], 1)
  | x :: xs =>
      (BinarizedState.suffix (x :: xs) :: (suffixStatesC xs).1, (suffixStatesC xs).2 + 2)

/-- Terminal rule of a production `A → a`. -/
def termOfProd (pr : N × List (MixedSymbol N α)) : List (FrontEndState N α × α) :=
  match pr.2 with
  | [Sum.inr a] => [(BinarizedState.old (Sum.inl pr.1), a)]
  | _ => []

/-- Top binary rule of a production with at least two symbols. -/
def binOfProd (pr : N × List (MixedSymbol N α)) :
    List (FrontEndState N α × FrontEndState N α × FrontEndState N α) :=
  match pr.2 with
  | [B, C] => [(BinarizedState.old (Sum.inl pr.1), BinarizedState.old B, BinarizedState.old C)]
  | B :: C :: D :: rest =>
      [(BinarizedState.old (Sum.inl pr.1), BinarizedState.old B,
        BinarizedState.suffix (C :: D :: rest))]
  | _ => []

/-- Unit rule of a production `A → B`. -/
def unitOfProd (pr : N × List (MixedSymbol N α)) :
    List (FrontEndState N α × FrontEndState N α) :=
  match pr.2 with
  | [Sum.inl B] => [(BinarizedState.old (Sum.inl pr.1), BinarizedState.old (Sum.inl B))]
  | _ => []

/-- ε rule of a production `A → ε`. -/
def epsOfProd (pr : N × List (MixedSymbol N α)) : List (FrontEndState N α) :=
  match pr.2 with
  | [] => [BinarizedState.old (Sum.inl pr.1)]
  | _ => []

/-- Binary rule of a suffix state. -/
def binOfSuffix (X : FrontEndState N α) :
    List (FrontEndState N α × FrontEndState N α × FrontEndState N α) :=
  match X with
  | BinarizedState.suffix [B, C] => [(X, BinarizedState.old B, BinarizedState.old C)]
  | BinarizedState.suffix (B :: C :: D :: rest) =>
      [(X, BinarizedState.old B, BinarizedState.suffix (C :: D :: rest))]
  | _ => []

/-- Unit rule of a suffix state of length one. -/
def unitOfSuffix (X : FrontEndState N α) : List (FrontEndState N α × FrontEndState N α) :=
  match X with
  | BinarizedState.suffix [B] => [(X, BinarizedState.old B)]
  | _ => []

/-- Suffix states of all productions (one pass over every right-hand side). -/
def feSufC (prs : List (N × List (MixedSymbol N α))) : List (FrontEndState N α) × Nat :=
  forListC (fun pr : N × List (MixedSymbol N α) => suffixStatesC pr.2) prs

/-- All front-end states. -/
def feStatesC (nts : List N) (alph : List α) (prs : List (N × List (MixedSymbol N α))) :
    List (FrontEndState N α) × Nat :=
  ((appendC (mapC (fun A : N => (BinarizedState.old (Sum.inl A) : FrontEndState N α)) nts).1
      (appendC (mapC (fun a : α => (BinarizedState.old (Sum.inr a) : FrontEndState N α))
        alph).1 (feSufC prs).1).1).1,
    (mapC (fun A : N => (BinarizedState.old (Sum.inl A) : FrontEndState N α)) nts).2 +
    (mapC (fun a : α => (BinarizedState.old (Sum.inr a) : FrontEndState N α)) alph).2 +
    (appendC (mapC (fun a : α => (BinarizedState.old (Sum.inr a) : FrontEndState N α))
        alph).1 (feSufC prs).1).2 +
    (appendC (mapC (fun A : N => (BinarizedState.old (Sum.inl A) : FrontEndState N α)) nts).1
      (appendC (mapC (fun a : α => (BinarizedState.old (Sum.inr a) : FrontEndState N α))
        alph).1 (feSufC prs).1).1).2)

/-- Terminal rules. -/
def feTermC (alph : List α) (prs : List (N × List (MixedSymbol N α))) :
    List (FrontEndState N α × α) × Nat :=
  ((appendC (forListC (fun pr => (termOfProd pr, 3)) prs).1
      (mapC (fun a : α => ((BinarizedState.old (Sum.inr a) : FrontEndState N α), a)) alph).1).1,
    (forListC (fun pr => (termOfProd pr, 3)) prs).2 +
    (mapC (fun a : α => ((BinarizedState.old (Sum.inr a) : FrontEndState N α), a)) alph).2 +
    (appendC (forListC (fun pr => (termOfProd pr, 3)) prs).1
      (mapC (fun a : α => ((BinarizedState.old (Sum.inr a) : FrontEndState N α), a)) alph).1).2)

/-- Binary rules. -/
def feBinC (prs : List (N × List (MixedSymbol N α))) :
    List (FrontEndState N α × FrontEndState N α × FrontEndState N α) × Nat :=
  ((appendC (forListC (fun pr => (binOfProd pr, 5)) prs).1
      (forListC (fun X => (binOfSuffix X, 5)) (feSufC prs).1).1).1,
    (forListC (fun pr => (binOfProd pr, 5)) prs).2 +
    (forListC (fun X => (binOfSuffix X, 5)) (feSufC prs).1).2 +
    (appendC (forListC (fun pr => (binOfProd pr, 5)) prs).1
      (forListC (fun X => (binOfSuffix X, 5)) (feSufC prs).1).1).2)

/-- Unit rules. -/
def feUnitC (prs : List (N × List (MixedSymbol N α))) :
    List (FrontEndState N α × FrontEndState N α) × Nat :=
  ((appendC (forListC (fun pr => (unitOfProd pr, 3)) prs).1
      (forListC (fun X => (unitOfSuffix X, 3)) (feSufC prs).1).1).1,
    (forListC (fun pr => (unitOfProd pr, 3)) prs).2 +
    (forListC (fun X => (unitOfSuffix X, 3)) (feSufC prs).1).2 +
    (appendC (forListC (fun pr => (unitOfProd pr, 3)) prs).1
      (forListC (fun X => (unitOfSuffix X, 3)) (feSufC prs).1).1).2)

/-- ε rules. -/
def feEpsC (prs : List (N × List (MixedSymbol N α))) : List (FrontEndState N α) × Nat :=
  forListC (fun pr => (epsOfProd pr, 2)) prs

/-- The front end: the written code and its step count. -/
def frontCodeC (nts : List N) (alph : List α) (prs : List (N × List (MixedSymbol N α))) :
    FrontCode (FrontEndState N α) α × Nat :=
  ({ states := (feStatesC nts alph prs).1, term := (feTermC alph prs).1,
     bin := (feBinC prs).1, unit := (feUnitC prs).1, eps := (feEpsC prs).1 },
    (feSufC prs).2 + (feStatesC nts alph prs).2 + (feTermC alph prs).2 + (feBinC prs).2 +
      (feUnitC prs).2 + (feEpsC prs).2 + 1)

/-- The suffix states of all productions. -/
def allSuffixStates (prs : List (N × List (MixedSymbol N α))) : List (FrontEndState N α) :=
  (feSufC prs).1

theorem frontCode_states (nts : List N) (alph : List α) (prs) :
    (frontCodeC nts alph prs).1.states =
      nts.map (fun A => BinarizedState.old (Sum.inl A)) ++
        (alph.map (fun a => BinarizedState.old (Sum.inr a)) ++ allSuffixStates prs) := by
  simp [frontCodeC, feStatesC, appendC_fst, mapC_fst, allSuffixStates]

theorem frontCode_term (nts : List N) (alph : List α) (prs) :
    (frontCodeC nts alph prs).1.term =
      (forListC (fun pr => (termOfProd pr, 3)) prs).1 ++
        alph.map (fun a => (BinarizedState.old (Sum.inr a), a)) := by
  simp [frontCodeC, feTermC, appendC_fst, mapC_fst]

theorem frontCode_bin (nts : List N) (alph : List α) (prs) :
    (frontCodeC nts alph prs).1.bin =
      (forListC (fun pr => (binOfProd pr, 5)) prs).1 ++
        (forListC (fun X => (binOfSuffix X, 5)) (allSuffixStates prs)).1 := by
  simp [frontCodeC, feBinC, appendC_fst, allSuffixStates]

theorem frontCode_unit (nts : List N) (alph : List α) (prs) :
    (frontCodeC nts alph prs).1.unit =
      (forListC (fun pr => (unitOfProd pr, 3)) prs).1 ++
        (forListC (fun X => (unitOfSuffix X, 3)) (allSuffixStates prs)).1 := by
  simp [frontCodeC, feUnitC, appendC_fst, allSuffixStates]

theorem frontCode_eps (nts : List N) (alph : List α) (prs) :
    (frontCodeC nts alph prs).1.eps = (forListC (fun pr => (epsOfProd pr, 2)) prs).1 := by
  simp [frontCodeC, feEpsC]

end Defs

/-! ### Membership in the written lists -/

section Membership

variable {N : Type u} {α : Type v}

theorem mem_suffixStatesC (X : FrontEndState N α) :
    ∀ r : List (MixedSymbol N α),
      X ∈ (suffixStatesC r).1 ↔ ∃ i, i < r.length ∧ X = BinarizedState.suffix (r.drop i)
  | [] => by simp [suffixStatesC]
  | x :: xs => by
      show X ∈ BinarizedState.suffix (x :: xs) :: (suffixStatesC xs).1 ↔ _
      rw [List.mem_cons, mem_suffixStatesC X xs]
      constructor
      · rintro (rfl | ⟨i, hi, rfl⟩)
        · exact ⟨0, by simp, rfl⟩
        · exact ⟨i + 1, by simp; omega, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        cases i with
        | zero => exact Or.inl rfl
        | succ i => exact Or.inr ⟨i, by simp at hi; omega, rfl⟩

theorem mem_allSuffixStates (prs : List (N × List (MixedSymbol N α))) (X : FrontEndState N α) :
    X ∈ allSuffixStates prs ↔
      ∃ pr, pr ∈ prs ∧ ∃ i, i < pr.2.length ∧ X = BinarizedState.suffix (pr.2.drop i) := by
  unfold allSuffixStates feSufC
  rw [mem_forListC]
  simp only [mem_suffixStatesC]

theorem forListC_const_mem {β γ : Type*} (f : β → List γ) (c : Nat) (l : List β) (x : γ) :
    x ∈ (forListC (fun b => (f b, c)) l).1 ↔ ∃ b, b ∈ l ∧ x ∈ f b := by
  rw [mem_forListC]

theorem mem_termOfProd (pr : N × List (MixedSymbol N α)) (x : FrontEndState N α) (a : α) :
    (x, a) ∈ termOfProd pr ↔ pr.2 = [Sum.inr a] ∧ x = BinarizedState.old (Sum.inl pr.1) := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [termOfProd]
  · rcases s with B | b
    · simp [termOfProd]
    · simp [termOfProd]; tauto
  · simp [termOfProd]

theorem mem_binOfProd (pr : N × List (MixedSymbol N α)) (x y z : FrontEndState N α) :
    (x, y, z) ∈ binOfProd pr ↔
      x = BinarizedState.old (Sum.inl pr.1) ∧
      ((∃ B C, pr.2 = [B, C] ∧ y = BinarizedState.old B ∧ z = BinarizedState.old C) ∨
        (∃ B C D rest, pr.2 = B :: C :: D :: rest ∧ y = BinarizedState.old B ∧
          z = BinarizedState.suffix (C :: D :: rest))) := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩
  · simp [binOfProd]
  · simp [binOfProd]
  · simp [binOfProd]; tauto
  · simp [binOfProd]; tauto

theorem mem_unitOfProd (pr : N × List (MixedSymbol N α)) (x y : FrontEndState N α) :
    (x, y) ∈ unitOfProd pr ↔
      ∃ B, pr.2 = [Sum.inl B] ∧ x = BinarizedState.old (Sum.inl pr.1) ∧
        y = BinarizedState.old (Sum.inl B) := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [unitOfProd]
  · rcases s with B | b
    · simp [unitOfProd]; tauto
    · simp [unitOfProd]
  · simp [unitOfProd]

theorem mem_epsOfProd (pr : N × List (MixedSymbol N α)) (x : FrontEndState N α) :
    x ∈ epsOfProd pr ↔ pr.2 = [] ∧ x = BinarizedState.old (Sum.inl pr.1) := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨s, rest⟩
  · simp [epsOfProd]
  · simp [epsOfProd]

theorem mem_binOfSuffix (X x y z : FrontEndState N α) :
    (x, y, z) ∈ binOfSuffix X ↔
      x = X ∧
      ((∃ B C, X = BinarizedState.suffix [B, C] ∧ y = BinarizedState.old B ∧
          z = BinarizedState.old C) ∨
        (∃ B C D rest, X = BinarizedState.suffix (B :: C :: D :: rest) ∧
          y = BinarizedState.old B ∧ z = BinarizedState.suffix (C :: D :: rest))) := by
  rcases X with Y | r
  · simp [binOfSuffix]
  · rcases r with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩
    · simp [binOfSuffix]
    · simp [binOfSuffix]
    · simp [binOfSuffix]; tauto
    · simp [binOfSuffix]; tauto

theorem mem_unitOfSuffix (X x y : FrontEndState N α) :
    (x, y) ∈ unitOfSuffix X ↔
      x = X ∧ ∃ B, X = BinarizedState.suffix [B] ∧ y = BinarizedState.old B := by
  rcases X with Y | r
  · simp [unitOfSuffix]
  · rcases r with _ | ⟨B, _ | ⟨C, rest⟩⟩
    · simp [unitOfSuffix]
    · simp [unitOfSuffix]; tauto
    · simp [unitOfSuffix]

end Membership

/-! ### The semantic front-end rules, made explicit -/

section Semantics

variable {N : Type u} {α : Type v}

theorem isolateSymbol_true_eq (s : MixedSymbol N α) : isolateSymbol true s = Sum.inl s := by
  cases s <;> simp [isolateSymbol]

theorem isolateRhs_of_not_single (r : List (MixedSymbol N α))
    (h : ¬ ∃ a, r = [Sum.inr a]) : isolateRhs r = r.map Sum.inl := by
  have hm : r.map (isolateSymbol true) = r.map Sum.inl :=
    List.map_congr_left (fun s _ => isolateSymbol_true_eq s)
  rcases r with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · rfl
  · rcases s with B | b
    · simpa [isolateRhs] using hm
    · exact absurd ⟨b, rfl⟩ h
  · simpa [isolateRhs] using hm

theorem map_inl_ne_single_inr (xs : List (N ⊕ α)) (a : α) :
    xs.map (Sum.inl : (N ⊕ α) → MixedSymbol (N ⊕ α) α) ≠ [Sum.inr a] := by
  rcases xs with _ | ⟨x, rest⟩
  · simp
  · simp

variable (R : MixedRules N α)

theorem isolatedRule_terminal_iff (X : N ⊕ α) (a : α) :
    IsolatedRule R X [Sum.inr a] ↔
      (∃ B, X = Sum.inl B ∧ R B [Sum.inr a]) ∨ X = Sum.inr a := by
  constructor
  · intro h
    generalize hl : ([Sum.inr a] : List (MixedSymbol (N ⊕ α) α)) = l at h
    cases h with
    | @original B rhs hR =>
        by_cases hs : ∃ b, rhs = [Sum.inr b]
        · obtain ⟨b, rfl⟩ := hs
          have : a = b := by simpa [isolateRhs] using hl
          subst this
          exact Or.inl ⟨B, rfl, hR⟩
        · rw [isolateRhs_of_not_single rhs hs] at hl
          exact absurd hl.symm (map_inl_ne_single_inr rhs a)
    | wrapper b =>
        have : a = b := by simpa using hl
        subst this
        exact Or.inr rfl
  · rintro (⟨B, rfl, hR⟩ | rfl)
    · exact IsolatedRule.original (rhs := [Sum.inr a]) hR
    · exact IsolatedRule.wrapper a

theorem isolatedRule_structural_iff (X : N ⊕ α) (xs : List (N ⊕ α)) :
    IsolatedRule R X (xs.map Sum.inl) ↔
      ∃ B, X = Sum.inl B ∧ R B xs ∧ ¬ ∃ a, xs = [Sum.inr a] := by
  constructor
  · intro h
    generalize hl : xs.map (Sum.inl : (N ⊕ α) → MixedSymbol (N ⊕ α) α) = l at h
    cases h with
    | @original B rhs hR =>
        by_cases hs : ∃ b, rhs = [Sum.inr b]
        · obtain ⟨b, rfl⟩ := hs
          exact absurd (by simpa [isolateRhs] using hl) (map_inl_ne_single_inr xs b)
        · rw [isolateRhs_of_not_single rhs hs] at hl
          have : xs = rhs := List.map_injective_iff.mpr Sum.inl_injective hl
          subst this
          exact ⟨B, rfl, hR, hs⟩
    | wrapper b =>
        exact absurd hl (map_inl_ne_single_inr xs b)
  · rintro ⟨B, rfl, hR, hs⟩
    have h := IsolatedRule.original (R := R) hR
    rwa [isolateRhs_of_not_single xs hs] at h

theorem topBinarizedRhs_eq_pair {M : Type*} (rhs : List M) (Y Z : BinarizedState M) :
    topBinarizedRhs rhs = [Y, Z] ↔
      (∃ B C, rhs = [B, C] ∧ Y = BinarizedState.old B ∧ Z = BinarizedState.old C) ∨
        (∃ B C D rest, rhs = B :: C :: D :: rest ∧ Y = BinarizedState.old B ∧
          Z = BinarizedState.suffix (C :: D :: rest)) := by
  rcases rhs with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩
  · simp [topBinarizedRhs]
  · simp [topBinarizedRhs]
  · simp [topBinarizedRhs]; tauto
  · simp [topBinarizedRhs]; tauto

theorem topBinarizedRhs_eq_single {M : Type*} (rhs : List M) (Y : BinarizedState M) :
    topBinarizedRhs rhs = [Y] ↔ ∃ B, rhs = [B] ∧ Y = BinarizedState.old B := by
  rcases rhs with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩
  · simp [topBinarizedRhs]
  · simp [topBinarizedRhs]; tauto
  · simp [topBinarizedRhs]
  · simp [topBinarizedRhs]

theorem topBinarizedRhs_eq_nil {M : Type*} (rhs : List M) :
    topBinarizedRhs rhs = [] ↔ rhs = [] := by
  rcases rhs with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩ <;> simp [topBinarizedRhs]

theorem binarizedRule_pair_iff {M : Type*} (G' : SequenceGrammar M α)
    (X Y Z : BinarizedState M) :
    BinarizedStructuralRule G' X [Y, Z] ↔
      (∃ A rhs, X = BinarizedState.old A ∧ G'.structural A rhs ∧
          topBinarizedRhs rhs = [Y, Z]) ∨
      (∃ B C, X = BinarizedState.suffix [B, C] ∧ Y = BinarizedState.old B ∧
          Z = BinarizedState.old C) ∨
      (∃ B C D rest, X = BinarizedState.suffix (B :: C :: D :: rest) ∧
          Y = BinarizedState.old B ∧ Z = BinarizedState.suffix (C :: D :: rest)) := by
  constructor
  · intro h
    generalize hl : [Y, Z] = l at h
    cases h with
    | @source A rhs hG => exact Or.inl ⟨A, rhs, rfl, hG, hl.symm⟩
    | suffixEmpty => simp at hl
    | suffixUnit B => simp at hl
    | suffixBinary B C =>
        simp only [List.cons.injEq, and_true] at hl
        exact Or.inr (Or.inl ⟨B, C, rfl, hl.1, hl.2⟩)
    | suffixLong B C D rest =>
        simp only [List.cons.injEq, and_true] at hl
        exact Or.inr (Or.inr ⟨B, C, D, rest, rfl, hl.1, hl.2⟩)
  · rintro (⟨A, rhs, rfl, hG, he⟩ | ⟨B, C, rfl, rfl, rfl⟩ | ⟨B, C, D, rest, rfl, rfl, rfl⟩)
    · rw [← he]; exact BinarizedStructuralRule.source hG
    · exact BinarizedStructuralRule.suffixBinary B C
    · exact BinarizedStructuralRule.suffixLong B C D rest

theorem binarizedRule_single_iff {M : Type*} (G' : SequenceGrammar M α)
    (X Y : BinarizedState M) :
    BinarizedStructuralRule G' X [Y] ↔
      (∃ A rhs, X = BinarizedState.old A ∧ G'.structural A rhs ∧ topBinarizedRhs rhs = [Y]) ∨
      (∃ B, X = BinarizedState.suffix [B] ∧ Y = BinarizedState.old B) := by
  constructor
  · intro h
    generalize hl : [Y] = l at h
    cases h with
    | @source A rhs hG => exact Or.inl ⟨A, rhs, rfl, hG, hl.symm⟩
    | suffixEmpty => simp at hl
    | suffixUnit B =>
        simp only [List.cons.injEq, and_true] at hl
        exact Or.inr ⟨B, rfl, hl⟩
    | suffixBinary B C => simp at hl
    | suffixLong B C D rest => simp at hl
  · rintro (⟨A, rhs, rfl, hG, he⟩ | ⟨B, rfl, rfl⟩)
    · rw [← he]; exact BinarizedStructuralRule.source hG
    · exact BinarizedStructuralRule.suffixUnit B

theorem binarizedRule_nil_iff {M : Type*} (G' : SequenceGrammar M α) (X : BinarizedState M) :
    BinarizedStructuralRule G' X [] ↔
      (∃ A, X = BinarizedState.old A ∧ G'.structural A []) ∨ X = BinarizedState.suffix [] := by
  constructor
  · intro h
    generalize hl : ([] : List (BinarizedState M)) = l at h
    cases h with
    | @source A rhs hG =>
        have : rhs = [] := (topBinarizedRhs_eq_nil rhs).mp hl.symm
        subst this
        exact Or.inl ⟨A, rfl, hG⟩
    | suffixEmpty => exact Or.inr rfl
    | suffixUnit B => simp at hl
    | suffixBinary B C => simp at hl
    | suffixLong B C D rest => simp at hl
  · rintro (⟨A, rfl, hG⟩ | rfl)
    · exact BinarizedStructuralRule.source (rhs := []) hG
    · exact BinarizedStructuralRule.suffixEmpty

/-- Terminal rules of the semantic front end. -/
theorem frontEnd_terminal_iff (X : FrontEndState N α) (a : α) :
    (frontEndBinaryGrammar R).terminalRule X a ↔
      (∃ B, X = BinarizedState.old (Sum.inl B) ∧ R B [Sum.inr a]) ∨
        X = BinarizedState.old (Sum.inr a) := by
  show (∃ A, X = BinarizedState.old A ∧ IsolatedRule R A [Sum.inr a]) ↔ _
  constructor
  · rintro ⟨A, rfl, h⟩
    rcases (isolatedRule_terminal_iff R A a).mp h with ⟨B, rfl, hR⟩ | rfl
    · exact Or.inl ⟨B, rfl, hR⟩
    · exact Or.inr rfl
  · rintro (⟨B, rfl, hR⟩ | rfl)
    · exact ⟨Sum.inl B, rfl, (isolatedRule_terminal_iff R _ a).mpr (Or.inl ⟨B, rfl, hR⟩)⟩
    · exact ⟨Sum.inr a, rfl, (isolatedRule_terminal_iff R _ a).mpr (Or.inr rfl)⟩

/-- Binary rules of the semantic front end. -/
theorem frontEnd_binary_iff (X Y Z : FrontEndState N α) :
    (frontEndBinaryGrammar R).binaryRule X Y Z ↔
      (∃ B rhs, X = BinarizedState.old (Sum.inl B) ∧ R B rhs ∧
        ((∃ B' C, rhs = [B', C] ∧ Y = BinarizedState.old B' ∧ Z = BinarizedState.old C) ∨
          (∃ B' C D rest, rhs = B' :: C :: D :: rest ∧ Y = BinarizedState.old B' ∧
            Z = BinarizedState.suffix (C :: D :: rest)))) ∨
      (∃ B C, X = BinarizedState.suffix [B, C] ∧ Y = BinarizedState.old B ∧
          Z = BinarizedState.old C) ∨
      (∃ B C D rest, X = BinarizedState.suffix (B :: C :: D :: rest) ∧
          Y = BinarizedState.old B ∧ Z = BinarizedState.suffix (C :: D :: rest)) := by
  show BinarizedStructuralRule (isolatedSequenceGrammar R) X [Y, Z] ↔ _
  rw [binarizedRule_pair_iff]
  constructor
  · rintro (⟨A, rhs, rfl, hG, he⟩ | h | h)
    · obtain ⟨B, rfl, hR, _⟩ := (isolatedRule_structural_iff R A rhs).mp hG
      exact Or.inl ⟨B, rhs, rfl, hR, (topBinarizedRhs_eq_pair rhs Y Z).mp he⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨B, rhs, rfl, hR, hshape⟩ | h | h)
    · refine Or.inl ⟨Sum.inl B, rhs, rfl, ?_, (topBinarizedRhs_eq_pair rhs Y Z).mpr hshape⟩
      refine (isolatedRule_structural_iff R _ rhs).mpr ⟨B, rfl, hR, ?_⟩
      rintro ⟨a, rfl⟩
      rcases hshape with ⟨_, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ <;> simp at h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

/-- Unit rules of the semantic front end. -/
theorem frontEnd_unit_iff (X Y : FrontEndState N α) :
    (frontEndBinaryGrammar R).unitRule X Y ↔
      (∃ B C, X = BinarizedState.old (Sum.inl B) ∧ R B [Sum.inl C] ∧
          Y = BinarizedState.old (Sum.inl C)) ∨
      (∃ B, X = BinarizedState.suffix [B] ∧ Y = BinarizedState.old B) := by
  show BinarizedStructuralRule (isolatedSequenceGrammar R) X [Y] ↔ _
  rw [binarizedRule_single_iff]
  constructor
  · rintro (⟨A, rhs, rfl, hG, he⟩ | h)
    · obtain ⟨B, rfl, hR, hs⟩ := (isolatedRule_structural_iff R A rhs).mp hG
      obtain ⟨S, rfl, rfl⟩ := (topBinarizedRhs_eq_single rhs Y).mp he
      rcases S with C | a
      · exact Or.inl ⟨B, C, rfl, hR, rfl⟩
      · exact absurd ⟨a, rfl⟩ hs
    · exact Or.inr h
  · rintro (⟨B, C, rfl, hR, rfl⟩ | h)
    · refine Or.inl ⟨Sum.inl B, [Sum.inl C], rfl, ?_, rfl⟩
      exact (isolatedRule_structural_iff R _ _).mpr ⟨B, rfl, hR, by simp⟩
    · exact Or.inr h

/-- ε rules of the semantic front end. -/
theorem frontEnd_epsilon_iff (X : FrontEndState N α) :
    (frontEndBinaryGrammar R).epsilonRule X ↔
      (∃ B, X = BinarizedState.old (Sum.inl B) ∧ R B []) ∨ X = BinarizedState.suffix [] := by
  show BinarizedStructuralRule (isolatedSequenceGrammar R) X [] ↔ _
  rw [binarizedRule_nil_iff]
  constructor
  · rintro (⟨A, rfl, hG⟩ | h)
    · obtain ⟨B, rfl, hR, _⟩ := (isolatedRule_structural_iff R A []).mp hG
      exact Or.inl ⟨B, rfl, hR⟩
    · exact Or.inr h
  · rintro (⟨B, rfl, hR⟩ | h)
    · exact Or.inl ⟨Sum.inl B, rfl,
        (isolatedRule_structural_iff R _ []).mpr ⟨B, rfl, hR, by simp⟩⟩
    · exact Or.inr h

end Semantics


/-! ### Sizes and costs of the front end -/

section FrontCosts

variable {N : Type u} {α : Type v}

/-- List size of the input: `|nts| + |alph| + |prs| + Σ |rhs|`. -/
def inputScale (nts : List N) (alph : List α) (prs : List (N × List (MixedSymbol N α))) : Nat :=
  nts.length + alph.length + prs.length + (prs.map (fun pr => pr.2.length)).sum

theorem forListC_fst_eq {β γ : Type*} (f : β → List γ × Nat) :
    ∀ l : List β, (forListC f l).1 = l.flatMap (fun b => (f b).1)
  | [] => rfl
  | b :: l => by
      show (f b).1 ++ (forListC f l).1 = _
      rw [forListC_fst_eq f l]; simp

theorem suffixStatesC_length : ∀ r : List (MixedSymbol N α), (suffixStatesC r).1.length = r.length
  | [] => rfl
  | x :: xs => by
      show (BinarizedState.suffix (x :: xs) :: (suffixStatesC xs).1).length = _
      simp [suffixStatesC_length xs]

theorem suffixStatesC_snd : ∀ r : List (MixedSymbol N α), (suffixStatesC r).2 = 2 * r.length + 1
  | [] => rfl
  | x :: xs => by
      show (suffixStatesC xs).2 + 2 = _
      rw [suffixStatesC_snd xs]; simp; ring

theorem allSuffixStates_length (prs : List (N × List (MixedSymbol N α))) :
    (allSuffixStates prs).length = (prs.map (fun pr => pr.2.length)).sum := by
  unfold allSuffixStates feSufC
  rw [forListC_fst_eq, List.length_flatMap]
  congr 1
  apply List.map_congr_left
  intro pr _
  exact suffixStatesC_length pr.2

theorem feSufC_snd_le (prs : List (N × List (MixedSymbol N α))) :
    (feSufC prs).2 ≤ 4 * (prs.map (fun pr => pr.2.length)).sum + 3 * prs.length + 1 := by
  unfold feSufC
  obtain ⟨_, h⟩ := forListC_bound (fun pr : N × List (MixedSymbol N α) => suffixStatesC pr.2)
    (fun pr => 2 * pr.2.length + 1) prs (fun pr _ => by
      rw [suffixStatesC_length, suffixStatesC_snd]; omega)
  refine le_trans h ?_
  have : ∀ l : List (N × List (MixedSymbol N α)),
      (l.map (fun pr => 2 * (2 * pr.2.length + 1) + 1)).sum =
        4 * (l.map (fun pr => pr.2.length)).sum + 3 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
  rw [this]

theorem length_le_one_of {β : Type*} (l : List β) (h : l = [] ∨ ∃ b, l = [b]) : l.length ≤ 1 := by
  rcases h with rfl | ⟨b, rfl⟩ <;> simp

theorem termOfProd_length (pr : N × List (MixedSymbol N α)) : (termOfProd pr).length ≤ 1 := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [termOfProd]
  · rcases s with B | b <;> simp [termOfProd]
  · simp [termOfProd]

theorem binOfProd_length (pr : N × List (MixedSymbol N α)) : (binOfProd pr).length ≤ 1 := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩ <;> simp [binOfProd]

theorem unitOfProd_length (pr : N × List (MixedSymbol N α)) : (unitOfProd pr).length ≤ 1 := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨s, _ | ⟨t, rest⟩⟩
  · simp [unitOfProd]
  · rcases s with B | b <;> simp [unitOfProd]
  · simp [unitOfProd]

theorem epsOfProd_length (pr : N × List (MixedSymbol N α)) : (epsOfProd pr).length ≤ 1 := by
  obtain ⟨A, r⟩ := pr
  rcases r with _ | ⟨s, rest⟩ <;> simp [epsOfProd]

theorem binOfSuffix_length (X : FrontEndState N α) : (binOfSuffix X).length ≤ 1 := by
  rcases X with Y | r
  · simp [binOfSuffix]
  · rcases r with _ | ⟨B, _ | ⟨C, _ | ⟨D, rest⟩⟩⟩ <;> simp [binOfSuffix]

theorem unitOfSuffix_length (X : FrontEndState N α) : (unitOfSuffix X).length ≤ 1 := by
  rcases X with Y | r
  · simp [unitOfSuffix]
  · rcases r with _ | ⟨B, _ | ⟨C, rest⟩⟩ <;> simp [unitOfSuffix]

/-- A uniform bound for loops emitting at most one record of constant cost `c ≥ 1`. -/
theorem forListC_const_bound {β γ : Type*} (f : β → List γ) (c : Nat) (hc : 1 ≤ c)
    (hf : ∀ b, (f b).length ≤ 1) (l : List β) :
    (forListC (fun b => (f b, c)) l).1.length ≤ l.length ∧
    (forListC (fun b => (f b, c)) l).2 ≤ l.length * (2 * c + 1) + 1 := by
  refine ⟨?_, (forListC_bound_const _ c l (fun b _ => ⟨le_trans (hf b) hc, le_refl _⟩)).2⟩
  have := forListC_length_le (fun b => (f b, c)) 1 l (fun b _ => hf b)
  simpa using this

/-- **Size of the written front end.** -/
theorem frontCode_sizeBound (nts : List N) (alph : List α)
    (prs : List (N × List (MixedSymbol N α))) :
    SizeBound (frontCodeC nts alph prs).1 (inputScale nts alph prs) := by
  have hsuf := allSuffixStates_length prs
  have ht := (forListC_const_bound termOfProd 3 (by omega) termOfProd_length prs).1
  have hb1 := (forListC_const_bound binOfProd 5 (by omega) binOfProd_length prs).1
  have hb2 := (forListC_const_bound binOfSuffix 5 (by omega) binOfSuffix_length
    (allSuffixStates prs)).1
  have hu1 := (forListC_const_bound unitOfProd 3 (by omega) unitOfProd_length prs).1
  have hu2 := (forListC_const_bound unitOfSuffix 3 (by omega) unitOfSuffix_length
    (allSuffixStates prs)).1
  have he := (forListC_const_bound epsOfProd 2 (by omega) epsOfProd_length prs).1
  unfold inputScale
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [frontCode_states]; simp only [List.length_append, List.length_map]; omega
  · rw [frontCode_term]; simp only [List.length_append, List.length_map]; omega
  · rw [frontCode_bin]; simp only [List.length_append]; omega
  · rw [frontCode_unit]; simp only [List.length_append]; omega
  · rw [frontCode_eps]; omega

theorem stateLen_le_of_mem (nts : List N) (alph : List α)
    (prs : List (N × List (MixedSymbol N α))) (x : FrontEndState N α)
    (hx : x ∈ (frontCodeC nts alph prs).1.states) :
    stateLen x ≤ (prs.map (fun pr => pr.2.length)).sum := by
  rw [frontCode_states] at hx
  simp only [List.mem_append, List.mem_map] at hx
  rcases hx with ⟨A, _, rfl⟩ | ⟨a, _, rfl⟩ | hx
  · simp [stateLen]
  · simp [stateLen]
  · obtain ⟨pr, hpr, i, _, rfl⟩ := (mem_allSuffixStates prs x).mp hx
    simp only [stateLen, List.length_drop]
    have := le_sum_map_of_mem (fun pr : N × List (MixedSymbol N α) => pr.2.length) hpr
    simp only at this
    omega

/-- **State comparisons cost at most `inputScale + 1` steps.** -/
theorem frontCode_ceqBound [DecidableEq N] [DecidableEq α] (nts : List N) (alph : List α)
    (prs : List (N × List (MixedSymbol N α))) :
    CeqBound stateEqC (· ∈ (frontCodeC nts alph prs).1.states) (inputScale nts alph prs + 1) := by
  intro x y hx _
  have h1 := stateEqC_snd_le x y
  have h2 := stateLen_le_of_mem nts alph prs x hx
  unfold inputScale
  omega

/-- **Cost of the front end: linear.** -/
theorem frontCodeC_snd_le (nts : List N) (alph : List α)
    (prs : List (N × List (MixedSymbol N α))) :
    (frontCodeC nts alph prs).2 ≤ 60 * (inputScale nts alph prs + 1) := by
  have hsuf := allSuffixStates_length prs
  have hS := feSufC_snd_le prs
  obtain ⟨ht1, ht2⟩ := forListC_const_bound termOfProd 3 (by omega) termOfProd_length prs
  obtain ⟨hb1, hb2⟩ := forListC_const_bound binOfProd 5 (by omega) binOfProd_length prs
  obtain ⟨hb3, hb4⟩ := forListC_const_bound binOfSuffix 5 (by omega) binOfSuffix_length
    (allSuffixStates prs)
  obtain ⟨hu1, hu2⟩ := forListC_const_bound unitOfProd 3 (by omega) unitOfProd_length prs
  obtain ⟨hu3, hu4⟩ := forListC_const_bound unitOfSuffix 3 (by omega) unitOfSuffix_length
    (allSuffixStates prs)
  obtain ⟨he1, he2⟩ := forListC_const_bound epsOfProd 2 (by omega) epsOfProd_length prs
  have hst : (feStatesC nts alph prs).2 = 4 * nts.length + 1 + (4 * alph.length + 1) +
      (alph.length + 1) + (nts.length + 1) := by
    simp only [feStatesC, mapC_snd, appendC_snd, mapC_fst, List.length_map]
  have hte : (feTermC alph prs).2 = (forListC (fun pr => (termOfProd pr, 3)) prs).2 +
      (4 * alph.length + 1) + ((forListC (fun pr => (termOfProd pr, 3)) prs).1.length + 1) := by
    simp only [feTermC, mapC_snd, appendC_snd]
  have hbi : (feBinC prs).2 = (forListC (fun pr => (binOfProd pr, 5)) prs).2 +
      (forListC (fun X => (binOfSuffix X, 5)) (allSuffixStates prs)).2 +
      ((forListC (fun pr => (binOfProd pr, 5)) prs).1.length + 1) := by
    simp only [feBinC, appendC_snd, allSuffixStates]
  have hun : (feUnitC prs).2 = (forListC (fun pr => (unitOfProd pr, 3)) prs).2 +
      (forListC (fun X => (unitOfSuffix X, 3)) (allSuffixStates prs)).2 +
      ((forListC (fun pr => (unitOfProd pr, 3)) prs).1.length + 1) := by
    simp only [feUnitC, appendC_snd, allSuffixStates]
  show (feSufC prs).2 + (feStatesC nts alph prs).2 + (feTermC alph prs).2 + (feBinC prs).2 +
      (feUnitC prs).2 + (feEpsC prs).2 + 1 ≤ _
  rw [hst, hte, hbi, hun]
  unfold feEpsC
  unfold inputScale
  omega

end FrontCosts

end SSBNFNorm
end TCS1
end LeanCfgProject
