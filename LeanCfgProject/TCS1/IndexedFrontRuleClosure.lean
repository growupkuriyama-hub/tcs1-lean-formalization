import LeanCfgProject.TCS1.IndexedClosedFrontSupport

/-!
# TCS #1 v66: finite indexed front-end rule closure

This module discharges the remaining closure obligation for the finite
front-end support.  It first gives non-dependent inversion principles for the
two indexed inductive rule relations.  Those avoid fragile dependent
elimination on already-specialized right-hand sides.

The key source-rule fact is that any isolated structural right-hand side of
length at least three comes from an actual indexed source production with
exactly that mixed RHS.  Therefore the suffix child of a long source rule is
one of the occurrence suffixes in the finite support.  Fresh suffix rules use
the suffix-tail closure proved in IndexedClosedFrontSupport.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section IndexedFrontRuleClosure

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}

/-- Non-dependent inversion for terminal-isolation rules. -/
theorem isolatedRule_cases
    (R : MixedRules N α)
    {X : N ⊕ α}
    {out : List (MixedSymbol (N ⊕ α) α)}
    (h : IsolatedRule R X out) :
    (∃ A rhs,
        X = Sum.inl A ∧
        out = isolateRhs rhs ∧
        R A rhs)
      ∨
    (∃ a,
        X = Sum.inr a ∧
        out = [Sum.inr a]) := by
  cases h with
  | @original A rhs hR =>
      exact Or.inl ⟨A, rhs, rfl, rfl, hR⟩
  | wrapper a =>
      exact Or.inr ⟨a, rfl, rfl⟩

/-- Non-dependent inversion for right-associated binarization rules. -/
theorem binarizedStructuralRule_cases
    (G : SequenceGrammar N α)
    {X : BinarizedState N}
    {out : List (BinarizedState N)}
    (h : BinarizedStructuralRule G X out) :
    (∃ A rhs,
        X = BinarizedState.old A ∧
        out = topBinarizedRhs rhs ∧
        G.structural A rhs)
      ∨
    (X = BinarizedState.suffix [] ∧ out = [])
      ∨
    (∃ B,
        X = BinarizedState.suffix [B] ∧
        out = [BinarizedState.old B])
      ∨
    (∃ B C,
        X = BinarizedState.suffix [B, C] ∧
        out = [BinarizedState.old B,
          BinarizedState.old C])
      ∨
    (∃ B C D rest,
        X = BinarizedState.suffix (B :: C :: D :: rest) ∧
        out = [BinarizedState.old B,
          BinarizedState.suffix (C :: D :: rest)]) := by
  cases h with
  | @source A rhs hG =>
      exact Or.inl ⟨A, rhs, rfl, rfl, hG⟩
  | suffixEmpty =>
      exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | suffixUnit B =>
      exact Or.inr (Or.inr (Or.inl
        ⟨B, rfl, rfl⟩))
  | suffixBinary B C =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        ⟨B, C, rfl, rfl⟩)))
  | suffixLong B C D rest =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        ⟨B, C, D, rest, rfl, rfl⟩)))

/-- Any source-RHS drop beginning at a valid occurrence is supported. -/
theorem indexedClosedFrontSupport_drop_mem
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (p : P)
    (i : Nat)
    (hi : i < (G.rhs p).length) :
    BinarizedState.suffix ((G.rhs p).drop i) ∈
      indexedClosedFrontSupport G := by
  let o : ProductionOccurrence G :=
    ⟨p, ⟨i, hi⟩⟩
  simpa [o, occurrenceSuffix] using
    indexedClosedFrontSupport_suffix_mem G o

/--
A length-at-least-three structural RHS of the terminal-isolated sequence
grammar is literally the right-hand side of some indexed source production.
-/
theorem indexed_isolatedStructural_long_has_source
    (G : IndexedMixedCFG N α P)
    (X B C D : MixedSymbol N α)
    (rest : List (MixedSymbol N α))
    (h :
      (isolatedSequenceGrammar G.toMixedRules).structural
        X (B :: C :: D :: rest)) :
    ∃ p : P,
      G.rhs p = B :: C :: D :: rest := by
  change
    IsolatedRule G.toMixedRules X
      ((B :: C :: D :: rest).map Sum.inl) at h
  rcases isolatedRule_cases G.toMixedRules h with
    horiginal | hwrapper
  · rcases horiginal with
      ⟨A, rhs, hX, hout, hR⟩
    rcases hR with ⟨p, hLhs, hRhs⟩
    cases rhs with
    | nil =>
        simp [isolateRhs] at hout
    | cons s tail =>
        cases tail with
        | nil =>
            cases s <;>
              simp [isolateRhs, isolateSymbol] at hout
        | cons s₂ tail₂ =>
            let f :
                MixedSymbol N α →
                  MixedSymbol (N ⊕ α) α :=
              fun x => Sum.inl x
            have hmaps :
                (B :: C :: D :: rest).map f =
                  (s :: s₂ :: tail₂).map f := by
              simpa [f, isolateRhs,
                map_isolateSymbol_true_eq_map_inl] using hout
            have hf : Function.Injective f := by
              intro x y hxy
              exact Sum.inl.inj hxy
            have hlist :
                B :: C :: D :: rest =
                  s :: s₂ :: tail₂ :=
              (List.map_inj_right hf).1 hmaps
            exact ⟨p, hRhs.trans hlist.symm⟩
  · rcases hwrapper with ⟨a, hX, hout⟩
    simp at hout

/--
The linear indexed support is closed under every unit and binary child edge of
the actual front-end binary grammar.
-/
theorem indexedClosedFrontSupport_ruleClosed
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P) :
    BinaryGrammarSupportedOn
      (frontEndBinaryGrammar G.toMixedRules)
      (indexedClosedFrontSupport G) := by
  constructor
  · intro A B hA hunit
    change
      BinarizedStructuralRule
        (isolatedSequenceGrammar G.toMixedRules)
        A [B] at hunit
    rcases
      binarizedStructuralRule_cases
        (isolatedSequenceGrammar G.toMixedRules) hunit with
      hsource | hrest
    · rcases hsource with
        ⟨X, rhs, hAX, hout, hsrc⟩
      cases rhs with
      | nil =>
          simp [topBinarizedRhs] at hout
      | cons R rest =>
          cases rest with
          | nil =>
              have hB :
                  B = BinarizedState.old R := by
                simpa [topBinarizedRhs] using hout
              rw [hB]
              exact indexedClosedFrontSupport_old_mem G R
          | cons S tail =>
              cases tail <;>
                simp [topBinarizedRhs] at hout
    · rcases hrest with
        hempty | hrest
      · simp at hempty
      · rcases hrest with
          hunitCase | hrest
        · rcases hunitCase with
            ⟨R, hAR, hout⟩
          have hB :
              B = BinarizedState.old R := by
            simpa using hout
          rw [hB]
          exact indexedClosedFrontSupport_old_mem G R
        · rcases hrest with
            hbinaryCase | hlongCase
          · rcases hbinaryCase with
              ⟨R, S, hARS, hout⟩
            simp at hout
          · rcases hlongCase with
              ⟨R, S, T, rest, hArest, hout⟩
            simp at hout

  · intro A B C hA hbin
    change
      BinarizedStructuralRule
        (isolatedSequenceGrammar G.toMixedRules)
        A [B, C] at hbin
    rcases
      binarizedStructuralRule_cases
        (isolatedSequenceGrammar G.toMixedRules) hbin with
      hsource | hrest
    · rcases hsource with
        ⟨X, rhs, hAX, hout, hsrc⟩
      cases rhs with
      | nil =>
          simp [topBinarizedRhs] at hout
      | cons R rest =>
          cases rest with
          | nil =>
              simp [topBinarizedRhs] at hout
          | cons S tail =>
              cases tail with
              | nil =>
                  have hpair :
                      B = BinarizedState.old R ∧
                      C = BinarizedState.old S := by
                    simpa [topBinarizedRhs] using hout
                  rcases hpair with ⟨rfl, rfl⟩
                  exact
                    ⟨indexedClosedFrontSupport_old_mem G R,
                     indexedClosedFrontSupport_old_mem G S⟩
              | cons T more =>
                  have hpair :
                      B = BinarizedState.old R ∧
                      C =
                        BinarizedState.suffix
                          (S :: T :: more) := by
                    simpa [topBinarizedRhs] using hout
                  obtain ⟨p, hp⟩ :=
                    indexed_isolatedStructural_long_has_source
                      G X R S T more hsrc
                  have hOne :
                      1 < (G.rhs p).length := by
                    rw [hp]
                    simp
                  have hTail :
                      BinarizedState.suffix
                          (S :: T :: more) ∈
                        indexedClosedFrontSupport G := by
                    have hd :=
                      indexedClosedFrontSupport_drop_mem
                        G p 1 hOne
                    simpa [hp] using hd
                  rcases hpair with ⟨rfl, rfl⟩
                  exact
                    ⟨indexedClosedFrontSupport_old_mem G R,
                     hTail⟩
    · rcases hrest with
        hempty | hrest
      · simp at hempty
      · rcases hrest with
          hunitCase | hrest
        · rcases hunitCase with
            ⟨R, hAR, hout⟩
          simp at hout
        · rcases hrest with
            hbinaryCase | hlongCase
          · rcases hbinaryCase with
              ⟨R, S, hARS, hout⟩
            have hpair :
                B = BinarizedState.old R ∧
                C = BinarizedState.old S := by
              simpa using hout
            rcases hpair with ⟨rfl, rfl⟩
            exact
              ⟨indexedClosedFrontSupport_old_mem G R,
               indexedClosedFrontSupport_old_mem G S⟩
          · rcases hlongCase with
              ⟨R, S, T, rest, hAlong, hout⟩
            have hpair :
                B = BinarizedState.old R ∧
                C =
                  BinarizedState.suffix
                    (S :: T :: rest) := by
              simpa using hout
            rw [hAlong] at hA
            have hTail :
                BinarizedState.suffix
                    (S :: T :: rest) ∈
                  indexedClosedFrontSupport G :=
              indexedClosedFrontSupport_suffix_tail_mem
                G R S (T :: rest) hA
            rcases hpair with ⟨rfl, rfl⟩
            exact
              ⟨indexedClosedFrontSupport_old_mem G R,
               hTail⟩

/--
The indexed support, together with a uniform source-RHS length bound, is a
complete front-end support certificate.
-/
def indexedFrontSupportCertificate
    [Fintype N] [Fintype α] [Fintype P]
    [DecidableEq N] [DecidableEq α]
    (G : IndexedMixedCFG N α P)
    (n : Nat)
    (hRhs : ∀ p, (G.rhs p).length ≤ n) :
    FrontEndSupportCertificate
      G.toMixedRules n where
  support := indexedClosedFrontSupport G
  closed := indexedClosedFrontSupport_ruleClosed G
  active :=
    indexedClosedFrontSupport_active G n hRhs

end IndexedFrontRuleClosure

end TCS1
end LeanCfgProject
