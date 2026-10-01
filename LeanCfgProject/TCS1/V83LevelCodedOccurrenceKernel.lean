import LeanCfgProject.TCS1.V83LevelCodedTreeParsing

/-!
# TCS #1 v83: occurrence splitting for level-coded serializations

This module develops position-sensitive occurrence lemmas used by the
Appendix replacement argument.  Unlike mere membership lemmas, these preserve
the exact prefix and suffix around a designated occurrence.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/--
A designated occurrence of one symbol in A++B lies either in A or in B, with
the exact surrounding prefix and suffix recovered.
-/
theorem factor_cons_split_append
    {α : Type}
    (a : α)
    (A B p q : List α)
    (h : A ++ B = p ++ a :: q) :
    (∃ pA qA : List α,
        A = pA ++ a :: qA ∧
        p = pA ∧
        q = qA ++ B) ∨
    (∃ pB qB : List α,
        B = pB ++ a :: qB ∧
        p = A ++ pB ∧
        q = qB) := by
  induction A generalizing p with
  | nil =>
      right
      exact ⟨p, q, by simpa using h, rfl, rfl⟩
  | cons ah tail ih =>
      cases p with
      | nil =>
          left
          simp only [List.cons_append, List.nil_append] at h
          have hah : ah = a := by
            simpa using congrArg List.head? h
          have htail : tail ++ B = q := by
            simpa [hah] using congrArg List.tail h
          subst ah
          exact ⟨[], tail, rfl, rfl, htail.symm⟩
      | cons ph pt =>
          simp only [List.cons_append] at h
          have hah : ah = ph := by
            simpa using congrArg List.head? h
          have htail :
              tail ++ B = pt ++ a :: q := by
            simpa [hah] using congrArg List.tail h
          rcases ih pt htail with hleft | hright
          · left
            rcases hleft with
              ⟨pA, qA, hA, hp, hq⟩
            refine
              ⟨ah :: pA, qA, ?_, ?_, hq⟩
            · rw [hA]
              rfl
            · simp [hah, hp]
          · right
            rcases hright with
              ⟨pB, qB, hB, hp, hq⟩
            refine
              ⟨pB, qB, hB, ?_, hq⟩
            rw [hp]
            simp [hah]

/-- No occurrence of c can be designated inside the one-letter word [l]. -/
theorem no_c_factor_in_l
    {p q : Word LevelTreeSymbol} :
    ¬ ([l] = p ++ c :: q) := by
  intro h
  have hc : c ∈ ([l] : Word LevelTreeSymbol) := by
    rw [h]
    simp
  simpa using hc

/-- No occurrence of c can be designated inside the one-letter word [r]. -/
theorem no_c_factor_in_r
    {p q : Word LevelTreeSymbol} :
    ¬ ([r] = p ++ c :: q) := by
  intro h
  have hc : c ∈ ([r] : Word LevelTreeSymbol) := by
    rw [h]
    simp
  simpa using hc

/--
A designated c in a valid serialization is exactly the first body symbol of
one parsed shortcut node.  The result preserves the exact prefix and suffix.
-/
theorem levelTree_c_factor_context
    {n : Nat}
    (t : LevelTree n)
    {p q : Word LevelTreeSymbol}
    (h : t.serialize = p ++ c :: q) :
    ∃ i : Nat, ∃ ctx : LevelTreeContext n i,
      p = ctx.prefix ++ [l] ∧
      q =
        List.replicate (i + 1) zero ++
          [d, r] ++ ctx.suffix := by
  induction t generalizing p q with
  | cleanLeaf =>
      have hc :
          c ∈ (LevelTree.cleanLeaf).serialize := by
        rw [h]
        simp
      simp [LevelTree.serialize] at hc
  | shortcut i =>
      have hcanon :
          ([l] : Word LevelTreeSymbol) ++
              c ::
                (List.replicate (i + 1) zero ++
                  [d, r]) =
            p ++ c :: q := by
        simpa [LevelTree.serialize, levelShortcutBody,
          List.append_assoc] using h
      have hinj :=
        (List.append_cons_inj_of_notMem
          (x₁ := ([l] : Word LevelTreeSymbol))
          (x₂ := p)
          (z₁ :=
            List.replicate (i + 1) zero ++
              [d, r])
          (z₂ := q)
          (a₁ := c) (a₂ := c)
          (by simp)
          (by
            simp)).1 hcanon
      rcases hinj with ⟨hp, _, hq⟩
      refine
        ⟨i, LevelTreeContext.hole i, ?_, ?_⟩
      · simpa [LevelTreeContext.prefix] using hp.symm
      · simpa [LevelTreeContext.suffix] using hq.symm
  | @node j left right ihL ihR =>
      have houter :
          ([l] : Word LevelTreeSymbol) ++
              (left.serialize ++ right.serialize ++ [r]) =
            p ++ c :: q := by
        simpa [LevelTree.serialize,
          List.append_assoc] using h
      rcases
          factor_cons_split_append
            c ([l] : Word LevelTreeSymbol)
            (left.serialize ++ right.serialize ++ [r])
            p q houter with
        hInL | hAfterL
      · rcases hInL with
          ⟨p0, q0, hbad, _, _⟩
        exact False.elim (no_c_factor_in_l hbad)
      · rcases hAfterL with
          ⟨p1, q1, hrest, hp, hq⟩
        have hrest' :
            left.serialize ++
                (right.serialize ++ [r]) =
              p1 ++ c :: q1 := by
          simpa [List.append_assoc] using hrest
        rcases
            factor_cons_split_append
              c left.serialize
              (right.serialize ++ [r])
              p1 q1 hrest' with
          hInLeft | hAfterLeft
        · rcases hInLeft with
            ⟨pL, qL, hLeft, hp1, hq1⟩
          obtain ⟨i, ctx, hpL, hqLctx⟩ :=
            ihL hLeft
          refine
            ⟨i, LevelTreeContext.left ctx right,
              ?_, ?_⟩
          · rw [hp, hp1, hpL]
            simp [LevelTreeContext.prefix,
              List.append_assoc]
          · rw [hq, hq1, hqLctx]
            simp [LevelTreeContext.suffix,
              List.append_assoc]
        · rcases hAfterLeft with
            ⟨p2, q2, hRightTail, hp1, hq1⟩
          rcases
              factor_cons_split_append
                c right.serialize ([r] : Word LevelTreeSymbol)
                p2 q2 hRightTail with
            hInRight | hInFinalR
          · rcases hInRight with
              ⟨pR, qR, hRight, hp2, hq2⟩
            obtain ⟨i, ctx, hpR, hqRctx⟩ :=
              ihR hRight
            refine
              ⟨i, LevelTreeContext.right left ctx,
                ?_, ?_⟩
            · rw [hp, hp1, hp2, hpR]
              simp [LevelTreeContext.prefix,
                List.append_assoc]
            · rw [hq, hq1, hq2, hqRctx]
              simp [LevelTreeContext.suffix,
                List.append_assoc]
          · rcases hInFinalR with
              ⟨pR, qR, hbad, _, _⟩
            exact False.elim (no_c_factor_in_r hbad)

/--
Two zero runs terminated by d have the same length and the same following
suffix.
-/
theorem zeroRun_d_injective
    {k m : Nat}
    {q s : Word LevelTreeSymbol}
    (h :
      List.replicate k zero ++ d :: q =
        List.replicate m zero ++ d :: s) :
    k = m ∧ q = s := by
  induction k generalizing m with
  | zero =>
      cases m with
      | zero =>
          simp at h
          exact ⟨rfl, h⟩
      | succ m =>
          have h' :
              d :: q =
                zero ::
                  (List.replicate m zero ++ d :: s) := by
            simpa [List.replicate_succ] using h
          have hbad : d = zero := by
            simpa using congrArg List.head? h'
          simp at hbad
  | succ k ih =>
      cases m with
      | zero =>
          have h' :
              zero ::
                  (List.replicate k zero ++ d :: q) =
                d :: s := by
            simpa [List.replicate_succ] using h
          have hbad : zero = d := by
            simpa using congrArg List.head? h'
          simp at hbad
      | succ m =>
          simp only [List.replicate_succ,
            List.cons_append] at h
          have htail :
              List.replicate k zero ++ d :: q =
                List.replicate m zero ++ d :: s := by
            simpa using congrArg List.tail h
          obtain ⟨hkm, hqs⟩ := ih htail
          exact ⟨by omega, hqs⟩

/--
A literal shortcut body s_i occurring in a valid level-n serialization is
exactly the body of a parsed residual-height-i shortcut node.
-/
theorem levelShortcutBodyRecognition_proved
    (n : Nat) :
    ∀ {i : Nat}
      {p q : Word LevelTreeSymbol},
      p ++ levelShortcutBody i ++ q ∈
          LevelTreeLanguage n →
      ∃ ctx : LevelTreeContext n i,
        p = ctx.prefix ++ [l] ∧
        q = [r] ++ ctx.suffix := by
  intro i p q hmem
  rcases hmem with ⟨t, ht⟩
  have hcFactor :
      t.serialize =
        p ++ c ::
          (List.replicate (i + 1) zero ++
            d :: q) := by
    rw [ht]
    simp [levelShortcutBody, List.append_assoc]
  obtain ⟨j, ctx, hp, hq⟩ :=
    levelTree_c_factor_context t hcFactor
  have hrun :
      List.replicate (i + 1) zero ++ d :: q =
        List.replicate (j + 1) zero ++
          d :: (r :: ctx.suffix) := by
    simpa [List.append_assoc] using hq
  obtain ⟨hij, hrest⟩ :=
    zeroRun_d_injective hrun
  have hij' : i = j := by omega
  subst j
  refine ⟨ctx, hp, ?_⟩
  simpa using hrest

end TCS1
end LeanCfgProject
