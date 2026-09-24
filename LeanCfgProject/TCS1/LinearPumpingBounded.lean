import LeanCfgProject.TCS1.LinearPumpingKernel

/-!
# TCS #1 v79: bounded linear pumping lemma

For the Double-Delta argument we need the standard *linear* pumping bound:
the outer material and the two pumped pieces together are bounded by a
grammar-dependent constant.  In the normalized linear-spine grammar every
spine step emits exactly one terminal.  Hence it suffices to find a repeated
state among the first |N|+1 spine states.

This file refines the qualitative pumping kernel accordingly.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section LinearPumpingBounded

variable {T : Type u}
variable {α : Type v}

/--
If X occurs among the first m+1 states of a linear-yield spine, then the
terminal context from the root to X has total length at most m.
-/
theorem linearYieldSpine_mem_take_decompose
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A X : T}
    {word : Word α}
    {path : List T}
    (s :
      LinearYieldSpine terminalRule binaryRule
        A word path)
    (m : Nat)
    (hmem : X ∈ path.take (m + 1)) :
    ∃ u v x : Word α,
      LinearSpineContext terminalRule binaryRule
        A X u v
      ∧
      UntypedDerives terminalRule binaryRule X x
      ∧
      word = u ++ x ++ v
      ∧
      u.length + v.length ≤ m := by
  induction s generalizing X m with
  | @terminal A a hterm =>
      have hXA : X = A := by
        simpa using hmem
      subst X
      exact
        ⟨[], [], [a],
          LinearSpineContext.refl A,
          UntypedDerives.terminal hterm,
          by simp,
          by simp⟩
  | @binaryLeft A B C a childWord childPath hbin child hsibling ih =>
      cases m with
      | zero =>
          have hXA : X = A := by
            simpa using hmem
          subst X
          exact
            ⟨[], [], childWord ++ [a],
              LinearSpineContext.refl A,
              linearYieldSpine_to_derives
                terminalRule binaryRule
                (LinearYieldSpine.binaryLeft
                  hbin child hsibling),
              by simp,
              by simp⟩
      | succ m =>
          have hcases :
              X = A ∨
              X ∈ childPath.take (m + 1) := by
            simpa [Nat.succ_eq_add_one,
              Nat.add_assoc] using hmem
          rcases hcases with hXA | htail
          · subst X
            exact
              ⟨[], [], childWord ++ [a],
                LinearSpineContext.refl A,
                linearYieldSpine_to_derives
                  terminalRule binaryRule
                  (LinearYieldSpine.binaryLeft
                    hbin child hsibling),
                by simp,
                by simp⟩
          · obtain
              ⟨u, v, x, hctx, dx, heq, hbound⟩ :=
              ih m htail
            refine
              ⟨u, v ++ [a], x,
                LinearSpineContext.rightSibling
                  hbin hsibling hctx,
                dx, ?_, ?_⟩
            · rw [heq]
              simp [List.append_assoc]
            · simp [List.length_append]
              omega
  | @binaryRight A B C a childWord childPath hbin hsibling child ih =>
      cases m with
      | zero =>
          have hXA : X = A := by
            simpa using hmem
          subst X
          exact
            ⟨[], [], [a] ++ childWord,
              LinearSpineContext.refl A,
              linearYieldSpine_to_derives
                terminalRule binaryRule
                (LinearYieldSpine.binaryRight
                  hbin hsibling child),
              by simp,
              by simp⟩
      | succ m =>
          have hcases :
              X = A ∨
              X ∈ childPath.take (m + 1) := by
            simpa [Nat.succ_eq_add_one,
              Nat.add_assoc] using hmem
          rcases hcases with hXA | htail
          · subst X
            exact
              ⟨[], [], [a] ++ childWord,
                LinearSpineContext.refl A,
                linearYieldSpine_to_derives
                  terminalRule binaryRule
                  (LinearYieldSpine.binaryRight
                    hbin hsibling child),
                by simp,
                by simp⟩
          · obtain
              ⟨u, v, x, hctx, dx, heq, hbound⟩ :=
              ih m htail
            refine
              ⟨[a] ++ u, v, x,
                LinearSpineContext.leftSibling
                  hbin hsibling hctx,
                dx, ?_, ?_⟩
            · rw [heq]
              simp [List.append_assoc]
            · simp [List.length_append]
              omega

/--
A duplicate among the first m+1 spine states yields a pumping decomposition
whose outer material plus pumped pieces has length at most m.
-/
theorem linearYieldSpine_duplicate_take_decompose
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A X : T}
    {word : Word α}
    {path : List T}
    (s :
      LinearYieldSpine terminalRule binaryRule
        A word path)
    (m : Nat)
    (hdup :
      List.Duplicate X (path.take (m + 1))) :
    ∃ u v x y z : Word α,
      LinearSpineContext terminalRule binaryRule
        A X u z
      ∧
      LinearSpineContext terminalRule binaryRule
        X X v y
      ∧
      UntypedDerives terminalRule binaryRule X x
      ∧
      word = u ++ v ++ x ++ y ++ z
      ∧
      0 < (v ++ y).length
      ∧
      (u ++ v ++ y ++ z).length ≤ m := by
  induction s generalizing X m with
  | @terminal A a hterm =>
      have hfalse :
          ¬ List.Duplicate X ([A] : List T) :=
        List.not_duplicate_singleton X A
      apply False.elim
      apply hfalse
      simpa using hdup
  | @binaryLeft A B C a childWord childPath hbin child hsibling ih =>
      cases m with
      | zero =>
          have hfalse :
              ¬ List.Duplicate X ([A] : List T) :=
            List.not_duplicate_singleton X A
          apply False.elim
          apply hfalse
          simpa using hdup
      | succ m =>
          have hcases :
              A = X ∧ X ∈ childPath.take (m + 1)
                ∨
              List.Duplicate X
                (childPath.take (m + 1)) := by
            simpa [Nat.succ_eq_add_one,
              Nat.add_assoc] using
              ((List.duplicate_cons_iff).1 hdup)
          rcases hcases with hhead | htail
          · rcases hhead with ⟨hAX, hmem⟩
            subst X
            obtain
              ⟨u0, v0, x, hctx0, dx,
                heq0, hbound0⟩ :=
              linearYieldSpine_mem_take_decompose
                terminalRule binaryRule child m hmem
            refine
              ⟨[], u0, x, v0 ++ [a], [],
                LinearSpineContext.refl A,
                LinearSpineContext.rightSibling
                  hbin hsibling hctx0,
                dx, ?_, ?_, ?_⟩
            · rw [heq0]
              simp [List.append_assoc]
            · simp
            · simp [List.length_append]
              omega
          · obtain
              ⟨u, v, x, y, z,
                houter, hself, dx, heq,
                hpos, hbound⟩ :=
              ih m htail
            refine
              ⟨u, v, x, y, z ++ [a],
                LinearSpineContext.rightSibling
                  hbin hsibling houter,
                hself, dx, ?_, hpos, ?_⟩
            · rw [heq]
              simp [List.append_assoc]
            · simp [List.length_append] at hbound ⊢
              omega
  | @binaryRight A B C a childWord childPath hbin hsibling child ih =>
      cases m with
      | zero =>
          have hfalse :
              ¬ List.Duplicate X ([A] : List T) :=
            List.not_duplicate_singleton X A
          apply False.elim
          apply hfalse
          simpa using hdup
      | succ m =>
          have hcases :
              A = X ∧ X ∈ childPath.take (m + 1)
                ∨
              List.Duplicate X
                (childPath.take (m + 1)) := by
            simpa [Nat.succ_eq_add_one,
              Nat.add_assoc] using
              ((List.duplicate_cons_iff).1 hdup)
          rcases hcases with hhead | htail
          · rcases hhead with ⟨hAX, hmem⟩
            subst X
            obtain
              ⟨u0, v0, x, hctx0, dx,
                heq0, hbound0⟩ :=
              linearYieldSpine_mem_take_decompose
                terminalRule binaryRule child m hmem
            refine
              ⟨[], [a] ++ u0, x, v0, [],
                LinearSpineContext.refl A,
                LinearSpineContext.leftSibling
                  hbin hsibling hctx0,
                dx, ?_, ?_, ?_⟩
            · rw [heq0]
              simp [List.append_assoc]
            · simp
            · simp [List.length_append]
              omega
          · obtain
              ⟨u, v, x, y, z,
                houter, hself, dx, heq,
                hpos, hbound⟩ :=
              ih m htail
            refine
              ⟨[a] ++ u, v, x, y, z,
                LinearSpineContext.leftSibling
                  hbin hsibling houter,
                hself, dx, ?_, hpos, ?_⟩
            · rw [heq]
              simp [List.append_assoc]
            · simp [List.length_append] at hbound ⊢
              omega

/--
Standard bounded pumping lemma for an exact linear-yield spine.

The threshold and the bound on the outer/pumped material are both the number
of possible spine states.
-/
theorem linearYieldSpine_pumping_bounded
    [Fintype T] [DecidableEq T]
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A : T}
    {word : Word α}
    {path : List T}
    (s :
      LinearYieldSpine terminalRule binaryRule
        A word path)
    (hlong :
      Fintype.card T < word.length) :
    ∃ u v x y z : Word α,
      word = u ++ v ++ x ++ y ++ z
      ∧
      0 < (v ++ y).length
      ∧
      (u ++ v ++ y ++ z).length
        ≤ Fintype.card T
      ∧
      ∀ n : Nat,
        UntypedDerives terminalRule binaryRule A
          (u ++
            linearPumpLeft v n ++
            x ++
            linearPumpRight y n ++
            z) := by
  let p := Fintype.card T
  have hpathLen :
      path.length = word.length := by
    symm
    exact
      linearYieldSpine_length_eq_path
        terminalRule binaryRule s
  have hprefLen :
      (path.take (p + 1)).length = p + 1 := by
    rw [List.length_take]
    have hle :
        p + 1 ≤ path.length := by
      rw [hpathLen]
      omega
    rw [Nat.min_eq_left hle]
  have hnot :
      ¬ (path.take (p + 1)).Nodup := by
    intro hnodup
    have hcard :
        (path.take (p + 1)).length
          ≤ Fintype.card T := by
      rw [← List.toFinset_card_of_nodup hnodup]
      exact Finset.card_le_univ _
    rw [hprefLen] at hcard
    dsimp [p] at hcard
    omega
  obtain ⟨X, hdup⟩ :=
    (List.exists_duplicate_iff_not_nodup).2 hnot
  obtain
    ⟨u, v, x, y, z,
      houter, hself, dx, heq,
      hpos, hbound⟩ :=
    linearYieldSpine_duplicate_take_decompose
      terminalRule binaryRule s p hdup
  refine
    ⟨u, v, x, y, z,
      heq, hpos, ?_, ?_⟩
  · simpa [p] using hbound
  · intro n
    have dpump :=
      linearSpineContext_pump
        terminalRule binaryRule hself dx n
    have dout :=
      linearSpineContext_plug
        terminalRule binaryRule houter dpump
    simpa [List.append_assoc] using dout

/-- Paper-style bounded pumping lemma for any finite linear-spine grammar. -/
theorem linearSpine_pumping_bounded
    [Fintype T] [DecidableEq T]
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape :
      LinearSpineShape terminalRule binaryRule Wrapper)
    {A : T}
    {word : Word α}
    (hA : ¬ Wrapper A)
    (d :
      UntypedDerives terminalRule binaryRule A word)
    (hlong :
      Fintype.card T < word.length) :
    ∃ u v x y z : Word α,
      word = u ++ v ++ x ++ y ++ z
      ∧
      0 < (v ++ y).length
      ∧
      (u ++ v ++ y ++ z).length
        ≤ Fintype.card T
      ∧
      ∀ n : Nat,
        UntypedDerives terminalRule binaryRule A
          (u ++
            linearPumpLeft v n ++
            x ++
            linearPumpRight y n ++
            z) := by
  obtain ⟨path, spine⟩ :=
    exists_exact_linearYieldSpine_of_nonwrapper_derives
      terminalRule binaryRule Wrapper shape hA d
  exact
    linearYieldSpine_pumping_bounded
      terminalRule binaryRule spine hlong

end LinearPumpingBounded

end TCS1
end LeanCfgProject
