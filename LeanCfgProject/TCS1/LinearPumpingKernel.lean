import LeanCfgProject.TCS1.LinearSpineSemantic
import Mathlib.Data.List.Duplicate
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# TCS #1 v79: pumping kernel for finite linear-spine grammars

This is the internal replacement for the one external classical theorem used
by the Delta-star non-linearity argument.

The normalized linear grammars constructed in Section 8 have a unique
continuing spine. This file proves the corresponding pumping lemma directly
for that representation:

* every derivation rooted at a non-wrapper symbol has an exact yield-preserving
  linear spine;
* a repeated state on that spine determines a nontrivial self-context;
* the self-context can be iterated any number of times;
* therefore every sufficiently long word has the usual linear pumping
  decomposition with the pumped pieces confined to the two ends.

No grammar-normal-form theorem is assumed here: the already verified
LinearSpineShape is exactly the representation needed by the argument.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section LinearPumpingKernel

variable {T : Type u}
variable {α : Type v}

def linearPumpLeft (w : Word α) : Nat → Word α
  | 0 => []
  | n + 1 => w ++ linearPumpLeft w n

def linearPumpRight (w : Word α) : Nat → Word α
  | 0 => []
  | n + 1 => linearPumpRight w n ++ w

@[simp] theorem linearPumpLeft_zero (w : Word α) :
    linearPumpLeft w 0 = [] := rfl

@[simp] theorem linearPumpLeft_succ (w : Word α) (n : Nat) :
    linearPumpLeft w (n + 1) =
      w ++ linearPumpLeft w n := rfl

@[simp] theorem linearPumpRight_zero (w : Word α) :
    linearPumpRight w 0 = [] := rfl

@[simp] theorem linearPumpRight_succ (w : Word α) (n : Nat) :
    linearPumpRight w (n + 1) =
      linearPumpRight w n ++ w := rfl

inductive LinearSpineContext
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop) :
    T → T → Word α → Word α → Prop
  | refl (A : T) :
      LinearSpineContext terminalRule binaryRule A A [] []
  | rightSibling
      {A B C X : T}
      {a : α}
      {u v : Word α}
      (hbin : binaryRule A B C)
      (hsibling : terminalRule C a)
      (ctx :
        LinearSpineContext terminalRule binaryRule B X u v) :
      LinearSpineContext terminalRule binaryRule
        A X u (v ++ [a])
  | leftSibling
      {A B C X : T}
      {a : α}
      {u v : Word α}
      (hbin : binaryRule A B C)
      (hsibling : terminalRule B a)
      (ctx :
        LinearSpineContext terminalRule binaryRule C X u v) :
      LinearSpineContext terminalRule binaryRule
        A X ([a] ++ u) v

theorem linearSpineContext_plug
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A B : T}
    {u v x : Word α}
    (ctx :
      LinearSpineContext terminalRule binaryRule A B u v)
    (d :
      UntypedDerives terminalRule binaryRule B x) :
    UntypedDerives terminalRule binaryRule A
      (u ++ x ++ v) := by
  induction ctx with
  | refl A =>
      simpa using d
  | @rightSibling A B C X a u v hbin hsibling ctx ih =>
      have dA :=
        UntypedDerives.binary
          hbin (ih d) (UntypedDerives.terminal hsibling)
      simpa [List.append_assoc] using dA
  | @leftSibling A B C X a u v hbin hsibling ctx ih =>
      have dA :=
        UntypedDerives.binary
          hbin (UntypedDerives.terminal hsibling) (ih d)
      simpa [List.append_assoc] using dA

theorem linearSpineContext_pump
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {X : T}
    {v y x : Word α}
    (ctx :
      LinearSpineContext terminalRule binaryRule X X v y)
    (d :
      UntypedDerives terminalRule binaryRule X x) :
    ∀ n : Nat,
      UntypedDerives terminalRule binaryRule X
        (linearPumpLeft v n ++
          x ++
          linearPumpRight y n) := by
  intro n
  induction n with
  | zero =>
      simpa using d
  | succ n ih =>
      have hp :=
        linearSpineContext_plug
          terminalRule binaryRule ctx ih
      simpa [linearPumpLeft, linearPumpRight,
        List.append_assoc] using hp

theorem exists_exact_linearYieldSpine_of_nonwrapper_derives
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    {A : T}
    {word : Word α}
    (hA : ¬ Wrapper A)
    (d : UntypedDerives terminalRule binaryRule A word) :
    ∃ path : List T,
      LinearYieldSpine terminalRule binaryRule
        A word path := by
  induction d with
  | @terminal A a hterm =>
      exact
        ⟨[A],
          LinearYieldSpine.terminal hterm⟩
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      rcases shape.binary_children hbin with
        ⟨hBW, hCnW⟩ | ⟨hBnW, hCW⟩
      · cases dB with
        | terminal htermB =>
            obtain ⟨path, child⟩ := ihC hCnW
            exact
              ⟨A :: path,
                LinearYieldSpine.binaryRight
                  hbin htermB child⟩
        | binary hbinB dBB dBC =>
            exact False.elim
              (shape.wrapper_no_binary hBW hbinB)
      · cases dC with
        | terminal htermC =>
            obtain ⟨path, child⟩ := ihB hBnW
            exact
              ⟨A :: path,
                LinearYieldSpine.binaryLeft
                  hbin child htermC⟩
        | binary hbinC dCB dCC =>
            exact False.elim
              (shape.wrapper_no_binary hCW hbinC)

theorem linearYieldSpine_mem_decompose
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A X : T}
    {word : Word α}
    {path : List T}
    (s :
      LinearYieldSpine terminalRule binaryRule
        A word path)
    (hmem : X ∈ path) :
    ∃ u v x : Word α,
      LinearSpineContext terminalRule binaryRule
        A X u v
      ∧
      UntypedDerives terminalRule binaryRule X x
      ∧
      word = u ++ x ++ v := by
  induction s with
  | @terminal A a hterm =>
      simp only [List.mem_singleton] at hmem
      subst X
      exact
        ⟨[], [], [a],
          LinearSpineContext.refl A,
          UntypedDerives.terminal hterm,
          by simp⟩
  | @binaryLeft A B C a childWord childPath hbin child hsibling ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with hXA | htail
      · subst X
        exact
          ⟨[], [], childWord ++ [a],
            LinearSpineContext.refl A,
            linearYieldSpine_to_derives
              terminalRule binaryRule
              (LinearYieldSpine.binaryLeft
                hbin child hsibling),
            by simp⟩
      · obtain ⟨u, v, x, hctx, dx, heq⟩ :=
          ih htail
        refine
          ⟨u, v ++ [a], x,
            LinearSpineContext.rightSibling
              hbin hsibling hctx,
            dx, ?_⟩
        rw [heq]
        simp [List.append_assoc]
  | @binaryRight A B C a childWord childPath hbin hsibling child ih =>
      simp only [List.mem_cons] at hmem
      rcases hmem with hXA | htail
      · subst X
        exact
          ⟨[], [], [a] ++ childWord,
            LinearSpineContext.refl A,
            linearYieldSpine_to_derives
              terminalRule binaryRule
              (LinearYieldSpine.binaryRight
                hbin hsibling child),
            by simp⟩
      · obtain ⟨u, v, x, hctx, dx, heq⟩ :=
          ih htail
        refine
          ⟨[a] ++ u, v, x,
            LinearSpineContext.leftSibling
              hbin hsibling hctx,
            dx, ?_⟩
        rw [heq]
        simp [List.append_assoc]

theorem linearYieldSpine_duplicate_decompose
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    {A X : T}
    {word : Word α}
    {path : List T}
    (s :
      LinearYieldSpine terminalRule binaryRule
        A word path)
    (hdup : List.Duplicate X path) :
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
      0 < (v ++ y).length := by
  induction s with
  | @terminal A a hterm =>
      exact False.elim
        (List.not_duplicate_singleton X A hdup)
  | @binaryLeft A B C a childWord childPath hbin child hsibling ih =>
      have hcases :
          A = X ∧ X ∈ childPath
            ∨
          List.Duplicate X childPath :=
        (List.duplicate_cons_iff).1 hdup
      rcases hcases with hhead | htail
      · rcases hhead with ⟨hAX, hmem⟩
        subst X
        obtain ⟨u0, v0, x, hctx0, dx, heq0⟩ :=
          linearYieldSpine_mem_decompose
            terminalRule binaryRule child hmem
        refine
          ⟨[], u0, x, v0 ++ [a], [],
            LinearSpineContext.refl A,
            LinearSpineContext.rightSibling
              hbin hsibling hctx0,
            dx, ?_, ?_⟩
        · rw [heq0]
          simp [List.append_assoc]
        · simp
      · obtain
          ⟨u, v, x, y, z,
            houter, hself, dx, heq, hpos⟩ :=
          ih htail
        refine
          ⟨u, v, x, y, z ++ [a],
            LinearSpineContext.rightSibling
              hbin hsibling houter,
            hself, dx, ?_, hpos⟩
        rw [heq]
        simp [List.append_assoc]
  | @binaryRight A B C a childWord childPath hbin hsibling child ih =>
      have hcases :
          A = X ∧ X ∈ childPath
            ∨
          List.Duplicate X childPath :=
        (List.duplicate_cons_iff).1 hdup
      rcases hcases with hhead | htail
      · rcases hhead with ⟨hAX, hmem⟩
        subst X
        obtain ⟨u0, v0, x, hctx0, dx, heq0⟩ :=
          linearYieldSpine_mem_decompose
            terminalRule binaryRule child hmem
        refine
          ⟨[], [a] ++ u0, x, v0, [],
            LinearSpineContext.refl A,
            LinearSpineContext.leftSibling
              hbin hsibling hctx0,
            dx, ?_, ?_⟩
        · rw [heq0]
          simp [List.append_assoc]
        · simp
      · obtain
          ⟨u, v, x, y, z,
            houter, hself, dx, heq, hpos⟩ :=
          ih htail
        refine
          ⟨[a] ++ u, v, x, y, z,
            LinearSpineContext.leftSibling
              hbin hsibling houter,
            hself, dx, ?_, hpos⟩
        rw [heq]
        simp [List.append_assoc]

theorem linearYieldSpine_pumping
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
      ∀ n : Nat,
        UntypedDerives terminalRule binaryRule A
          (u ++
            linearPumpLeft v n ++
            x ++
            linearPumpRight y n ++
            z) := by
  have hlen :
      path.length = word.length := by
    symm
    exact
      linearYieldSpine_length_eq_path
        terminalRule binaryRule s
  have hnot : ¬ path.Nodup := by
    intro hnodup
    have hcard :
        path.length ≤ Fintype.card T := by
      rw [← List.toFinset_card_of_nodup hnodup]
      exact Finset.card_le_univ _
    rw [hlen] at hcard
    omega
  obtain ⟨X, hdup⟩ :=
    (List.exists_duplicate_iff_not_nodup).2 hnot
  obtain
    ⟨u, v, x, y, z,
      houter, hself, dx, heq, hpos⟩ :=
    linearYieldSpine_duplicate_decompose
      terminalRule binaryRule s hdup
  refine ⟨u, v, x, y, z, heq, hpos, ?_⟩
  intro n
  have dpump :=
    linearSpineContext_pump
      terminalRule binaryRule hself dx n
  have dout :=
    linearSpineContext_plug
      terminalRule binaryRule houter dpump
  simpa [List.append_assoc] using dout

theorem linearSpine_pumping
    [Fintype T] [DecidableEq T]
    (terminalRule : T → α → Prop)
    (binaryRule : T → T → T → Prop)
    (Wrapper : T → Prop)
    (shape : LinearSpineShape terminalRule binaryRule Wrapper)
    {A : T}
    {word : Word α}
    (hA : ¬ Wrapper A)
    (d : UntypedDerives terminalRule binaryRule A word)
    (hlong :
      Fintype.card T < word.length) :
    ∃ u v x y z : Word α,
      word = u ++ v ++ x ++ y ++ z
      ∧
      0 < (v ++ y).length
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
    linearYieldSpine_pumping
      terminalRule binaryRule spine hlong

end LinearPumpingKernel

end TCS1
end LeanCfgProject
