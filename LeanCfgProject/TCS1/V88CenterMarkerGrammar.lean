import LeanCfgProject.TCS1.V88CenterMarkerProduct
import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1 v88: finite CFG for the center-marker product

The manuscript displays

  S -> X d X
  X -> a X b | c.

This file gives an explicit finite binary CFG for that grammar and proves that
its start language is exactly CenterMarkerProductLanguage.  The few auxiliary
states only binarize the two displayed productions.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

private theorem replicate_succ_last
    (s : LpmSymbol) (n : Nat) :
    List.replicate n s ++ [s] =
      List.replicate (n + 1) s := by
  simpa using (List.replicate_add n 1 s).symm

inductive CenterMarkerProductNT where
  | s | x | r | y | ta | tb | td
  deriving DecidableEq, Fintype, Repr

inductive CenterMarkerProductTerminalRule :
    CenterMarkerProductNT → LpmSymbol → Prop
  | xCenter : CenterMarkerProductTerminalRule .x c
  | aWrap : CenterMarkerProductTerminalRule .ta a
  | bWrap : CenterMarkerProductTerminalRule .tb b
  | dWrap : CenterMarkerProductTerminalRule .td d

inductive CenterMarkerProductBinaryRule :
    CenterMarkerProductNT →
    CenterMarkerProductNT →
    CenterMarkerProductNT → Prop
  | xRule : CenterMarkerProductBinaryRule .x .ta .r
  | rRule : CenterMarkerProductBinaryRule .r .x .tb
  | sRule : CenterMarkerProductBinaryRule .s .x .y
  | yRule : CenterMarkerProductBinaryRule .y .td .x

/-- Finite binary presentation of S -> X d X, X -> a X b | c. -/
def centerMarkerProductGrammar :
    BinaryNullableGrammar CenterMarkerProductNT LpmSymbol where
  terminalRule := CenterMarkerProductTerminalRule
  binaryRule := CenterMarkerProductBinaryRule
  epsilonRule _ := False
  unitRule _ _ := False

/-- Closed forms for every auxiliary nonterminal. -/
def CenterMarkerProductBinaryShape :
    CenterMarkerProductNT → Word LpmSymbol → Prop
  | .s, w =>
      ∃ n m : Nat,
        w = lpmCore n c ++ [d] ++ lpmCore m c
  | .x, w =>
      ∃ n : Nat, w = lpmCore n c
  | .r, w =>
      ∃ n : Nat, w = lpmCore n c ++ [b]
  | .y, w =>
      ∃ n : Nat, w = [d] ++ lpmCore n c
  | .ta, w => w = [a]
  | .tb, w => w = [b]
  | .td, w => w = [d]

/-- Every derivation in the binarized grammar has the advertised form. -/
theorem centerMarkerProduct_binaryDerives_shape
    {A : CenterMarkerProductNT}
    {w : Word LpmSymbol}
    (deriv : BinaryNullableDerives centerMarkerProductGrammar A w) :
    CenterMarkerProductBinaryShape A w := by
  induction deriv with
  | terminal h =>
      change CenterMarkerProductTerminalRule _ _ at h
      cases h with
      | xCenter =>
          exact ⟨0, by simp [lpmCore]⟩
      | aWrap =>
          rfl
      | bWrap =>
          rfl
      | dWrap =>
          rfl
  | epsilon h =>
      exact False.elim h
  | unit h child ih =>
      exact False.elim h
  | @binary A B C wB wC h dB dC ihB ihC =>
      change CenterMarkerProductBinaryRule A B C at h
      cases h with
      | xRule =>
          change wB = [a] at ihB
          change ∃ n : Nat, wC = lpmCore n c ++ [b] at ihC
          rcases ihC with ⟨n, rfl⟩
          subst wB
          refine ⟨n + 1, ?_⟩
          simp [lpmCore, List.replicate_succ,
            replicate_succ_last, List.append_assoc]
      | rRule =>
          change ∃ n : Nat, wB = lpmCore n c at ihB
          change wC = [b] at ihC
          rcases ihB with ⟨n, rfl⟩
          subst wC
          exact ⟨n, rfl⟩
      | sRule =>
          change ∃ n : Nat, wB = lpmCore n c at ihB
          change ∃ m : Nat, wC = [d] ++ lpmCore m c at ihC
          rcases ihB with ⟨n, rfl⟩
          rcases ihC with ⟨m, rfl⟩
          exact ⟨n, m, by simp [List.append_assoc]⟩
      | yRule =>
          change wB = [d] at ihB
          change ∃ n : Nat, wC = lpmCore n c at ihC
          rcases ihC with ⟨n, rfl⟩
          subst wB
          exact ⟨n, rfl⟩

/-- The X nonterminal derives every a^n c b^n. -/
theorem centerMarkerProduct_x_derives
    (n : Nat) :
    BinaryNullableDerives centerMarkerProductGrammar
      .x (lpmCore n c) := by
  induction n with
  | zero =>
      simpa [lpmCore] using
        (BinaryNullableDerives.terminal
          (G := centerMarkerProductGrammar)
          CenterMarkerProductTerminalRule.xCenter)
  | succ n ih =>
      have da :
          BinaryNullableDerives centerMarkerProductGrammar .ta [a] :=
        BinaryNullableDerives.terminal
          CenterMarkerProductTerminalRule.aWrap
      have db :
          BinaryNullableDerives centerMarkerProductGrammar .tb [b] :=
        BinaryNullableDerives.terminal
          CenterMarkerProductTerminalRule.bWrap
      have dr :
          BinaryNullableDerives centerMarkerProductGrammar .r
            (lpmCore n c ++ [b]) :=
        BinaryNullableDerives.binary
          CenterMarkerProductBinaryRule.rRule ih db
      have dx :
          BinaryNullableDerives centerMarkerProductGrammar .x
            ([a] ++ (lpmCore n c ++ [b])) :=
        BinaryNullableDerives.binary
          CenterMarkerProductBinaryRule.xRule da dr
      simpa [lpmCore, List.replicate_succ,
        replicate_succ_last, List.append_assoc] using dx

/-- The auxiliary Y derives d followed by an arbitrary P-word. -/
theorem centerMarkerProduct_y_derives
    (m : Nat) :
    BinaryNullableDerives centerMarkerProductGrammar .y
      ([d] ++ lpmCore m c) := by
  have dd :
      BinaryNullableDerives centerMarkerProductGrammar .td [d] :=
    BinaryNullableDerives.terminal
      CenterMarkerProductTerminalRule.dWrap
  exact BinaryNullableDerives.binary
    CenterMarkerProductBinaryRule.yRule dd
    (centerMarkerProduct_x_derives m)

/-- The start state derives every canonical word of L_x. -/
theorem centerMarkerProduct_s_derives
    (n m : Nat) :
    BinaryNullableDerives centerMarkerProductGrammar .s
      (lpmCore n c ++ [d] ++ lpmCore m c) := by
  have ds := BinaryNullableDerives.binary
    CenterMarkerProductBinaryRule.sRule
    (centerMarkerProduct_x_derives n)
    (centerMarkerProduct_y_derives m)
  simpa [List.append_assoc] using ds

/-- Start language of the displayed finite grammar. -/
def CenterMarkerProductGrammarLanguage : Set (Word LpmSymbol) :=
  {w |
    BinaryNullableDerives centerMarkerProductGrammar .s w}

/-- Exact context-free grammar semantics for the v88 manuscript display. -/
theorem centerMarkerProductGrammar_language_eq :
    CenterMarkerProductGrammarLanguage = CenterMarkerProductLanguage := by
  apply Set.ext
  intro w
  constructor
  · intro dw
    exact centerMarkerProduct_binaryDerives_shape dw
  · rintro ⟨n, m, rfl⟩
    exact centerMarkerProduct_s_derives n m

end TCS1
end LeanCfgProject
