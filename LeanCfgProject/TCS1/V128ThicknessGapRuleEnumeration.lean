import LeanCfgProject.TCS1.V128ThicknessGapReducedness

/-!
# TCS #1 v128: enumerate the *actual* indexed source productions

Every production of the concrete finite SSBNF family has one of seven
fixed forms (including S₀ → U) or one of two indexed forms for
i = 1,...,n. Thus there are 2n+7 production *codes*.

Unlike a standalone arithmetic definition `2*n+7`, the source
rules here are decoded into the same `GapTerminalRule`,
`GapBinaryRule`, and `GapStartRule` relations used by the language
and typed-thickness theorems. Soundness and surjective coverage
ensure the enumeration is exactly the grammar's production schemes.

The size counts treat each indexed nonterminal as one grammar symbol,
as in the manuscript's standard grammar-symbol size convention;
bit-level encoding of integer indices is a different convention.
-/

namespace LeanCfgProject
namespace TCS1

/-- Seven fixed rules and two indexed rules for each i=1,...,n. -/
inductive GapRuleCode (n : Nat) where
  | start
  | universalA
  | universalC
  | markerC
  | exponentA
  | universalPair
  | universalExp
  | exponentC (i : Fin n)
  | exponentPair (i : Fin n)
deriving DecidableEq, Fintype

/-- Finite source-production datums, including the start production. -/
inductive GapRuleDatum (n : Nat) where
  | start (A : GapNonterminal n)
  | terminal (A : GapNonterminal n) (a : Bool)
  | binary (A B C : GapNonterminal n)
deriving DecidableEq

/-- A datum belongs to the source grammar's actual relations. -/
def gapRuleValid (n : Nat) : GapRuleDatum n → Prop
  | .start A => GapStartRule n A
  | .terminal A a => GapTerminalRule n A a
  | .binary A B C => GapBinaryRule n A B C

/-- Decode every indexed production code into the source grammar syntax. -/
def gapRuleDecode (n : Nat) : GapRuleCode n → GapRuleDatum n
  | .start => .start .universal
  | .universalA => .terminal .universal false
  | .universalC => .terminal .universal true
  | .markerC => .terminal .marker true
  | .exponentA =>
      .terminal (.exponent ⟨0, Nat.zero_lt_succ n⟩) false
  | .universalPair =>
      .binary .universal .universal .universal
  | .universalExp =>
      .binary .universal (.exponent ⟨n, Nat.lt_succ_self n⟩) .marker
  | .exponentC i =>
      .terminal (.exponent i.succ) true
  | .exponentPair i =>
      .binary (.exponent i.succ)
        (.exponent i.castSucc) (.exponent i.castSucc)

/-- Each code denotes a genuine terminal, binary or start production. -/
theorem gapRuleDecode_sound (n : Nat) (code : GapRuleCode n) :
    gapRuleValid n (gapRuleDecode n code) := by
  cases code with
  | start =>
      rfl
  | universalA =>
      exact GapTerminalRule.universalA
  | universalC =>
      exact GapTerminalRule.universalC
  | markerC =>
      exact GapTerminalRule.markerC
  | exponentA =>
      exact GapTerminalRule.exponentA
  | universalPair =>
      exact GapBinaryRule.universalPair
  | universalExp =>
      exact GapBinaryRule.universalExp
  | exponentC i =>
      exact GapTerminalRule.exponentC (by
        change 0 < i.val + 1
        omega)
  | exponentPair i =>
      exact GapBinaryRule.exponentPair rfl

/-- Every terminal production is represented by one of the codes. -/
theorem gapRuleDecode_terminal_complete (n : Nat)
    {A : GapNonterminal n} {a : Bool}
    (h : GapTerminalRule n A a) :
    ∃ code : GapRuleCode n,
      gapRuleDecode n code = .terminal A a := by
  cases h with
  | universalA =>
      exact ⟨.universalA, rfl⟩
  | universalC =>
      exact ⟨.universalC, rfl⟩
  | markerC =>
      exact ⟨.markerC, rfl⟩
  | exponentA =>
      exact ⟨.exponentA, rfl⟩
  | @exponentC i hi =>
      let j : Fin n := ⟨i.val - 1, by
        have hiLt := i.isLt
        omega⟩
      have hj : j.succ = i := by
        apply Fin.ext
        change j.val + 1 = i.val
        dsimp [j]
        omega
      exact ⟨.exponentC j, by
        change GapRuleDatum.terminal (.exponent j.succ) true =
          GapRuleDatum.terminal (.exponent i) true
        rw [hj]⟩

/-- Every binary production is represented by one of the codes. -/
theorem gapRuleDecode_binary_complete (n : Nat)
    {A B C : GapNonterminal n}
    (h : GapBinaryRule n A B C) :
    ∃ code : GapRuleCode n,
      gapRuleDecode n code = .binary A B C := by
  cases h with
  | universalPair =>
      exact ⟨.universalPair, rfl⟩
  | universalExp =>
      exact ⟨.universalExp, rfl⟩
  | @exponentPair i j hstep =>
      let k : Fin n := ⟨j.val, by
        have hiLt := i.isLt
        omega⟩
      have hk0 : k.castSucc = j := Fin.ext rfl
      have hk1 : k.succ = i := by
        apply Fin.ext
        change k.val + 1 = i.val
        dsimp [k]
        omega
      exact ⟨.exponentPair k, by
        change GapRuleDatum.binary
            (.exponent k.succ) (.exponent k.castSucc)
            (.exponent k.castSucc) =
          GapRuleDatum.binary (.exponent i)
            (.exponent j) (.exponent j)
        rw [hk0, hk1]⟩

/-- The code family is sound and surjective onto actual source rules. -/
theorem gapRuleDecode_exact (n : Nat)
    (r : GapRuleDatum n) :
    gapRuleValid n r ↔
      ∃ code : GapRuleCode n, gapRuleDecode n code = r := by
  constructor
  · intro hv
    cases r with
    | start A =>
        change GapStartRule n A at hv
        subst A
        exact ⟨.start, rfl⟩
    | terminal A a =>
        exact gapRuleDecode_terminal_complete n hv
    | binary A B C =>
        exact gapRuleDecode_binary_complete n hv
  · rintro ⟨code, rfl⟩
    exact gapRuleDecode_sound n code

/-- Concrete enumeration of seven rules and two families of n rules. -/
def gapRuleCodeEnumeration (n : Nat) : List (GapRuleCode n) :=
  [.start, .universalA, .universalC, .markerC, .exponentA,
    .universalPair, .universalExp] ++
  (List.ofFn (fun i : Fin n => GapRuleCode.exponentC i)) ++
  (List.ofFn (fun i : Fin n => GapRuleCode.exponentPair i))

/-- Counting the actual enumerated rules yields the paper's exact 2n+7. -/
theorem gapRuleCodeEnumeration_length (n : Nat) :
    (gapRuleCodeEnumeration n).length = 2 * n + 7 := by
  simp [gapRuleCodeEnumeration]
  omega

/-- Hence the number of source production codes grows linearly in n. -/
theorem gapRuleCodeEnumeration_linear (n : Nat) :
    (gapRuleCodeEnumeration n).length ≤ 9 * (n + 1) := by
  rw [gapRuleCodeEnumeration_length]
  omega

end TCS1
end LeanCfgProject
