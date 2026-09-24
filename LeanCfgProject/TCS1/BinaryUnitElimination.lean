import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1: semantic correctness of unit elimination

After non-start epsilon elimination, the appendix computes unit closure and
copies every unit-reachable non-unit production to its source.  This module
formalizes exactly that transformation on the binary epsilon-free grammar from
BinaryEpsilonElimination and proves preservation of every nonterminal
language.

The copied unit-free grammar has only terminal and binary derivation rules.
A terminal/binary rule rooted at B may be used at A whenever B is reachable
from A through zero or more unit rules.  Both simulation directions are
proved, so unit elimination preserves the full terminal language, not merely
the nonempty part.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section BinaryUnitElimination

variable {N : Type u}
variable {α : Type v}

/-- Reflexive-transitive closure of a unit relation, oriented source to target. -/
inductive UnitReach
    (unit : N → N → Prop) :
    N → N → Prop
  | refl (A : N) :
      UnitReach unit A A
  | step
      {A B C : N}
      (hAB : unit A B)
      (hBC : UnitReach unit B C) :
      UnitReach unit A C

/-- Composition of unit-reachability paths. -/
theorem UnitReach.trans
    {unit : N → N → Prop}
    {A B C : N}
    (hAB : UnitReach unit A B)
    (hBC : UnitReach unit B C) :
    UnitReach unit A C := by
  induction hAB with
  | refl _ =>
      exact hBC
  | step hAX hXB ih =>
      exact UnitReach.step hAX (ih hBC)

/-- One unit edge is a unit-reachability path. -/
theorem UnitReach.single
    {unit : N → N → Prop}
    {A B : N}
    (h : unit A B) :
    UnitReach unit A B :=
  UnitReach.step h (UnitReach.refl B)

/--
Lift an epsilon-free derivation backward along a unit-closure path.
-/
theorem epsilonFreeDerives_of_unitReach
    (G : BinaryNullableGrammar N α)
    {A B : N} {w : List α}
    (hAB : UnitReach (EpsilonElimUnitRule G) A B)
    (d : EpsilonFreeDerives G B w) :
    EpsilonFreeDerives G A w := by
  induction hAB with
  | refl _ =>
      exact d
  | @step A B C hAB hBC ih =>
      exact EpsilonFreeDerives.unit hAB (ih d)

/--
Terminal rules of the unit-free grammar are copied to every unit-reachable
source.
-/
def UnitFreeTerminalRule
    (G : BinaryNullableGrammar N α)
    (A : N)
    (a : α) : Prop :=
  ∃ B,
    UnitReach (EpsilonElimUnitRule G) A B ∧
    G.terminalRule B a

/--
Binary rules of the unit-free grammar are copied to every unit-reachable
source.
-/
def UnitFreeBinaryRule
    (G : BinaryNullableGrammar N α)
    (A C D : N) : Prop :=
  ∃ B,
    UnitReach (EpsilonElimUnitRule G) A B ∧
    G.binaryRule B C D

/-- Derivations after eliminating all unit rules. -/
inductive UnitFreeDerives
    (G : BinaryNullableGrammar N α) :
    N → List α → Prop
  | terminal
      {A : N} {a : α}
      (h : UnitFreeTerminalRule G A a) :
      UnitFreeDerives G A [a]
  | binary
      {A C D : N} {wC wD : List α}
      (h : UnitFreeBinaryRule G A C D)
      (dC : UnitFreeDerives G C wC)
      (dD : UnitFreeDerives G D wD) :
      UnitFreeDerives G A (wC ++ wD)

/--
Changing the root by a unit-closure prefix is admissible in the copied
unit-free grammar.
-/
theorem unitFreeDerives_of_unitReach
    (G : BinaryNullableGrammar N α)
    {A B : N} {w : List α}
    (hAB : UnitReach (EpsilonElimUnitRule G) A B)
    (d : UnitFreeDerives G B w) :
    UnitFreeDerives G A w := by
  induction d with
  | @terminal B a hterm =>
      rcases hterm with ⟨C, hBC, hCa⟩
      exact UnitFreeDerives.terminal
        ⟨C, UnitReach.trans hAB hBC, hCa⟩

  | @binary B C D wC wD hbin dC dD ihC ihD =>
      rcases hbin with ⟨E, hBE, hECD⟩
      exact UnitFreeDerives.binary
        ⟨E, UnitReach.trans hAB hBE, hECD⟩
        dC dD

/--
Forward simulation: collapse explicit unit derivations into the copied root
rules.
-/
theorem epsilonFreeDerives_to_unitFree
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (d : EpsilonFreeDerives G A w) :
    UnitFreeDerives G A w := by
  induction d with
  | @terminal A a h =>
      exact UnitFreeDerives.terminal
        ⟨A, UnitReach.refl A, h⟩

  | @unit A B w h d ih =>
      exact unitFreeDerives_of_unitReach
        G
        (UnitReach.single h)
        ih

  | @binary A B C wB wC h dB dC ihB ihC =>
      exact UnitFreeDerives.binary
        ⟨A, UnitReach.refl A, h⟩
        ihB ihC

/--
Backward simulation: expand each copied rule by its unit-closure prefix.
-/
theorem unitFreeDerives_to_epsilonFree
    (G : BinaryNullableGrammar N α)
    {A : N} {w : List α}
    (d : UnitFreeDerives G A w) :
    EpsilonFreeDerives G A w := by
  induction d with
  | @terminal A a h =>
      rcases h with ⟨B, hAB, hBa⟩
      exact epsilonFreeDerives_of_unitReach
        G hAB (EpsilonFreeDerives.terminal hBa)

  | @binary A C D wC wD h dC dD ihC ihD =>
      rcases h with ⟨B, hAB, hBCD⟩
      have dB :
          EpsilonFreeDerives G B (wC ++ wD) :=
        EpsilonFreeDerives.binary hBCD ihC ihD
      exact epsilonFreeDerives_of_unitReach G hAB dB

/-- Unit elimination preserves every nonterminal terminal language exactly. -/
theorem unit_elimination_preserves_language
    (G : BinaryNullableGrammar N α)
    (A : N)
    (w : List α) :
    EpsilonFreeDerives G A w ↔
      UnitFreeDerives G A w := by
  constructor
  · exact epsilonFreeDerives_to_unitFree G
  · exact unitFreeDerives_to_epsilonFree G

/--
The full-language equality required by the normalization thickness interface.
-/
theorem unit_elimination_sameLanguage
    (G : BinaryNullableGrammar N α) :
    SameLanguage
      (fun A => {w | EpsilonFreeDerives G A w})
      (fun A => {w | UnitFreeDerives G A w}) := by
  intro A w
  exact unit_elimination_preserves_language G A w

end BinaryUnitElimination

end TCS1
end LeanCfgProject
