import LeanCfgProject.TCS1.NormalizationLanguageBounds

/-!
# TCS #1 v65: terminal-isolation kernel

Appendix A isolates terminals occurring in mixed or long right-hand sides
before binarization. This module formalizes that transformation at the local
grammar-operator level.

A right-hand side is a list of either nonterminals or terminal symbols.
Given an interpretation of every old nonterminal by a terminal language,
RhsRealizes gives the words realized by such a right-hand side. The
terminal-isolated grammar uses fresh wrapper nonterminals W_a; singleton
terminal rules are left unchanged, while every terminal in any other
right-hand side is replaced by its wrapper.

The main theorem says that, for an arbitrary interpretation of the old
nonterminals, every old right-hand side and its isolated version realize
exactly the same terminal words. Consequently the one-step grammar operator
on every original nonterminal is unchanged. This is the local semantic fact
needed for the terminal-isolation stage of Proposition 7.4.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section TerminalIsolation

variable {N : Type u}
variable {α : Type v}

abbrev MixedSymbol (N : Type u) (α : Type v) :=
  Sum N α

/--
Terminal words realized by a mixed right-hand side under an arbitrary
interpretation L of its nonterminals.
-/
def RhsRealizes
    (L : N → Set (List α)) :
    List (MixedSymbol N α) → List α → Prop
  | [], w =>
      w = []
  | Sum.inr a :: rhs, w =>
      ∃ tail,
        w = a :: tail ∧
        RhsRealizes L rhs tail
  | Sum.inl A :: rhs, w =>
      ∃ u v,
        w = u ++ v ∧
        u ∈ L A ∧
        RhsRealizes L rhs v

/-- Fresh wrapper Sum.inr a denotes exactly the one-letter word [a]. -/
def isolatedInterpretation
    (L : N → Set (List α)) :
    (N ⊕ α) → Set (List α)
  | Sum.inl A => L A
  | Sum.inr a => {[a]}

/--
Map an old mixed symbol into the isolated alphabet/nonterminal universe.
When wrapTerminal=true, terminals become wrapper nonterminals; otherwise
they remain literal terminals.
-/
def isolateSymbol
    (wrapTerminal : Bool) :
    MixedSymbol N α → MixedSymbol (N ⊕ α) α
  | Sum.inl A => Sum.inl (Sum.inl A)
  | Sum.inr a =>
      if wrapTerminal then
        Sum.inl (Sum.inr a)
      else
        Sum.inr a

/--
Exact manuscript convention: a singleton terminal RHS stays terminal;
all other right-hand sides have every terminal occurrence wrapped.
-/
def isolateRhs :
    List (MixedSymbol N α) →
      List (MixedSymbol (N ⊕ α) α)
  | [Sum.inr a] => [Sum.inr a]
  | rhs => rhs.map (isolateSymbol true)

/--
Wrapping every terminal occurrence preserves the terminal word realized by a
right-hand side.
-/
theorem rhsRealizes_map_wrapped_iff
    (L : N → Set (List α))
    (rhs : List (MixedSymbol N α))
    (w : List α) :
    RhsRealizes L rhs w ↔
      RhsRealizes
        (isolatedInterpretation L)
        (rhs.map (isolateSymbol true))
        w := by
  induction rhs generalizing w with
  | nil =>
      simp [RhsRealizes]
  | cons s rhs ih =>
      cases s with
      | inl A =>
          simp only [isolateSymbol, List.map_cons]
          constructor
          · intro h
            rcases h with ⟨u, v, hw, hu, hv⟩
            exact ⟨u, v, hw, hu, (ih v).1 hv⟩
          · intro h
            rcases h with ⟨u, v, hw, hu, hv⟩
            exact ⟨u, v, hw, hu, (ih v).2 hv⟩
      | inr a =>
          simp only [isolateSymbol, List.map_cons, if_true]
          constructor
          · intro h
            rcases h with ⟨tail, hw, htail⟩
            refine ⟨[a], tail, ?_, ?_, ?_⟩
            · simpa using hw
            · simp [isolatedInterpretation]
            · exact (ih tail).1 htail
          · intro h
            rcases h with ⟨u, tail, hw, hu, htail⟩
            have hu' : u = [a] := by
              simpa [isolatedInterpretation] using hu
            subst u
            refine ⟨tail, ?_, ?_⟩
            · simpa using hw
            · exact (ih tail).2 htail

/--
The exact terminal-isolation operation, which leaves singleton terminal rules
alone, preserves RHS semantics.
-/
theorem rhsRealizes_isolateRhs_iff
    (L : N → Set (List α))
    (rhs : List (MixedSymbol N α))
    (w : List α) :
    RhsRealizes L rhs w ↔
      RhsRealizes
        (isolatedInterpretation L)
        (isolateRhs rhs)
        w := by
  cases rhs with
  | nil =>
      simp [isolateRhs, RhsRealizes]
  | cons s rest =>
      cases rest with
      | nil =>
          cases s with
          | inl A =>
              simpa [isolateRhs] using
                (rhsRealizes_map_wrapped_iff
                  L [Sum.inl A] w)
          | inr a =>
              simp [isolateRhs, RhsRealizes]
      | cons s₂ rest₂ =>
          simpa [isolateRhs] using
            (rhsRealizes_map_wrapped_iff
              L (s :: s₂ :: rest₂) w)

/-- An arbitrary CFG presentation as a predicate of mixed right-hand sides. -/
abbrev MixedRules (N : Type u) (α : Type v) :=
  N → List (MixedSymbol N α) → Prop

/--
One application of a grammar rule, evaluated against an arbitrary current
interpretation of its child nonterminals.
-/
def RuleStepLanguage
    (R : MixedRules N α)
    (L : N → Set (List α))
    (A : N) :
    Set (List α) :=
  {w | ∃ rhs, R A rhs ∧ RhsRealizes L rhs w}

/--
Rules of the terminal-isolated presentation. Original rules get their
isolated RHS; each fresh wrapper has its one-letter terminal rule.
-/
inductive IsolatedRule
    (R : MixedRules N α) :
    (N ⊕ α) →
      List (MixedSymbol (N ⊕ α) α) →
      Prop
  | original
      {A : N}
      {rhs : List (MixedSymbol N α)}
      (h : R A rhs) :
      IsolatedRule R (Sum.inl A) (isolateRhs rhs)
  | wrapper
      (a : α) :
      IsolatedRule R (Sum.inr a) [Sum.inr a]

/--
Terminal isolation preserves the one-step grammar operator on every original
nonterminal, for every interpretation of the old nonterminals.
-/
theorem terminalIsolation_ruleStep_eq
    (R : MixedRules N α)
    (L : N → Set (List α))
    (A : N) :
    RuleStepLanguage
        (IsolatedRule R)
        (isolatedInterpretation L)
        (Sum.inl A)
      =
    RuleStepLanguage R L A := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    rcases hw with ⟨rhs', hrule, hreal⟩
    cases hrule with
    | original hR =>
        exact ⟨_, hR,
          (rhsRealizes_isolateRhs_iff L _ w).2 hreal⟩
  · intro hw
    rcases hw with ⟨rhs, hR, hreal⟩
    exact
      ⟨isolateRhs rhs,
        IsolatedRule.original hR,
        (rhsRealizes_isolateRhs_iff L rhs w).1 hreal⟩

/-- Each fresh wrapper realizes exactly its intended one-letter word. -/
theorem terminalIsolation_wrapper_ruleStep
    (R : MixedRules N α)
    (L : N → Set (List α))
    (a : α) :
    RuleStepLanguage
        (IsolatedRule R)
        (isolatedInterpretation L)
        (Sum.inr a)
      =
    ({[a]} : Set (List α)) := by
  apply Set.ext
  intro w
  constructor
  · intro hw
    rcases hw with ⟨rhs, hrule, hreal⟩
    cases hrule with
    | wrapper _ =>
        rcases hreal with ⟨tail, hw, htail⟩
        have htailNil : tail = [] := htail
        subst tail
        simpa using hw
  · intro hw
    have hw' : w = [a] := by
      simpa using hw
    subst w
    refine ⟨[Sum.inr a], IsolatedRule.wrapper a, ?_⟩
    exact ⟨[], rfl, rfl⟩

end TerminalIsolation

end TCS1
end LeanCfgProject
