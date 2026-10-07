import LeanCfgProject.TCS1.V118LinearFilterShapeBridge

/-!
# TCS #1 v121: exact productive filtering of linear-spine grammars

The ordinary DFA product of an SSBNF grammar gives an exact language
intersection, but a source wrapper may acquire useless product-state copies
without any terminal production. Those copies invalidate the *strong* wrapper
shape predicate, even though the filtered language is still linear.

Here the product is trimmed to productive state copies, retaining precisely
the derivations needed for its language. We prove:
* sound and complete transfer of non-start derivations;
* exact filtered start language, including epsilon;
* the untyped linear-spine wrapper shape after trimming;
* finite nonterminal type for finite source/DFA state sets.

Combined with the arbitrary indexed linear normalization in the next
package, this proves the representation-level linear-regular intersection
step, not merely its untyped CFL language equality.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V121ProductiveLinearFilter

variable {α : Type u} {N : Type v} {Q : Type w}

/-- Only productive product-state copies are kept. -/
abbrev V121ProductiveFilterState
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop) :=
  {X : V115FilterState N Q //
    ∃ w : Word α,
      UntypedDerives
        (v115FilterTerminal δ t)
        (v115FilterBinary b) X w}

/-- Restrict terminal rules to the productive product-state subtype. -/
def v121ProductiveFilterTerminal
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop) :
    V121ProductiveFilterState δ t b → α → Prop :=
  fun X a => v115FilterTerminal δ t X.val a

/-- Restrict binary productions, without changing their source semantics. -/
def v121ProductiveFilterBinary
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop) :
    V121ProductiveFilterState δ t b →
    V121ProductiveFilterState δ t b →
    V121ProductiveFilterState δ t b → Prop :=
  fun A B C => v115FilterBinary b A.val B.val C.val

/-- Restrict accepting start children; epsilon is handled separately. -/
def v121ProductiveFilterStart
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop)
    (s : N → Prop)
    (q₀ : Q)
    (accept : Q → Prop) :
    V121ProductiveFilterState δ t b → Prop :=
  fun X => v115FilterStart s q₀ accept X.val

/-- The filtered productive states still form a finite state set. -/
theorem v121_productiveFilter_finite
    [Fintype N] [Fintype Q]
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop) :
    Finite (V121ProductiveFilterState δ t b) := by
  classical
  infer_instance

/-- Forget productive-state proofs in a trimmed derivation. -/
theorem v121_productiveFilterDerives_sound
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop)
    {X : V121ProductiveFilterState δ t b}
    {w : Word α}
    (d : UntypedDerives
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      X w) :
    UntypedDerives
      (v115FilterTerminal δ t)
      (v115FilterBinary b) X.val w := by
  induction d with
  | terminal h => exact UntypedDerives.terminal h
  | binary h _ _ ihB ihC =>
      exact UntypedDerives.binary h ihB ihC

/-- A successful product derivation uses only productive state copies. -/
theorem v121_productiveFilterDerives_complete
    (δ : Q → α → Q)
    (t : N → α → Prop)
    (b : N → N → N → Prop)
    {X : V115FilterState N Q}
    {w : Word α}
    (d : UntypedDerives
      (v115FilterTerminal δ t)
      (v115FilterBinary b) X w) :
    UntypedDerives
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      ⟨X, ⟨w, d⟩⟩ w := by
  induction d with
  | terminal h =>
      exact UntypedDerives.terminal h
  | @binary A B C wB wC h dB dC ihB ihC =>
      have hfiltered :
          v121ProductiveFilterBinary δ t b
            ⟨A, ⟨wB ++ wC,
              UntypedDerives.binary h dB dC⟩⟩
            ⟨B, ⟨wB, dB⟩⟩
            ⟨C, ⟨wC, dC⟩⟩ := h
      exact UntypedDerives.binary hfiltered ihB ihC

/-- Productive filtering does not change the DFA-product start language. -/
theorem v121_productiveFilterStartLanguage_eq
    (δ : Q → α → Q)
    (q₀ : Q)
    (accept : Q → Prop)
    (t : N → α → Prop)
    (b : N → N → N → Prop)
    (s : N → Prop)
    (eps : Prop) :
    UntypedStartLanguage
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (v121ProductiveFilterStart δ t b s q₀ accept)
      (eps ∧ accept q₀) =
    UntypedStartLanguage
      (v115FilterTerminal δ t)
      (v115FilterBinary b)
      (v115FilterStart s q₀ accept)
      (eps ∧ accept q₀) := by
  apply Set.ext
  intro word
  constructor
  · intro d
    cases d with
    | nonempty hs dx =>
        exact UntypedStartDerives.nonempty hs
          (v121_productiveFilterDerives_sound δ t b dx)
    | epsilon heps =>
        exact UntypedStartDerives.epsilon heps
  · intro d
    cases d with
    | @nonempty A word hs dx =>
        have hs' :
            v121ProductiveFilterStart δ t b s q₀ accept
              ⟨A, ⟨word, dx⟩⟩ := hs
        exact UntypedStartDerives.nonempty hs'
          (v121_productiveFilterDerives_complete δ t b dx)
    | epsilon heps =>
        exact UntypedStartDerives.epsilon heps

/--
The filtered language is exactly the regular intersection, and the
productive filtered grammar has the full linear-spine structure.
-/
theorem v121_productiveFilter_linear_package
    (δ : Q → α → Q)
    (q₀ : Q)
    (accept : Q → Prop)
    (t : N → α → Prop)
    (b : N → N → N → Prop)
    (s : N → Prop)
    (eps : Prop)
    (Wrapper : N → Prop)
    (shape : UntypedLinearSpineShape t b Wrapper) :
    UntypedStartLanguage
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (v121ProductiveFilterStart δ t b s q₀ accept)
      (eps ∧ accept q₀) =
    UntypedStartLanguage t b s eps ∩
      {word : Word α | accept (v115AutomatonRead δ q₀ word)}
    ∧
    UntypedLinearSpineShape
      (v121ProductiveFilterTerminal δ t b)
      (v121ProductiveFilterBinary δ t b)
      (fun X => Wrapper X.val.1) := by
  constructor
  · rw [v121_productiveFilterStartLanguage_eq]
    exact v115FilterStartLanguage_eq_inter δ q₀ accept t b s eps
  · refine
      { wrapper_terminal := ?_
        wrapper_no_binary := ?_
        binary_children := ?_ }
    · intro X hx
      obtain ⟨w, d⟩ := X.property
      cases d with
      | @terminal A a hterm =>
          exact ⟨a, hterm⟩
      | @binary A B C wB wC hb _ _ =>
          exact False.elim
            (shape.wrapper_no_binary hx hb.1)
    · intro X Y Z hx hbin
      exact shape.wrapper_no_binary hx hbin.1
    · intro X Y Z hbin
      exact shape.binary_children hbin.1

end V121ProductiveLinearFilter

end TCS1
end LeanCfgProject
