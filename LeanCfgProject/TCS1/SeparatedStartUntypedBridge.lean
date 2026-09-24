import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage
import LeanCfgProject.TCS1.SeparatedStartSSBNF

/-!
# TCS #1 v69: separated-start SSBNF to learner grammar bridge

The Section 7 learner is formulated with a separate start relation plus
terminal/binary non-start rules.  Appendix A constructs the same shape using a
fresh start symbol in SeparatedStartSSBNF.  This module proves the two
presentations equivalent.

It is the semantic adapter needed to feed the concrete output of Proposition
7.4 directly into the fixed-window characteristic-data theorems.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section SeparatedStartUntypedBridge

variable {N : Type u}
variable {α : Type v}

/-- Terminal rules of the final reduced non-start grammar. -/
def reducedSSBNFTerminalRule
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G) :
    ReducedUnitFreeState G start → α → Prop :=
  (reducedUnitFreeGrammar G start).terminalRule

/-- Binary rules of the final reduced non-start grammar. -/
def reducedSSBNFBinaryRule
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G) :
    ReducedUnitFreeState G start →
      ReducedUnitFreeState G start →
      ReducedUnitFreeState G start → Prop :=
  (reducedUnitFreeGrammar G start).binaryRule

/-- The learner's unique start child is the old reduced start. -/
def reducedSSBNFStartRule
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G) :
    ReducedUnitFreeState G start → Prop :=
  fun A => A = reducedUnitFreeStart G start

/--
The learner's non-start derivations are exactly derivations in the final
reduced terminal/binary grammar.
-/
theorem reducedSSBNF_untypedDerives_iff
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G)
    (A : ReducedUnitFreeState G start)
    (w : Word α) :
    UntypedDerives
        (reducedSSBNFTerminalRule G start)
        (reducedSSBNFBinaryRule G start)
        A w
      ↔
    BinaryNullableDerives
      (reducedUnitFreeGrammar G start) A w := by
  constructor
  · intro d
    induction d with
    | terminal h =>
        exact BinaryNullableDerives.terminal h
    | binary h _ _ ihB ihC =>
        exact BinaryNullableDerives.binary h ihB ihC
  · intro d
    induction d with
    | terminal h =>
        exact UntypedDerives.terminal h
    | epsilon h =>
        exact False.elim h
    | unit h _ ih =>
        exact False.elim h
    | binary h _ _ ihB ihC =>
        exact UntypedDerives.binary h ihB ihC

/--
The learner-style separate start semantics is exactly the explicit fresh-start
grammar from Appendix A.
-/
theorem reducedSSBNF_untypedStartDerives_iff_separated
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G)
    (keepEmpty : Prop)
    (w : Word α) :
    UntypedStartDerives
        (reducedSSBNFTerminalRule G start)
        (reducedSSBNFBinaryRule G start)
        (reducedSSBNFStartRule G start)
        keepEmpty
        w
      ↔
    BinaryNullableDerives
      (separatedStartGrammar G start keepEmpty)
      none w := by
  constructor
  · intro d
    cases d with
    | @nonempty A _ hstart hder =>
        have hA :
            A = reducedUnitFreeStart G start :=
          hstart
        subst A
        have hred :
            BinaryNullableDerives
              (reducedUnitFreeGrammar G start)
              (reducedUnitFreeStart G start)
              w :=
          (reducedSSBNF_untypedDerives_iff
            G start (reducedUnitFreeStart G start) w).1 hder
        exact
          reducedStartDerives_to_separatedStart
            G start keepEmpty hred
    | epsilon heps =>
        exact separatedStart_derives_empty G start heps
  · intro d
    have hshape :=
      separatedStart_derivation_shape
        G start keepEmpty d
    rcases hshape with hnil | hred
    · rcases hnil with ⟨rfl, heps⟩
      exact UntypedStartDerives.epsilon heps
    · exact
        UntypedStartDerives.nonempty
          (show
            reducedSSBNFStartRule G start
              (reducedUnitFreeStart G start) from rfl)
          ((reducedSSBNF_untypedDerives_iff
            G start (reducedUnitFreeStart G start) w).2 hred)

/-- Set-valued form of the separated-start semantic equivalence. -/
theorem reducedSSBNF_untypedStartLanguage_eq_separated
    (G : BinaryNullableGrammar N α)
    (start : ProductiveUnitFreeState G)
    (keepEmpty : Prop) :
    UntypedStartLanguage
        (reducedSSBNFTerminalRule G start)
        (reducedSSBNFBinaryRule G start)
        (reducedSSBNFStartRule G start)
        keepEmpty
      =
    {w |
      BinaryNullableDerives
        (separatedStartGrammar G start keepEmpty)
        none w} := by
  apply Set.ext
  intro w
  exact
    reducedSSBNF_untypedStartDerives_iff_separated
      G start keepEmpty w

end SeparatedStartUntypedBridge

end TCS1
end LeanCfgProject
