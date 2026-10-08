import LeanCfgProject.TCS1.V128SubstringQuotient
import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1 v128: substring reconstruction as an ordinary binary CFG

The v116 non-start grammar rules (B), (U), and (L) are presented as the
terminal/binary/unit rules of a `BinaryNullableGrammar` with word-indexed
nonterminals. They are extensionally equivalent to `SubstringDerives`.

The word-indexed carrier is not finite as a type. The productions' active
states are nevertheless guarded by occurrence witnesses from finite K.
A separate finite-support/finite-encoding presentation is still needed for
a machine-checked grammar-size bound.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section SubstringCFG

variable {α : Type u} {M : Type v}
variable [Monoid M] [Fintype M]

/-- Binary/terminal/unit CFG implementing v116 non-start rules. -/
def substringReconstructionGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    BinaryNullableGrammar (Word α) α where
  terminalRule x a :=
    x = [a] ∧ ∃ p q : Word α, Observed K [a] p q
  binaryRule x y z :=
    x = y ++ z ∧ y ≠ [] ∧ z ≠ [] ∧
      ∃ p q : Word α, Observed K x p q
  epsilonRule _ := False
  unitRule x y := SubstringUnaryRelated H K x y

/-- Every v116 non-start derivation is a derivation in its CFG presentation. -/
theorem substringDerives_to_CFG
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : SubstringDerives H K x w) :
    BinaryNullableDerives (substringReconstructionGrammar H K) x w := by
  induction d with
  | letter hobs =>
      exact BinaryNullableDerives.terminal ⟨rfl, hobs⟩
  | unary hrel _d ih =>
      exact BinaryNullableDerives.unit hrel ih
  | binary hparent hx hy _dx _dy ihx ihy =>
      exact BinaryNullableDerives.binary
        ⟨rfl, hx, hy, hparent⟩ ihx ihy

/-- Every CFG derivation uses exactly the permitted v116 non-start rules. -/
theorem CFG_to_substringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x w : Word α}
    (d : BinaryNullableDerives (substringReconstructionGrammar H K) x w) :
    SubstringDerives H K x w := by
  induction d with
  | terminal h =>
      rcases h with ⟨rfl, hobs⟩
      exact SubstringDerives.letter hobs
  | epsilon h =>
      exact False.elim h
  | unit h _d ih =>
      exact SubstringDerives.unary h ih
  | binary h _dx _dy ihx ihy =>
      rcases h with ⟨rfl, hx, hy, hparent⟩
      exact SubstringDerives.binary hparent hx hy ihx ihy

/-- Exact semantic equivalence between v116 inductive rules and their CFG. -/
theorem substringCFG_iff_substringDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (x w : Word α) :
    BinaryNullableDerives (substringReconstructionGrammar H K) x w ↔
      SubstringDerives H K x w := by
  constructor
  · exact CFG_to_substringDerives H K
  · exact substringDerives_to_CFG H K

end SubstringCFG

end TCS1
end LeanCfgProject
