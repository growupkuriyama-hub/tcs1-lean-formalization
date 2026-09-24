import LeanCfgProject.TCS1.ReconstructionFiniteStateSupport
import LeanCfgProject.TCS1.BinaryEpsilonElimination

/-!
# TCS #1 v79: finite active grammar for the reconstruction hypothesis

The set-driven learner's non-start semantics `HypDerives` is now presented
as an ordinary finite binary/terminal/unit grammar over the genuinely finite
type of observed reconstruction symbols.

Rules are exactly the paper's R1--R4:

* R4 is a terminal rule when the stored factor is one letter;
* R2 is a unit edge between two observed occurrences of the same factor;
* R3 is a unit edge between two observed factors in the same context with the
  same fixed-h type;
* R1 is the binary factor split with the two induced child contexts.

There are no non-start epsilon rules.  The main theorem below proves exact
equivalence with `HypDerives` in both directions.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section ReconstructionActiveGrammar

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]

/-- Finite binary/terminal/unit grammar underlying one reconstructed hypothesis. -/
def reconstructionActiveGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α)) :
    BinaryNullableGrammar
      (ActiveReconstructionNonterminal K) α where
  terminalRule A a :=
    A.1.factor = [a]
  binaryRule A B C :=
    A.1.factor = B.1.factor ++ C.1.factor ∧
    B.1.leftContext = A.1.leftContext ∧
    B.1.rightContext =
      C.1.factor ++ A.1.rightContext ∧
    C.1.leftContext =
      A.1.leftContext ++ B.1.factor ∧
    C.1.rightContext = A.1.rightContext
  epsilonRule _ := False
  unitRule A B :=
    A.1.factor = B.1.factor ∨
      (A.1.leftContext = B.1.leftContext ∧
       A.1.rightContext = B.1.rightContext ∧
       H.h A.1.factor = H.h B.1.factor)

/-- Every `HypDerives` root is an observed reconstruction symbol. -/
theorem hypDerives_root_observed
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    Observed K x u v := by
  cases d with
  | r4 hobs => exact hobs
  | r3 hobs _ _ _ => exact hobs
  | r2 hobs _ _ => exact hobs
  | r1 hparent _ _ _ _ => exact hparent

/--
Forward representation theorem: every reconstruction derivation is literally
a derivation of the finite active binary/unit grammar.
-/
theorem hypDerives_to_activeGrammar
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {x u v w : Word α}
    (d : HypDerives H K x u v w) :
    BinaryNullableDerives
      (reconstructionActiveGrammar H K)
      ⟨⟨x, u, v⟩, hypDerives_root_observed H K d⟩
      w := by
  induction d with
  | @r4 a u v hobs =>
      exact
        BinaryNullableDerives.terminal
          (G := reconstructionActiveGrammar H K)
          rfl
  | @r3 x x' u v w hobs hobs' htype d ih =>
      have hunit :
          (reconstructionActiveGrammar H K).unitRule
            ⟨⟨x, u, v⟩, hobs⟩
            ⟨⟨x', u, v⟩, hobs'⟩ := by
        exact Or.inr ⟨rfl, rfl, htype⟩
      exact
        BinaryNullableDerives.unit hunit ih
  | @r2 x u v u' v' w hobs hobs' d ih =>
      have hunit :
          (reconstructionActiveGrammar H K).unitRule
            ⟨⟨x, u, v⟩, hobs⟩
            ⟨⟨x, u', v'⟩, hobs'⟩ := by
        exact Or.inl rfl
      exact
        BinaryNullableDerives.unit hunit ih
  | @r1 x y u v w₁ w₂ hparent hleft hright dleft dright ihleft ihrigh =>
      have hbin :
          (reconstructionActiveGrammar H K).binaryRule
            ⟨⟨x ++ y, u, v⟩, hparent⟩
            ⟨⟨x, u, y ++ v⟩, hleft⟩
            ⟨⟨y, u ++ x, v⟩, hright⟩ := by
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      exact
        BinaryNullableDerives.binary
          hbin ihleft ihrigh

/--
Reverse representation theorem: the finite active grammar has no derivations
beyond R1--R4.
-/
theorem activeGrammar_to_hypDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    {A : ActiveReconstructionNonterminal K}
    {w : Word α}
    (d :
      BinaryNullableDerives
        (reconstructionActiveGrammar H K)
        A w) :
    HypDerives H K
      A.1.factor A.1.leftContext A.1.rightContext w := by
  induction d with
  | @terminal A a hterm =>
      rcases A with ⟨⟨x, u, v⟩, hobs⟩
      change x = [a] at hterm
      subst x
      exact HypDerives.r4 hobs
  | @epsilon A heps =>
      exact False.elim heps
  | @unit A B w hunit d ih =>
      rcases A with ⟨⟨x, u, v⟩, hobsA⟩
      rcases B with ⟨⟨x', u', v'⟩, hobsB⟩
      change
        x = x' ∨
          (u = u' ∧ v = v' ∧ H.h x = H.h x')
        at hunit
      rcases hunit with hsame | htyped
      · subst x'
        exact
          HypDerives.r2
            hobsA hobsB ih
      · rcases htyped with ⟨hu, hv, ht⟩
        subst u'
        subst v'
        exact
          HypDerives.r3
            hobsA hobsB ht ih
  | @binary A B C wB wC hbin dB dC ihB ihC =>
      rcases A with ⟨⟨xA, uA, vA⟩, hobsA⟩
      rcases B with ⟨⟨xB, uB, vB⟩, hobsB⟩
      rcases C with ⟨⟨xC, uC, vC⟩, hobsC⟩
      change
        xA = xB ++ xC ∧
        uB = uA ∧
        vB = xC ++ vA ∧
        uC = uA ++ xB ∧
        vC = vA
        at hbin
      rcases hbin with
        ⟨hxA, huB, hvB, huC, hvC⟩
      have hparent :
          Observed K (xB ++ xC) uA vA := by
        simpa [hxA] using hobsA
      have hleft :
          Observed K xB uA (xC ++ vA) := by
        simpa [huB, hvB] using hobsB
      have hright :
          Observed K xC (uA ++ xB) vA := by
        simpa [huC, hvC] using hobsC
      have ihB' :
          HypDerives H K xB uA (xC ++ vA) wB := by
        simpa [huB, hvB] using ihB
      have ihC' :
          HypDerives H K xC (uA ++ xB) vA wC := by
        simpa [huC, hvC] using ihC
      have h :=
        HypDerives.r1
          (H := H) (K := K)
          hparent hleft hright ihB' ihC'
      simpa [hxA] using h

/-- Exact non-start semantic equivalence for the finite reconstruction grammar. -/
theorem activeGrammar_iff_hypDerives
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (A : ActiveReconstructionNonterminal K)
    (w : Word α) :
    BinaryNullableDerives
        (reconstructionActiveGrammar H K)
        A w
      ↔
    HypDerives H K
      A.1.factor A.1.leftContext A.1.rightContext w := by
  constructor
  · exact activeGrammar_to_hypDerives H K
  · intro d
    have hd :=
      hypDerives_to_activeGrammar H K d
    have hstate :
        (⟨⟨A.1.factor, A.1.leftContext, A.1.rightContext⟩,
          hypDerives_root_observed H K d⟩ :
          ActiveReconstructionNonterminal K) = A := by
      apply Subtype.ext
      cases A with
      | mk q hq =>
          cases q
          rfl
    simpa [hstate] using hd

end ReconstructionActiveGrammar

end TCS1
end LeanCfgProject
