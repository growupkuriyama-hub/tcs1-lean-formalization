import LeanCfgProject.TCS1.V115FiniteInformationClosure
import LeanCfgProject.TCS1.ConcreteTypedTrimLanguage

/-!
# TCS #1 v115: finite product-grammar construction for regular filtering

Proposition 3.2(ii), the representation-level closure step:
an SSBNF grammar filtered by a finite deterministic automaton has an
explicit SSBNF grammar, using triples (A,p,q) for non-start states.
A terminal rule records one automaton transition; a binary rule
concatenates two composable paths.

We prove both inclusions of the exact derived language, then specialize
the automaton to right multiplication by the recognizing finite monoid.
No generic CFL intersection closure theorem is assumed.

This directly discharges regular filtering for start-separated SSBNF,
the concrete normal form used elsewhere in the TCS #1 development.
The full arbitrary-source-CFG formulation additionally uses the
already separately verified language-preserving normalization.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section V115SSBNFRegularFilter

variable {α : Type u}
variable {N : Type v} {Q : Type w}

/-- Deterministic reading of a finite-state transition function. -/
def v115AutomatonRead (δ : Q → α → Q) :
    Q → Word α → Q
  | q, [] => q
  | q, letter :: rest =>
      v115AutomatonRead δ (δ q letter) rest

@[simp] theorem v115AutomatonRead_nil
    (δ : Q → α → Q) (q : Q) :
    v115AutomatonRead δ q [] = q := rfl

theorem v115AutomatonRead_append
    (δ : Q → α → Q)
    (q : Q)
    (u v : Word α) :
    v115AutomatonRead δ q (u ++ v) =
      v115AutomatonRead δ
        (v115AutomatonRead δ q u) v := by
  induction u generalizing q with
  | nil => rfl
  | cons letter rest ih =>
      exact ih (δ q letter)

/-- A filtered nonterminal remembers initial and final automaton states. -/
abbrev V115FilterState (N Q : Type*) := N × Q × Q

/-- A terminal is usable exactly when it advances p to q. -/
def v115FilterTerminal
    (δ : Q → α → Q)
    (terminalRule : N → α → Prop) :
    V115FilterState N Q → α → Prop :=
  fun X letter =>
    terminalRule X.1 letter ∧
      δ X.2.1 letter = X.2.2

/-- A binary rule composes a path p-to-r with a path r-to-q. -/
def v115FilterBinary
    (binaryRule : N → N → N → Prop) :
    V115FilterState N Q →
    V115FilterState N Q →
    V115FilterState N Q → Prop :=
  fun A B C =>
    binaryRule A.1 B.1 C.1 ∧
      A.2.1 = B.2.1 ∧
      B.2.2 = C.2.1 ∧
      C.2.2 = A.2.2

/-- Start rules accept only paths from the initial state into Acc. -/
def v115FilterStart
    (startRule : N → Prop)
    (q₀ : Q)
    (accept : Q → Prop) :
    V115FilterState N Q → Prop :=
  fun X =>
    startRule X.1 ∧ X.2.1 = q₀ ∧ accept X.2.2

/-- Every product-grammar derivation erases to the original derivation,
    and its boundary states describe the recognized yield. -/
theorem v115FilterDerives_sound
    (δ : Q → α → Q)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {X : V115FilterState N Q}
    {word : Word α}
    (d : UntypedDerives
      (v115FilterTerminal δ terminalRule)
      (v115FilterBinary binaryRule)
      X word) :
    UntypedDerives
      terminalRule binaryRule X.1 word ∧
      v115AutomatonRead δ X.2.1 word = X.2.2 := by
  induction d with
  | @terminal X letter h =>
      exact ⟨UntypedDerives.terminal h.1, h.2⟩
  | @binary A B C wB wC h _ _ ihB ihC =>
      rcases h with ⟨hb, hleft, hmiddle, hright⟩
      rcases ihB with ⟨db, eqB⟩
      rcases ihC with ⟨dc, eqC⟩
      constructor
      · exact UntypedDerives.binary hb db dc
      · calc
          v115AutomatonRead δ A.2.1 (wB ++ wC) =
              v115AutomatonRead δ
                (v115AutomatonRead δ A.2.1 wB) wC :=
            v115AutomatonRead_append δ A.2.1 wB wC
          _ = v115AutomatonRead δ
                (v115AutomatonRead δ B.2.1 wB) wC := by
            rw [hleft]
          _ = v115AutomatonRead δ B.2.2 wC := by
            rw [eqB]
          _ = v115AutomatonRead δ C.2.1 wC := by
            rw [hmiddle]
          _ = C.2.2 := eqC
          _ = A.2.2 := hright

/-- Every original derivation lifts to the product grammar with its
    uniquely determined output automaton state. -/
theorem v115FilterDerives_complete
    (δ : Q → α → Q)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    {A : N} {word : Word α}
    (d : UntypedDerives terminalRule binaryRule A word)
    (q : Q) :
    UntypedDerives
      (v115FilterTerminal δ terminalRule)
      (v115FilterBinary binaryRule)
      (A, q, v115AutomatonRead δ q word)
      word := by
  induction d generalizing q with
  | terminal h =>
      exact UntypedDerives.terminal ⟨h, rfl⟩
  | @binary A B C wB wC hr _ _ ihB ihC =>
      rw [v115AutomatonRead_append]
      exact
        UntypedDerives.binary
          ⟨hr, rfl, rfl, rfl⟩
          (ihB q)
          (ihC (v115AutomatonRead δ q wB))

/--
Exact regular intersection, including the epsilon-start case.
The construction is a genuine finite-NT grammar whenever N and Q are
finite, since its NT type is N x Q x Q.
-/
theorem v115FilterStartLanguage_eq_inter
    (δ : Q → α → Q)
    (q₀ : Q)
    (accept : Q → Prop)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    UntypedStartLanguage
      (v115FilterTerminal δ terminalRule)
      (v115FilterBinary binaryRule)
      (v115FilterStart startRule q₀ accept)
      (epsilonStart ∧ accept q₀)
      =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart
      ∩ {word : Word α |
          accept (v115AutomatonRead δ q₀ word)} := by
  apply Set.ext
  intro word
  constructor
  · intro d
    cases d with
    | @nonempty X word hstart dX =>
        rcases hstart with ⟨hs, hinit, hacc⟩
        obtain ⟨dOld, hread⟩ :=
          v115FilterDerives_sound
            δ terminalRule binaryRule dX
        have hfinal :
            v115AutomatonRead δ q₀ word = X.2.2 := by
          rw [← hinit]
          exact hread
        exact
          ⟨UntypedStartDerives.nonempty hs dOld,
            by rw [hfinal]; exact hacc⟩
    | epsilon heps =>
        exact
          ⟨UntypedStartDerives.epsilon heps.1,
            by simpa only [v115AutomatonRead_nil] using heps.2⟩
  · rintro ⟨d, hacc⟩
    cases d with
    | @nonempty A word hs dA =>
        exact
          UntypedStartDerives.nonempty
            ⟨hs, rfl, hacc⟩
            (v115FilterDerives_complete
              δ terminalRule binaryRule dA q₀)
    | epsilon heps =>
        exact
          UntypedStartDerives.epsilon
            ⟨heps,
              by simpa only [v115AutomatonRead_nil] using hacc⟩

end V115SSBNFRegularFilter

section V115MonoidRecognizedFilter

variable {α : Type u}
variable {N : Type v} {M : Type z}
variable [Monoid M] [Fintype M]

/-- The recognizing homomorphism gives a deterministic finite automaton. -/
def v115MonoidTransition
    (G : FixedFiniteMonoidHom α M) :
    M → α → M :=
  fun m letter => m * G.h [letter]

/-- Running that DFA from state m multiplies by the homomorphic image. -/
theorem v115MonoidRead
    (G : FixedFiniteMonoidHom α M)
    (m : M)
    (word : Word α) :
    v115AutomatonRead
      (v115MonoidTransition G)
      m word = m * G.h word := by
  induction word generalizing m with
  | nil =>
      simp only [v115AutomatonRead_nil, G.map_nil, mul_one]
  | cons letter rest ih =>
      calc
        v115AutomatonRead
            (v115MonoidTransition G)
            m (letter :: rest) =
          v115AutomatonRead
            (v115MonoidTransition G)
            (m * G.h [letter]) rest := rfl
        _ = (m * G.h [letter]) * G.h rest :=
          ih _
        _ = m * G.h ([letter] ++ rest) := by
          rw [G.map_append]
          simp only [mul_assoc]
        _ = m * G.h (letter :: rest) := rfl

/-- The constructed SSBNF grammar is exactly L intersect g^{-1}(Acc). -/
theorem v115MonoidFilteredSSBNF_language
    (G : FixedFiniteMonoidHom α M)
    (Acc : Set M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop) :
    UntypedStartLanguage
      (v115FilterTerminal (v115MonoidTransition G) terminalRule)
      (v115FilterBinary binaryRule)
      (v115FilterStart startRule 1 (fun m => m ∈ Acc))
      (epsilonStart ∧ (1 : M) ∈ Acc) =
    UntypedStartLanguage
      terminalRule binaryRule startRule epsilonStart ∩
    RecognizedPreimage G Acc := by
  calc
    UntypedStartLanguage
        (v115FilterTerminal (v115MonoidTransition G) terminalRule)
        (v115FilterBinary binaryRule)
        (v115FilterStart startRule 1 (fun m => m ∈ Acc))
        (epsilonStart ∧ (1 : M) ∈ Acc) =
      UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart ∩
        {word : Word α |
          v115AutomatonRead
            (v115MonoidTransition G)
            (1 : M) word ∈ Acc} :=
      v115FilterStartLanguage_eq_inter
        (v115MonoidTransition G) 1
        (fun m => m ∈ Acc)
        terminalRule binaryRule startRule epsilonStart
    _ = UntypedStartLanguage
        terminalRule binaryRule startRule epsilonStart ∩
        RecognizedPreimage G Acc := by
      apply Set.ext
      intro word
      change
        ((UntypedStartDerives
          terminalRule binaryRule startRule epsilonStart word) ∧
          v115AutomatonRead (v115MonoidTransition G) 1 word ∈ Acc)
          ↔
        ((UntypedStartDerives
          terminalRule binaryRule startRule epsilonStart word) ∧
          G.h word ∈ Acc)
      rw [v115MonoidRead]
      simp

end V115MonoidRecognizedFilter

section V115SSBNFRegularFilteringTyped

variable {α : Type u}
variable {N : Type v} {M : Type w} {F : Type z}
variable [Monoid M] [Fintype M]
variable [Monoid F] [Fintype F]

/--
The grammar constructed above witnesses both aspects of Prop. 3.2(ii)
at SSBNF level: exact regular-filtered CFL semantics and substitutability
for the product typing. Neither implication is an assumption.
-/
theorem v115_ssbnf_regular_filter_fixedH
    (H : FixedFiniteMonoidHom α M)
    (G : FixedFiniteMonoidHom α F)
    (Acc : Set F)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (hsub :
      FixedHSubstitutable H
        (UntypedStartLanguage
          terminalRule binaryRule startRule epsilonStart)) :
    FixedHSubstitutable
      (productFixedFiniteMonoidHom H G)
      (UntypedStartLanguage
        (v115FilterTerminal (v115MonoidTransition G) terminalRule)
        (v115FilterBinary binaryRule)
        (v115FilterStart startRule 1 (fun m => m ∈ Acc))
        (epsilonStart ∧ (1 : F) ∈ Acc)) := by
  rw [v115MonoidFilteredSSBNF_language]
  exact
    fixedHSubstitutable_inter_recognized_product
      H G Acc hsub

end V115SSBNFRegularFilteringTyped

end TCS1
end LeanCfgProject
