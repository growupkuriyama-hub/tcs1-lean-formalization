import Mathlib.Computability.DFA
import LeanCfgProject.TCS1.LinearRawEpsilonUnitSemantics

/-!
# TCS #1 v78: linear grammars and intersection with a DFA language

The nonlinear Delta-star example uses the standard closure fact that linear
languages are closed under intersection with regular languages.  Rather than
leave that closure step entirely external, this module proves the part needed
for the manuscript directly for the repository's raw indexed linear-grammar
semantics.

Given a raw linear grammar G and a DFA D, the product nonterminal

  <A,p,q>

means: A derives a terminal word taking D from p to q.

Every source production remains linear:

* epsilon keeps p=q;
* A -> B keeps the same entry/exit pair;
* A -> w sends p to D.evalFrom p w;
* A -> u B v threads the DFA through u, the unique child B, and v.

The resulting grammar generates exactly the intersection with the DFA
language.  This removes the regular-intersection closure theorem from the
external dependency boundary of the Delta-star non-linearity argument.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w x

section LinearRegularIntersection

variable {N : Type u}
variable {α : Type v}
variable {P : Type w}
variable {Q : Type x}

/-- Product nonterminal: source nonterminal plus DFA entry/exit states. -/
structure RawDFAProductState (N : Type u) (Q : Type x) where
  source : N
  entry : Q
  exit : Q
  deriving Repr

/-- Product production index: source production plus two threading states. -/
structure RawDFAProductProd (P : Type w) (Q : Type x) where
  sourceProd : P
  entry : Q
  middle : Q
  deriving Repr

instance [Fintype N] [Fintype Q] :
    Fintype (RawDFAProductState N Q) :=
  Fintype.ofEquiv (N × Q × Q)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun x => (x.source, x.entry, x.exit)
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }

instance [Fintype P] [Fintype Q] :
    Fintype (RawDFAProductProd P Q) :=
  Fintype.ofEquiv (P × Q × Q)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩
      invFun := fun x => (x.sourceProd, x.entry, x.middle)
      left_inv := by intro x; cases x; rfl
      right_inv := by intro x; cases x; rfl }

/--
Raw product grammar.  The second state stored in a product production is
ignored for epsilon and terminal-only rules; harmless duplicate productions
keep the production type uniformly finite.
-/
def rawDFAProductGrammar
    (G : RawLinearIndexedCFG N α P)
    (D : DFA α Q) :
    RawLinearIndexedCFG
      (RawDFAProductState N Q)
      α
      (RawDFAProductProd P Q) where
  lhs i :=
    match G.rhs i.sourceProd with
    | .epsilon =>
        ⟨G.lhs i.sourceProd,
          i.entry, i.entry⟩
    | .unit _ =>
        ⟨G.lhs i.sourceProd,
          i.entry, i.middle⟩
    | .prepared (.terminals head tail) =>
        ⟨G.lhs i.sourceProd,
          i.entry,
          D.evalFrom i.entry (head :: tail)⟩
    | .prepared (.around left _ right _) =>
        ⟨G.lhs i.sourceProd,
          i.entry,
          D.evalFrom i.middle right⟩
  rhs i :=
    match G.rhs i.sourceProd with
    | .epsilon =>
        .epsilon
    | .unit B =>
        .unit
          ⟨B, i.entry, i.middle⟩
    | .prepared (.terminals head tail) =>
        .prepared
          (.terminals head tail)
    | .prepared (.around left core right hnonunit) =>
        .prepared
          (.around left
            ⟨core,
              D.evalFrom i.entry left,
              i.middle⟩
            right hnonunit)

/--
Soundness of the DFA product: every product derivation projects to a source
derivation, and its entry/exit annotations are the exact DFA transition.
-/
theorem rawDFAProductDerives_sound
    (G : RawLinearIndexedCFG N α P)
    (D : DFA α Q)
    {X : RawDFAProductState N Q}
    {word : Word α}
    (d :
      RawLinearDerives
        (rawDFAProductGrammar G D) X word) :
    RawLinearDerives G X.source word
      ∧
    D.evalFrom X.entry word = X.exit := by
  induction d with
  | epsilon i hrhs =>
      cases hsrc : G.rhs i.sourceProd with
      | epsilon =>
          constructor
          · simpa [rawDFAProductGrammar, hsrc] using
              (RawLinearDerives.epsilon
                (G := G) i.sourceProd hsrc)
          · simp [rawDFAProductGrammar, hsrc]
      | unit B =>
          simp [rawDFAProductGrammar, hsrc] at hrhs
      | prepared rhs =>
          cases rhs with
          | terminals head tail =>
              simp [rawDFAProductGrammar, hsrc] at hrhs
          | around left core right hnonunit =>
              simp [rawDFAProductGrammar, hsrc] at hrhs
  | @unit i B hrhs word child ih =>
      cases hsrc : G.rhs i.sourceProd with
      | epsilon =>
          simp [rawDFAProductGrammar, hsrc] at hrhs
      | unit core =>
          have hB :
              ⟨core, i.entry, i.middle⟩ = B := by
            simpa [rawDFAProductGrammar, hsrc] using hrhs
          subst B
          constructor
          · simpa [rawDFAProductGrammar, hsrc] using
              (RawLinearDerives.unit
                (G := G)
                i.sourceProd core hsrc ih.1)
          · simpa [rawDFAProductGrammar, hsrc] using ih.2
      | prepared rhs =>
          cases rhs with
          | terminals head tail =>
              simp [rawDFAProductGrammar, hsrc] at hrhs
          | around left core right hnonunit =>
              simp [rawDFAProductGrammar, hsrc] at hrhs
  | terminals i head tail hrhs =>
      cases hsrc : G.rhs i.sourceProd with
      | epsilon =>
          simp [rawDFAProductGrammar, hsrc] at hrhs
      | unit B =>
          simp [rawDFAProductGrammar, hsrc] at hrhs
      | prepared rhs =>
          cases rhs with
          | terminals srcHead srcTail =>
              have hEq :
                  srcHead = head ∧
                  srcTail = tail := by
                simpa [rawDFAProductGrammar, hsrc] using hrhs
              rcases hEq with ⟨rfl, rfl⟩
              constructor
              · simpa [rawDFAProductGrammar, hsrc] using
                  (RawLinearDerives.terminals
                    (G := G)
                    i.sourceProd srcHead srcTail hsrc)
              · simp [rawDFAProductGrammar, hsrc]
          | around left core right hnonunit =>
              simp [rawDFAProductGrammar, hsrc] at hrhs
  | @around i left core right hnonunit hrhs word child ih =>
      cases hsrc : G.rhs i.sourceProd with
      | epsilon =>
          simp [rawDFAProductGrammar, hsrc] at hrhs
      | unit B =>
          simp [rawDFAProductGrammar, hsrc] at hrhs
      | prepared rhs =>
          cases rhs with
          | terminals head tail =>
              simp [rawDFAProductGrammar, hsrc] at hrhs
          | around srcLeft srcCore srcRight srcNonunit =>
              have hparts :
                  srcLeft = left ∧
                  ⟨srcCore,
                    D.evalFrom i.entry srcLeft,
                    i.middle⟩ = core ∧
                  srcRight = right := by
                simpa [rawDFAProductGrammar, hsrc] using hrhs
              rcases hparts with
                ⟨rfl, rfl, rfl⟩
              constructor
              · simpa [rawDFAProductGrammar, hsrc] using
                  (RawLinearDerives.around
                    (G := G)
                    i.sourceProd
                    srcLeft srcCore srcRight
                    srcNonunit hsrc ih.1)
              · have htrans :
                    D.evalFrom i.entry
                        (srcLeft ++ word ++ srcRight) =
                      D.evalFrom i.middle srcRight := by
                  calc
                    D.evalFrom i.entry
                        (srcLeft ++ word ++ srcRight)
                      =
                    D.evalFrom
                        (D.evalFrom i.entry
                          (srcLeft ++ word))
                        srcRight := by
                          rw [DFA.evalFrom_of_append]
                    _ =
                    D.evalFrom
                        (D.evalFrom
                          (D.evalFrom i.entry srcLeft)
                          word)
                        srcRight := by
                          rw [DFA.evalFrom_of_append]
                    _ =
                    D.evalFrom i.middle srcRight := by
                          rw [ih.2]
                simpa [rawDFAProductGrammar, hsrc] using htrans

/--
Completeness of the DFA product: every source derivation lifts from an
arbitrary DFA entry state to the uniquely determined exit state.
-/
theorem rawDFAProductDerives_complete
    (G : RawLinearIndexedCFG N α P)
    (D : DFA α Q)
    {A : N}
    {word : Word α}
    (d : RawLinearDerives G A word)
    (q : Q) :
    RawLinearDerives
      (rawDFAProductGrammar G D)
      ⟨A, q, D.evalFrom q word⟩
      word := by
  induction d generalizing q with
  | epsilon p hrhs =>
      let i : RawDFAProductProd P Q :=
        ⟨p, q, q⟩
      have h :
          (rawDFAProductGrammar G D).rhs i =
            RawLinearRhs.epsilon := by
        simp [rawDFAProductGrammar, i, hrhs]
      have d' :=
        RawLinearDerives.epsilon
          (G := rawDFAProductGrammar G D)
          i h
      simpa [rawDFAProductGrammar, i, hrhs] using d'
  | @unit p B hrhs word child ih =>
      let r := D.evalFrom q word
      let i : RawDFAProductProd P Q :=
        ⟨p, q, r⟩
      have h :
          (rawDFAProductGrammar G D).rhs i =
            RawLinearRhs.unit
              ⟨B, q, r⟩ := by
        simp [rawDFAProductGrammar, i, hrhs, r]
      have d' :=
        RawLinearDerives.unit
          (G := rawDFAProductGrammar G D)
          i
          ⟨B, q, r⟩
          h
          (ih q)
      simpa [rawDFAProductGrammar, i, hrhs, r] using d'
  | terminals p head tail hrhs =>
      let i : RawDFAProductProd P Q :=
        ⟨p, q, q⟩
      have h :
          (rawDFAProductGrammar G D).rhs i =
            RawLinearRhs.prepared
              (PreparedLinearRhs.terminals
                head tail) := by
        simp [rawDFAProductGrammar, i, hrhs]
      have d' :=
        RawLinearDerives.terminals
          (G := rawDFAProductGrammar G D)
          i head tail h
      simpa [rawDFAProductGrammar, i, hrhs] using d'
  | @around p left core right hnonunit hrhs word child ih =>
      let qLeft := D.evalFrom q left
      let qMiddle := D.evalFrom qLeft word
      let i : RawDFAProductProd P Q :=
        ⟨p, q, qMiddle⟩
      have h :
          (rawDFAProductGrammar G D).rhs i =
            RawLinearRhs.prepared
              (PreparedLinearRhs.around
                left
                ⟨core, qLeft, qMiddle⟩
                right hnonunit) := by
        simp [rawDFAProductGrammar, i,
          hrhs, qLeft, qMiddle]
      have child' :
          RawLinearDerives
            (rawDFAProductGrammar G D)
            ⟨core, qLeft, qMiddle⟩
            word := by
        simpa [qMiddle] using
          (ih qLeft)
      have d' :=
        RawLinearDerives.around
          (G := rawDFAProductGrammar G D)
          i left
          ⟨core, qLeft, qMiddle⟩
          right hnonunit h child'
      have hEval :
          D.evalFrom q
              (left ++ word ++ right) =
            D.evalFrom qMiddle right := by
        calc
          D.evalFrom q
              (left ++ word ++ right)
            =
          D.evalFrom
              (D.evalFrom q (left ++ word))
              right := by
                rw [DFA.evalFrom_of_append]
          _ =
          D.evalFrom
              (D.evalFrom
                (D.evalFrom q left) word)
              right := by
                rw [DFA.evalFrom_of_append]
          _ =
          D.evalFrom qMiddle right := by
                rfl
      rw [hEval]
      simpa [rawDFAProductGrammar, i,
        hrhs, qLeft, qMiddle] using d'

/-- Language generated from a finite set of raw-linear initial states. -/
def RawLinearInitialLanguage
    (G : RawLinearIndexedCFG N α P)
    (I : Set N) :
    Set (Word α) :=
  {word |
    ∃ A : N,
      A ∈ I ∧
      RawLinearDerives G A word}

/-- Product initial states: source initial, DFA start, DFA accepting exit. -/
def rawDFAProductInitial
    (D : DFA α Q)
    (I : Set N) :
    Set (RawDFAProductState N Q) :=
  {X |
    X.source ∈ I ∧
    X.entry = D.start ∧
    X.exit ∈ D.accept}

/-- The product initial-set language is exactly source language intersect DFA language. -/
theorem rawDFAProductInitialLanguage_eq
    (G : RawLinearIndexedCFG N α P)
    (D : DFA α Q)
    (I : Set N) :
    RawLinearInitialLanguage
        (rawDFAProductGrammar G D)
        (rawDFAProductInitial D I)
      =
    RawLinearInitialLanguage G I ∩
      D.accepts := by
  apply Set.ext
  intro word
  constructor
  · rintro ⟨X, hX, dX⟩
    rcases hX with
      ⟨hI, hstart, haccept⟩
    have hs :=
      rawDFAProductDerives_sound
        G D dX
    constructor
    · exact ⟨X.source, hI, hs.1⟩
    · change
        D.eval word ∈ D.accept
      change
        D.evalFrom D.start word ∈
          D.accept
      rw [← hstart, hs.2]
      exact haccept
  · rintro ⟨⟨A, hI, dA⟩, hacc⟩
    let X : RawDFAProductState N Q :=
      ⟨A, D.start,
        D.evalFrom D.start word⟩
    refine ⟨X, ?_, ?_⟩
    · refine ⟨hI, rfl, ?_⟩
      exact hacc
    · exact
        rawDFAProductDerives_complete
          G D dA D.start

/--
Finite raw-linear initial-set representability.  This is equivalent to the
usual finite linear-CFG notion after adding one fresh start symbol with unit
rules to the finitely many initial states; the present form is convenient for
the DFA product construction.
-/
def RawLinearInitialRepresentable
    {α : Type v}
    (L : Set (Word α)) : Prop :=
  ∃ N : Type u,
    ∃ _fN : Fintype N,
    ∃ P : Type w,
      ∃ _fP : Fintype P,
      ∃ G : RawLinearIndexedCFG N α P,
        ∃ I : Set N,
          I.Finite ∧
          RawLinearInitialLanguage G I = L

/--
A finite indexed linear CFG gives a raw-linear initial-set presentation of its
source language (with the singleton start set).
-/
theorem indexedLinear_to_rawInitialRepresentable
    [Fintype N] [Fintype P]
    (G : IndexedMixedCFG N α P)
    (hlinear : G.IsLinear)
    (S : N) :
    RawLinearInitialRepresentable.{
      u, v, w}
      (LeastClosedLanguage G.toMixedRules S) := by
  let I : Set N := {A | A = S}
  refine
    ⟨N, inferInstance,
      P, inferInstance,
      G.toRawLinear hlinear,
      I, Set.toFinite I, ?_⟩
  apply Set.ext
  intro word
  constructor
  · rintro ⟨A, hA, dA⟩
    have hAS : A = S := hA
    subst A
    have hleast :
        word ∈
          RawLinearLeastLanguage
            (G.toRawLinear hlinear) S :=
      (rawLinearDerives_iff_least
        (G.toRawLinear hlinear)
        S word).1 dA
    simpa [indexedMixedCFG_rawLeast_eq_source
      G hlinear S] using hleast
  · intro hsource
    refine ⟨S, rfl, ?_⟩
    apply
      (rawLinearDerives_iff_least
        (G.toRawLinear hlinear)
        S word).2
    simpa [indexedMixedCFG_rawLeast_eq_source
      G hlinear S] using hsource

/--
Machine-checked regular-intersection closure for finite raw-linear
initial-set presentations.
-/
theorem rawLinearInitialRepresentable_inter_dfa
    [Fintype Q]
    (D : DFA α Q)
    {L : Set (Word α)}
    (hL :
      RawLinearInitialRepresentable.{
        u, v, w} L) :
    RawLinearInitialRepresentable.{
      max u x, v, max w x}
      (L ∩ D.accepts) := by
  rcases hL with
    ⟨N, fN, P, fP, G, I, hIfin, hlang⟩
  letI : Fintype N := fN
  letI : Fintype P := fP
  let PI :=
    rawDFAProductInitial D I
  refine
    ⟨RawDFAProductState N Q,
      inferInstance,
      RawDFAProductProd P Q,
      inferInstance,
      rawDFAProductGrammar G D,
      PI,
      Set.toFinite PI,
      ?_⟩
  rw [rawDFAProductInitialLanguage_eq]
  rw [hlang]

end LinearRegularIntersection

end TCS1
end LeanCfgProject
