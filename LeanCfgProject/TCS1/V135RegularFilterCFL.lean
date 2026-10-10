import LeanCfgProject.TCS1.GeneralCFGDerivationBridge
import LeanCfgProject.TCS1.FiniteCFGEncoding
import LeanCfgProject.TCS1.V128FiniteInformationClosure

/-!
# TCS #1 v135: CFL side of `prop:finite-info-closure` (ii)

Manuscript (v135) `prop:finite-info-closure` (ii):

> If `Q = g⁻¹(F)` is regular and `L ∈ C_h`, then `L ∩ Q ∈ C_{h×g}`.

The manuscript proof combines item (i) (already verified as
`fixedHSubstitutable_regularFilter_product`) with the classical closure of
CFLs under intersection with regular languages.  This module removes that
classical fact from the external trust boundary for the representation used
throughout the formalization (finite indexed CFGs with parse-tree semantics),
for regular sets presented as `g⁻¹(F)` with `g` a finite-monoid typing and
`F` a finite set of accepted types — exactly the form in the proposition.

Construction (standard typed refinement):

* `typedRefinement R g`: nonterminals `(A, m)`; a rule `(A,m) → rhs'` exists
  iff erasing the annotations of `rhs'` gives a source rule of `A` and the
  product of the annotated types (terminals typed by `g`) is `m`.
  Theorem: `(A,m) ⇒* w  ↔  A ⇒* w ∧ g(w) = m`.
* `startUnion`: a fresh start symbol `none` with unit rules
  `none → (S, m)` for `m ∈ F`.
* `regularFilterGrammar`: a finite indexed presentation of the composite
  grammar, with production index `(Σ p, Fin |rhs p| → M_g) ⊕ F`.

Main results: `regularFilterGrammar_language` and
`finiteInfoClosure_ii_cfl`.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w q

section TypedRefinement

variable {N : Type u} {α : Type v}
variable {Mg : Type q} [Monoid Mg] [Fintype Mg]

/-- Type of an annotated symbol: annotated nonterminals carry their type,
terminals are typed by `g`. -/
def annSymbolType (g : FixedFiniteMonoidHom α Mg) :
    MixedSymbol (N × Mg) α → Mg
  | Sum.inl X => X.2
  | Sum.inr a => g.h [a]

/-- Product of the types along an annotated right-hand side. -/
def annRhsType (g : FixedFiniteMonoidHom α Mg)
    (rhs : List (MixedSymbol (N × Mg) α)) : Mg :=
  (rhs.map (annSymbolType g)).prod

/-- Forget the type annotation of a symbol. -/
def eraseSymbol : MixedSymbol (N × Mg) α → MixedSymbol N α
  | Sum.inl X => Sum.inl X.1
  | Sum.inr a => Sum.inr a

theorem annRhsType_nil (g : FixedFiniteMonoidHom α Mg) :
    annRhsType (N := N) g [] = 1 := by
  simp [annRhsType]

theorem annRhsType_cons (g : FixedFiniteMonoidHom α Mg)
    (s : MixedSymbol (N × Mg) α) (rhs : List (MixedSymbol (N × Mg) α)) :
    annRhsType g (s :: rhs) = annSymbolType g s * annRhsType g rhs := by
  simp [annRhsType]

/-- Typed refinement of a predicate grammar. -/
def typedRefinement (R : MixedRules N α) (g : FixedFiniteMonoidHom α Mg) :
    MixedRules (N × Mg) α :=
  fun X rhs' => R X.1 (rhs'.map eraseSymbol) ∧ annRhsType g rhs' = X.2

theorem typedRefinement_iff (R : MixedRules N α)
    (g : FixedFiniteMonoidHom α Mg) (X : N × Mg)
    (rhs' : List (MixedSymbol (N × Mg) α)) :
    typedRefinement R g X rhs' ↔
      R X.1 (rhs'.map eraseSymbol) ∧ annRhsType g rhs' = X.2 :=
  Iff.rfl

/-- Soundness of the typed refinement. -/
theorem typedRefinement_derives_sound (R : MixedRules N α)
    (g : FixedFiniteMonoidHom α Mg)
    {X : N × Mg} {w : List α}
    (d : MixedDerives (typedRefinement R g) X w) :
    MixedDerives R X.1 w ∧ g.h w = X.2 := by
  refine MixedDerives.rec
    (motive_1 := fun X w _ => MixedDerives R X.1 w ∧ g.h w = X.2)
    (motive_2 := fun rhs' pieces _ =>
      MixedSymbolsDerive R (rhs'.map eraseSymbol) pieces ∧
        g.h pieces.flatten = annRhsType g rhs')
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro X rhs' pieces hR _ ih
    have hR' := (typedRefinement_iff R g X rhs').1 hR
    exact ⟨MixedDerives.rule hR'.1 ih.1, ih.2.trans hR'.2⟩
  case nil =>
    refine ⟨MixedSymbolsDerive.nil, ?_⟩
    rw [annRhsType_nil]
    simpa using g.map_nil
  case terminal =>
    intro a rhs' pieces _ ih
    refine ⟨?_, ?_⟩
    · show MixedSymbolsDerive R (Sum.inr a :: rhs'.map eraseSymbol) _
      exact MixedSymbolsDerive.terminal ih.1
    · rw [List.flatten_cons, g.map_append, ih.2, annRhsType_cons]
      rfl
  case nonterminal =>
    intro Y rhs' w pieces _ _ ihA ihT
    refine ⟨?_, ?_⟩
    · show MixedSymbolsDerive R (Sum.inl Y.1 :: rhs'.map eraseSymbol) _
      exact MixedSymbolsDerive.nonterminal ihA.1 ihT.1
    · rw [List.flatten_cons, g.map_append, ihA.2, ihT.2, annRhsType_cons]
      rfl

/-- Completeness of the typed refinement. -/
theorem typedRefinement_derives_complete (R : MixedRules N α)
    (g : FixedFiniteMonoidHom α Mg)
    {A : N} {w : List α}
    (d : MixedDerives R A w) :
    MixedDerives (typedRefinement R g) (A, g.h w) w := by
  refine MixedDerives.rec
    (motive_1 := fun A w _ => MixedDerives (typedRefinement R g) (A, g.h w) w)
    (motive_2 := fun rhs pieces _ =>
      ∃ rhs' : List (MixedSymbol (N × Mg) α),
        rhs'.map eraseSymbol = rhs ∧
        annRhsType g rhs' = g.h pieces.flatten ∧
        MixedSymbolsDerive (typedRefinement R g) rhs' pieces)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR _ ih
    obtain ⟨rhs', herase, htype, hd⟩ := ih
    refine MixedDerives.rule ?_ hd
    rw [typedRefinement_iff]
    exact ⟨by rw [herase]; exact hR, htype⟩
  case nil =>
    refine ⟨[], rfl, ?_, MixedSymbolsDerive.nil⟩
    rw [annRhsType_nil]
    simpa using g.map_nil.symm
  case terminal =>
    intro a rhs pieces _ ih
    obtain ⟨rhs', herase, htype, hd⟩ := ih
    refine ⟨Sum.inr a :: rhs', ?_, ?_, MixedSymbolsDerive.terminal hd⟩
    · rw [List.map_cons, herase]; rfl
    · rw [annRhsType_cons, htype, List.flatten_cons, g.map_append]
      rfl
  case nonterminal =>
    intro A rhs w pieces _ _ ihA ihT
    obtain ⟨rhs', herase, htype, hd⟩ := ihT
    refine ⟨Sum.inl (A, g.h w) :: rhs', ?_, ?_,
      MixedSymbolsDerive.nonterminal ihA hd⟩
    · rw [List.map_cons, herase]; rfl
    · rw [annRhsType_cons, htype, List.flatten_cons, g.map_append]
      rfl

/-- `(A, m) ⇒* w` in the typed refinement iff `A ⇒* w` and `g(w) = m`. -/
theorem typedRefinement_derives_iff (R : MixedRules N α)
    (g : FixedFiniteMonoidHom α Mg) (A : N) (m : Mg) (w : List α) :
    MixedDerives (typedRefinement R g) (A, m) w ↔
      MixedDerives R A w ∧ g.h w = m := by
  constructor
  · intro d
    exact typedRefinement_derives_sound R g d
  · rintro ⟨d, rfl⟩
    exact typedRefinement_derives_complete R g d

end TypedRefinement

section StartUnion

variable {X : Type u} {α : Type v}

/-- Lift a symbol to the grammar with a fresh start symbol `none`. -/
def liftSym : MixedSymbol X α → MixedSymbol (Option X) α :=
  Sum.map some id

/-- Fresh start symbol `none` with unit rules to the selected starts. -/
def startUnion (R : MixedRules X α) (st : X → Prop) :
    MixedRules (Option X) α
  | none, rhs => ∃ x, st x ∧ rhs = [Sum.inl (some x)]
  | some x, rhs => ∃ rhs', R x rhs' ∧ rhs = rhs'.map liftSym

theorem startUnion_none_iff (R : MixedRules X α) (st : X → Prop)
    (rhs : List (MixedSymbol (Option X) α)) :
    startUnion R st none rhs ↔ ∃ x, st x ∧ rhs = [Sum.inl (some x)] :=
  Iff.rfl

theorem startUnion_some_iff (R : MixedRules X α) (st : X → Prop) (x : X)
    (rhs : List (MixedSymbol (Option X) α)) :
    startUnion R st (some x) rhs ↔ ∃ rhs', R x rhs' ∧ rhs = rhs'.map liftSym :=
  Iff.rfl

/-- Embedded derivations are source derivations. -/
theorem startUnion_some_sound (R : MixedRules X α) (st : X → Prop)
    {o : Option X} {w : List α}
    (d : MixedDerives (startUnion R st) o w) :
    ∀ x, o = some x → MixedDerives R x w := by
  refine MixedDerives.rec
    (motive_1 := fun o w _ => ∀ x, o = some x → MixedDerives R x w)
    (motive_2 := fun rhs'' pieces _ =>
      ∀ rhs, rhs'' = rhs.map liftSym → MixedSymbolsDerive R rhs pieces)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro o rhs'' pieces hR _ ih x hx
    subst hx
    obtain ⟨rhs, hRx, hrhs⟩ := (startUnion_some_iff R st x rhs'').1 hR
    exact MixedDerives.rule hRx (ih rhs hrhs)
  case nil =>
    intro rhs h
    have : rhs = [] := List.map_eq_nil_iff.mp h.symm
    subst this
    exact MixedSymbolsDerive.nil
  case terminal =>
    intro a rhs'' pieces _ ih rhs h
    cases rhs with
    | nil => exact absurd h (by simp)
    | cons s rest =>
        rw [List.map_cons] at h
        obtain ⟨h1, h2⟩ := List.cons.inj h
        cases s with
        | inl y => simp [liftSym] at h1
        | inr b =>
            simp only [liftSym, Sum.map_inr, id, Sum.inr.injEq] at h1
            subst h1
            exact MixedSymbolsDerive.terminal (ih rest h2)
  case nonterminal =>
    intro o rhs'' w pieces _ _ ihA ihT rhs h
    cases rhs with
    | nil => exact absurd h (by simp)
    | cons s rest =>
        rw [List.map_cons] at h
        obtain ⟨h1, h2⟩ := List.cons.inj h
        cases s with
        | inr b => simp [liftSym] at h1
        | inl y =>
            simp only [liftSym, Sum.map_inl, Sum.inl.injEq] at h1
            exact MixedSymbolsDerive.nonterminal (ihA y h1) (ihT rest h2)

/-- Source derivations embed. -/
theorem startUnion_some_complete (R : MixedRules X α) (st : X → Prop)
    {x : X} {w : List α}
    (d : MixedDerives R x w) :
    MixedDerives (startUnion R st) (some x) w := by
  refine MixedDerives.rec
    (motive_1 := fun x w _ => MixedDerives (startUnion R st) (some x) w)
    (motive_2 := fun rhs pieces _ =>
      MixedSymbolsDerive (startUnion R st) (rhs.map liftSym) pieces)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro x rhs pieces hR _ ih
    exact MixedDerives.rule ((startUnion_some_iff R st x _).2 ⟨rhs, hR, rfl⟩) ih
  case nil =>
    exact MixedSymbolsDerive.nil
  case terminal =>
    intro a rhs pieces _ ih
    show MixedSymbolsDerive (startUnion R st) (Sum.inr a :: rhs.map liftSym) _
    exact MixedSymbolsDerive.terminal ih
  case nonterminal =>
    intro y rhs w pieces _ _ ihA ihT
    show MixedSymbolsDerive (startUnion R st)
      (Sum.inl (some y) :: rhs.map liftSym) _
    exact MixedSymbolsDerive.nonterminal ihA ihT

theorem startUnion_some_iff_derives (R : MixedRules X α) (st : X → Prop)
    (x : X) (w : List α) :
    MixedDerives (startUnion R st) (some x) w ↔ MixedDerives R x w :=
  ⟨fun d => startUnion_some_sound R st d x rfl,
   fun d => startUnion_some_complete R st d⟩

/-- The fresh start generates the union of the selected start languages. -/
theorem startUnion_none_iff_derives (R : MixedRules X α) (st : X → Prop)
    (w : List α) :
    MixedDerives (startUnion R st) none w ↔
      ∃ x, st x ∧ MixedDerives R x w := by
  constructor
  · intro d
    cases d with
    | @rule _ rhs pieces hR hp =>
        obtain ⟨x, hx, rfl⟩ := (startUnion_none_iff R st rhs).1 hR
        cases hp with
        | @nonterminal _ _ w' pieces' head tail =>
            cases tail with
            | nil =>
                refine ⟨x, hx, ?_⟩
                have := (startUnion_some_iff_derives R st x w').1 head
                simpa using this
  · rintro ⟨x, hx, d⟩
    have d' := (startUnion_some_iff_derives R st x w).2 d
    have hrule := (startUnion_none_iff R st [Sum.inl (some x)]).2 ⟨x, hx, rfl⟩
    have := MixedDerives.rule hrule
      (MixedSymbolsDerive.nonterminal d' MixedSymbolsDerive.nil)
    simpa using this

end StartUnion

section IndexedPresentation

variable {N : Type u} {α : Type v} {P : Type w}
variable {Mg : Type q} [Monoid Mg] [Fintype Mg]

/-- Annotate one source symbol with a type (terminals ignore it). -/
def annSym : MixedSymbol N α → Mg → MixedSymbol (N × Mg) α
  | Sum.inl B, m => Sum.inl (B, m)
  | Sum.inr a, _ => Sum.inr a

/-- Read the annotation of a symbol (`1` for terminals). -/
def symAnn : MixedSymbol (N × Mg) α → Mg
  | Sum.inl X => X.2
  | Sum.inr _ => 1

theorem eraseSymbol_annSym (s : MixedSymbol N α) (m : Mg) :
    eraseSymbol (annSym s m) = s := by
  cases s <;> rfl

theorem annSym_eraseSymbol (s : MixedSymbol (N × Mg) α) :
    annSym (eraseSymbol s) (symAnn s) = s := by
  cases s <;> rfl

/-- Annotate a right-hand side by a choice of types for its positions. -/
def annotateRhs (r : List (MixedSymbol N α)) (σ : Fin r.length → Mg) :
    List (MixedSymbol (N × Mg) α) :=
  List.ofFn (fun i : Fin r.length => annSym (r.get i) (σ i))

theorem erase_annotateRhs (r : List (MixedSymbol N α))
    (σ : Fin r.length → Mg) :
    (annotateRhs r σ).map eraseSymbol = r := by
  apply List.ext_get
  · simp [annotateRhs]
  · intro n h1 h2
    simp [annotateRhs, eraseSymbol_annSym]

theorem annotateRhs_surj (rhs' : List (MixedSymbol (N × Mg) α))
    (r : List (MixedSymbol N α)) (hr : r = rhs'.map eraseSymbol) :
    ∃ σ : Fin r.length → Mg, annotateRhs r σ = rhs' := by
  subst hr
  refine ⟨fun i => symAnn (rhs'.get ⟨i.1, by simpa using i.2⟩), ?_⟩
  apply List.ext_get
  · simp [annotateRhs]
  · intro n h1 h2
    simp [annotateRhs, annSym_eraseSymbol]

variable [Fintype P]

/-- Production index of the filtered grammar. -/
abbrev RegularFilterProd (G : IndexedMixedCFG N α P) (F : Finset Mg) :=
  (Σ p : P, (Fin (G.rhs p).length → Mg)) ⊕ F

/-- Finite indexed CFG for `L(G, S) ∩ g⁻¹(F)` with start symbol `none`. -/
def regularFilterGrammar (G : IndexedMixedCFG N α P) (S : N)
    (g : FixedFiniteMonoidHom α Mg) (F : Finset Mg) :
    IndexedMixedCFG (Option (N × Mg)) α (RegularFilterProd G F) where
  lhs := fun q =>
    match q with
    | Sum.inl ⟨p, σ⟩ =>
        some (G.lhs p, annRhsType g (annotateRhs (G.rhs p) σ))
    | Sum.inr _ => none
  rhs := fun q =>
    match q with
    | Sum.inl ⟨p, σ⟩ => (annotateRhs (G.rhs p) σ).map liftSym
    | Sum.inr m => [Sum.inl (some (S, m.1))]

/-- The indexed presentation has exactly the rules of the composite
predicate grammar. -/
theorem regularFilterGrammar_rules (G : IndexedMixedCFG N α P) (S : N)
    (g : FixedFiniteMonoidHom α Mg) (F : Finset Mg) :
    (regularFilterGrammar G S g F).toMixedRules =
      startUnion (typedRefinement G.toMixedRules g)
        (fun X => X.1 = S ∧ X.2 ∈ F) := by
  funext o rhs''
  apply propext
  cases o with
  | none =>
      rw [startUnion_none_iff]
      constructor
      · rintro ⟨q, hq, rfl⟩
        cases q with
        | inl pσ =>
            obtain ⟨p, σ⟩ := pσ
            simp [regularFilterGrammar] at hq
        | inr m => exact ⟨(S, m.1), ⟨rfl, m.2⟩, rfl⟩
      · rintro ⟨⟨S', m⟩, ⟨hS, hm⟩, rfl⟩
        simp only at hS hm
        subst hS
        exact ⟨Sum.inr ⟨m, hm⟩, rfl, rfl⟩
  | some X =>
      rw [startUnion_some_iff]
      constructor
      · rintro ⟨q, hq, rfl⟩
        cases q with
        | inr m => simp [regularFilterGrammar] at hq
        | inl pσ =>
            obtain ⟨p, σ⟩ := pσ
            simp only [regularFilterGrammar, Option.some.injEq] at hq
            subst hq
            refine ⟨annotateRhs (G.rhs p) σ, ?_, rfl⟩
            rw [typedRefinement_iff]
            refine ⟨⟨p, rfl, ?_⟩, rfl⟩
            exact (erase_annotateRhs (G.rhs p) σ).symm
      · rintro ⟨rhs', hR, rfl⟩
        obtain ⟨⟨p, hlhs, hrhs⟩, htype⟩ := (typedRefinement_iff _ g X rhs').1 hR
        obtain ⟨σ, hσ⟩ := annotateRhs_surj rhs' (G.rhs p) hrhs
        refine ⟨Sum.inl ⟨p, σ⟩, ?_, ?_⟩
        · show some (G.lhs p, annRhsType g (annotateRhs (G.rhs p) σ)) = some X
          rw [hσ, hlhs, htype]
        · show (annotateRhs (G.rhs p) σ).map liftSym = rhs'.map liftSym
          rw [hσ]

/-- **CFL closure under regular filtering, constructively.**
The explicit finite grammar `regularFilterGrammar G S g F` generates exactly
`L(G, S) ∩ g⁻¹(F)`. -/
theorem regularFilterGrammar_language (G : IndexedMixedCFG N α P) (S : N)
    (g : FixedFiniteMonoidHom α Mg) (F : Finset Mg) :
    MixedNonterminalLanguage (regularFilterGrammar G S g F).toMixedRules none =
      MixedNonterminalLanguage G.toMixedRules S ∩
        RecognizedPreimage g (↑F : Set Mg) := by
  ext w
  change MixedDerives (regularFilterGrammar G S g F).toMixedRules none w ↔
    MixedDerives G.toMixedRules S w ∧ g.h w ∈ (↑F : Set Mg)
  rw [regularFilterGrammar_rules, startUnion_none_iff_derives]
  constructor
  · rintro ⟨⟨A, m⟩, ⟨hA, hm⟩, d⟩
    simp only at hA hm
    subst hA
    obtain ⟨d', hw⟩ := (typedRefinement_derives_iff _ g A m w).1 d
    exact ⟨d', by rw [hw]; exact_mod_cast hm⟩
  · rintro ⟨d, hw⟩
    refine ⟨(S, g.h w), ⟨rfl, by exact_mod_cast hw⟩, ?_⟩
    exact (typedRefinement_derives_iff _ g S (g.h w) w).2 ⟨d, rfl⟩

end IndexedPresentation

section FiniteInfoClosureII

variable {N : Type u} {α : Type v} {P : Type w}
variable {M : Type q} [Monoid M] [Fintype M]
variable {Mg : Type q} [Monoid Mg] [Fintype Mg]
variable [Fintype N] [Fintype P]

/--
**`prop:finite-info-closure` (ii), complete for finite indexed CFGs.**

If `L = L(G, S)` is generated by a finite CFG and is `h`-substitutable, then
for any finite-monoid typing `g` and finite accepted set `F`, the language
`L ∩ g⁻¹(F)` is generated by an explicit finite CFG (finite nonterminal and
production index types) and is `(h × g)`-substitutable.
-/
theorem finiteInfoClosure_ii_cfl
    (H : FixedFiniteMonoidHom α M)
    (g : FixedFiniteMonoidHom α Mg)
    (F : Finset Mg)
    (G : IndexedMixedCFG N α P) (S : N)
    (hL : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S)) :
    Nonempty (Fintype (Option (N × Mg))) ∧
    Nonempty (Fintype (RegularFilterProd G F)) ∧
    MixedNonterminalLanguage (regularFilterGrammar G S g F).toMixedRules none =
      MixedNonterminalLanguage G.toMixedRules S ∩
        RecognizedPreimage g (↑F : Set Mg) ∧
    FixedHSubstitutable (productTyping H g)
      (MixedNonterminalLanguage G.toMixedRules S ∩
        RecognizedPreimage g (↑F : Set Mg)) :=
  ⟨⟨inferInstance⟩, ⟨inferInstance⟩, regularFilterGrammar_language G S g F,
    fixedHSubstitutable_regularFilter_product H g (↑F : Set Mg) hL⟩

end FiniteInfoClosureII

end TCS1
end LeanCfgProject
