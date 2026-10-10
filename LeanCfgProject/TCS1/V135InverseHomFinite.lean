import LeanCfgProject.TCS1.V135InverseHomCFL
import LeanCfgProject.TCS1.V128ErasureFlagTyping

/-!
# TCS #1 v135: `prop:finite-info-closure` (iii), CFL side with a finite grammar

`V135InverseHomCFL` gives a predicate grammar for `φ⁻¹(L)` whose
nonterminals carry arbitrary transducer states.  Here:

1. `restrictRules`: restricting a predicate grammar to a set `V` of
   nonterminals preserves derivations from `V`, provided every successful
   rule from a `V`-nonterminal only uses `V`-nonterminals
   (`restrict_derives_iff`).
2. For the inverse-image grammar, `V` = "both transducer states are valid";
   valid states are finitely many (`finite_validState`), and every rule has
   right-hand side of bounded length.
3. `exists_indexed_of_bounded`: a predicate grammar over finite nonterminal
   and terminal types with bounded right-hand sides is the rule predicate of a
   finite `IndexedMixedCFG`.
4. `cfl_inverseImage`: for every finite indexed CFG `G` with start `S` over `Σ`
   and every (possibly erasing) homomorphism `φ : Γ* → Σ*` with finite `Γ`,
   there is a finite indexed CFG generating exactly `φ⁻¹(L(G,S))`.
5. `finiteInfoClosure_iii_cfl`: the full manuscript item (iii) for CFLs —
   `φ⁻¹(L)` is a CFL and is `ĥ`-substitutable for
   `ĥ = (h ∘ φ) × e_φ` (`erasingInverseTyping`, reused).
-/

namespace LeanCfgProject
namespace TCS1
namespace InverseHom

set_option linter.unusedSectionVars false

universe u

section Restriction

variable {X T : Type u}

/-- Forget the membership proof of a restricted nonterminal. -/
def liftSymV (V : X → Prop) : MixedSymbol {x // V x} T → MixedSymbol X T :=
  Sum.map Subtype.val id

/-- The grammar restricted to the nonterminals satisfying `V`. -/
def restrictRules (R : MixedRules X T) (V : X → Prop) : MixedRules {x // V x} T :=
  fun A rhs => R A.1 (rhs.map (liftSymV V))

theorem restrict_sound (R : MixedRules X T) (V : X → Prop) {A : {x // V x}}
    {w : List T} (d : MixedDerives (restrictRules R V) A w) :
    MixedDerives R A.1 w := by
  refine MixedDerives.rec
    (motive_1 := fun A w _ => MixedDerives R A.1 w)
    (motive_2 := fun rhs pieces _ =>
      MixedSymbolsDerive R (rhs.map (liftSymV V)) pieces)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR _ ih
    exact MixedDerives.rule hR ih
  case nil => exact MixedSymbolsDerive.nil
  case terminal =>
    intro a rhs pieces _ ih
    exact MixedSymbolsDerive.terminal ih
  case nonterminal =>
    intro B rhs w pieces _ _ ihA ihT
    exact MixedSymbolsDerive.nonterminal ihA ihT

/-- Every nonterminal of a successfully derived right-hand side is productive. -/
theorem msd_productive {R : MixedRules X T} :
    ∀ {rhs : List (MixedSymbol X T)} {pieces : List (List T)},
      MixedSymbolsDerive R rhs pieces →
      ∀ Y, Sum.inl Y ∈ rhs → ∃ w, MixedDerives R Y w := by
  intro rhs
  induction rhs with
  | nil => intro pieces _ Y hY; cases hY
  | cons s rhs ih =>
      intro pieces d Y hY
      cases d with
      | terminal tail =>
          rcases List.mem_cons.mp hY with h | h
          · cases h
          · exact ih tail Y h
      | @nonterminal B _ w _ head tail =>
          rcases List.mem_cons.mp hY with h | h
          · cases h; exact ⟨w, head⟩
          · exact ih tail Y h

theorem restrict_complete (R : MixedRules X T) (V : X → Prop)
    (hV : ∀ X' rhs pieces, V X' → R X' rhs → MixedSymbolsDerive R rhs pieces →
      ∀ Y, Sum.inl Y ∈ rhs → V Y)
    {A : X} {w : List T} (d : MixedDerives R A w) :
    ∀ hA : V A, MixedDerives (restrictRules R V) ⟨A, hA⟩ w := by
  refine MixedDerives.rec
    (motive_1 := fun A w _ => ∀ hA : V A, MixedDerives (restrictRules R V) ⟨A, hA⟩ w)
    (motive_2 := fun rhs pieces _ => (∀ Y, Sum.inl Y ∈ rhs → V Y) →
      ∃ rhs'', rhs''.map (liftSymV V) = rhs ∧
        MixedSymbolsDerive (restrictRules R V) rhs'' pieces)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR hp ih hA
    obtain ⟨rhs'', hmap, hd⟩ := ih (hV A rhs pieces hA hR hp)
    refine MixedDerives.rule (R := restrictRules R V) ?_ hd
    show R A (rhs''.map (liftSymV V))
    rw [hmap]
    exact hR
  case nil =>
    intro _
    exact ⟨[], rfl, MixedSymbolsDerive.nil⟩
  case terminal =>
    intro a rhs pieces _ ih hY
    obtain ⟨rhs'', hmap, hd⟩ := ih (fun Y h => hY Y (List.mem_cons_of_mem _ h))
    exact ⟨Sum.inr a :: rhs'', by rw [List.map_cons, hmap]; rfl,
      MixedSymbolsDerive.terminal hd⟩
  case nonterminal =>
    intro B rhs w pieces _ _ ihA ihT hY
    have hB : V B := hY B (by simp)
    obtain ⟨rhs'', hmap, hd⟩ := ihT (fun Y h => hY Y (List.mem_cons_of_mem _ h))
    exact ⟨Sum.inl ⟨B, hB⟩ :: rhs'', by rw [List.map_cons, hmap]; rfl,
      MixedSymbolsDerive.nonterminal (ihA hB) hd⟩

theorem restrict_derives_iff (R : MixedRules X T) (V : X → Prop)
    (hV : ∀ X' rhs pieces, V X' → R X' rhs → MixedSymbolsDerive R rhs pieces →
      ∀ Y, Sum.inl Y ∈ rhs → V Y)
    (A : {x // V x}) (w : List T) :
    MixedDerives (restrictRules R V) A w ↔ MixedDerives R A.1 w :=
  ⟨restrict_sound R V, fun d => restrict_complete R V hV d A.2⟩

end Restriction

section FiniteIndexing

variable {X T : Type u}

/-- **Finite presentation.**  A predicate grammar over finite nonterminal and
terminal types whose right-hand sides have bounded length is the rule
predicate of a finite indexed CFG. -/
theorem exists_indexed_of_bounded [Finite X] [Finite T] (R : MixedRules X T)
    (m : Nat) (hR : ∀ A rhs, R A rhs → rhs.length ≤ m) :
    ∃ (P : Type u) (_ : Fintype P) (G : IndexedMixedCFG X T P),
      G.toMixedRules = R := by
  classical
  let P := {r : X × List (MixedSymbol X T) // R r.1 r.2}
  have hfin : Set.Finite {r : X × List (MixedSymbol X T) | R r.1 r.2} := by
    apply Set.Finite.subset
      ((Set.finite_univ (α := X)).prod (List.finite_length_le (MixedSymbol X T) m))
    intro r hr
    exact ⟨Set.mem_univ _, hR r.1 r.2 hr⟩
  haveI : Finite P := hfin.to_subtype
  refine ⟨P, Fintype.ofFinite P, ⟨fun r => r.1.1, fun r => r.1.2⟩, ?_⟩
  funext A rhs
  apply propext
  constructor
  · rintro ⟨r, rfl, rfl⟩
    exact r.2
  · intro h
    exact ⟨⟨(A, rhs), h⟩, rfl, rfl⟩

end FiniteIndexing

section ValidStates

variable {N Γ Sig : Type u} (φ : Γ → List Sig)

/-- Valid transducer states. -/
abbrev ValidState := {s : TState Γ Sig // TValid φ s}

theorem finite_validState [Finite Γ] : Finite (ValidState φ) := by
  classical
  haveI := Fintype.ofFinite Γ
  let B := Finset.univ.sup (fun c => (φ c).length)
  let f : ValidState φ → Option (Γ × Fin (B + 1)) := fun s =>
    match s with
    | ⟨none, _⟩ => none
    | ⟨some (c, r), h⟩ => some (c, ⟨r.length, by
        have h1 : r.length ≤ (φ c).length := h.2.length_le
        have h2 : (φ c).length ≤ B := Finset.le_sup (f := fun c => (φ c).length)
          (Finset.mem_univ c)
        omega⟩)
  apply Finite.of_injective f
  rintro ⟨s, hs⟩ ⟨t, ht⟩ hst
  match s, t, hs, ht, hst with
  | none, none, _, _, _ => rfl
  | none, some _, _, _, h => cases h
  | some _, none, _, _, h => cases h
  | some (c, r), some (c', r'), hs, ht, h =>
      simp only [f, Option.some.injEq, Prod.mk.injEq, Fin.mk.injEq] at h
      obtain ⟨rfl, hl⟩ := h
      have e1 := List.suffix_iff_eq_drop.mp hs.2
      have e2 := List.suffix_iff_eq_drop.mp ht.2
      apply Subtype.ext
      show some (c, r) = some (c, r')
      rw [e1, e2, hl]

end ValidStates

section InverseImageGrammar

variable {N Γ Sig : Type u} (φ : Γ → List Sig)

/-- Validity predicate on the nonterminals of the inverse-image grammar. -/
def invValid : (N × TState Γ Sig × TState Γ Sig) ⊕ Bool → Prop
  | Sum.inl X => TValid φ X.2.1 ∧ TValid φ X.2.2
  | Sum.inr _ => True

theorem annot_length {s t : TState Γ Sig} {rhs : List (MixedSymbol N Sig)}
    {rhs' : List (MixedSymbol (N × TState Γ Sig × TState Γ Sig) Γ)}
    (h : Annot φ s rhs t rhs') : rhs'.length ≤ rhs.length := by
  induction h with
  | nil => simp
  | nt h ih => simp; omega
  | tm hs h ih =>
      cases hs <;> simp <;> omega

theorem flatMap_insSym_length {X : Type u} (l : List (MixedSymbol X Γ)) :
    (l.flatMap insSym).length ≤ 2 * l.length := by
  induction l with
  | nil => simp
  | cons s l ih =>
      rw [List.flatMap_cons, List.length_append, List.length_cons]
      have h : (insSym s).length ≤ 2 := by cases s <;> simp [insSym]
      omega

theorem mem_flatMap_insSym_cases {X : Type u} (l : List (MixedSymbol X Γ))
    (Y : X ⊕ Bool) (h : Sum.inl Y ∈ l.flatMap insSym) :
    Y = Sum.inr false ∨ ∃ Z, Y = Sum.inl Z ∧ Sum.inl Z ∈ l := by
  obtain ⟨s, hs, hY⟩ := List.mem_flatMap.mp h
  cases s with
  | inl B =>
      have e : Y = Sum.inl B := by simpa [insSym] using hY
      exact Or.inr ⟨B, e, hs⟩
  | inr c =>
      have e : Y = Sum.inr false := by simpa [insSym] using hY
      exact Or.inl e

theorem mem_flatMap_insSym_of_mem {X : Type u} (l : List (MixedSymbol X Γ))
    (Z : X) (h : Sum.inl Z ∈ l) : Sum.inl (Sum.inl Z) ∈ l.flatMap insSym :=
  List.mem_flatMap.mpr ⟨_, h, by simp [insSym]⟩

/-- Along an annotation from a valid state, every refined nonterminal whose
endpoints are connected by a run has valid endpoints. -/
theorem annot_valid {s t : TState Γ Sig} {rhs : List (MixedSymbol N Sig)}
    {rhs' : List (MixedSymbol (N × TState Γ Sig × TState Γ Sig) Γ)}
    (h : Annot φ s rhs t rhs') (hs : TValid φ s)
    (hrun : ∀ B s' q', Sum.inl (B, s', q') ∈ rhs' → ∃ u y, TRun φ s' u q' y) :
    ∀ B s' q', Sum.inl (B, s', q') ∈ rhs' → TValid φ s' ∧ TValid φ q' := by
  induction h with
  | nil => intro B s' q' hm; cases hm
  | @nt s q t B rhs rhs' h ih =>
      obtain ⟨u, y, hr⟩ := hrun B s q (by simp)
      have hq : TValid φ q := trun_valid φ hr hs
      intro B' s' q' hm
      rcases List.mem_cons.mp hm with he | hm
      · simp only [Sum.inl.injEq, Prod.mk.injEq] at he
        obtain ⟨rfl, rfl, rfl⟩ := he
        exact ⟨hs, hq⟩
      · exact ih hq (fun B s' q' h => hrun B s' q' (List.mem_cons_of_mem _ h)) B' s' q' hm
  | @tm s q t a o rhs rhs' hstep h ih =>
      have hq : TValid φ q := tstep_valid φ hstep hs
      have hsub : ∀ Y, Sum.inl Y ∈ rhs' → Sum.inl Y ∈ o.map Sum.inr ++ rhs' :=
        fun Y hY => List.mem_append_right _ hY
      intro B' s' q' hm
      have hm' : Sum.inl (B', s', q') ∈ rhs' := by
        rcases List.mem_append.mp hm with hm | hm
        · simp at hm
        · exact hm
      exact ih hq (fun B s' q' h => hrun B s' q' (hsub _ h)) B' s' q' hm'

theorem erasingInverse_valid (R : MixedRules N Sig) (S : N) :
    ∀ X' rhs pieces, invValid φ X' → erasingInverseRules φ R S X' rhs →
      MixedSymbolsDerive (erasingInverseRules φ R S) rhs pieces →
      ∀ Y, Sum.inl Y ∈ rhs → invValid φ Y := by
  intro X' rhs pieces hX hR hd Y hY
  match X', hR, hX with
  | Sum.inr false, hR, _ =>
      rcases hR with rfl | ⟨d, _, rfl⟩
      · cases hY
      · simp at hY
        subst hY
        trivial
  | Sum.inr true, hR, _ =>
      have hR' : rhs = [Sum.inl (Sum.inl (S, none, none)), Sum.inl (Sum.inr false)] := hR
      subst hR'
      simp at hY
      rcases hY with rfl | rfl
      · exact ⟨trivial, trivial⟩
      · trivial
  | Sum.inl X, hR, hX =>
      obtain ⟨rhs1, ⟨rhs0, _, hA⟩, rfl⟩ := hR
      rcases mem_flatMap_insSym_cases rhs1 Y hY with rfl | ⟨Z, rfl, hZ⟩
      · trivial
      · -- every refined nonterminal of the rule is productive, hence connected
        have hprod : ∀ B s' q', Sum.inl (B, s', q') ∈ rhs1 →
            ∃ u y, TRun φ s' u q' y := by
          intro B s' q' hm
          have hm' : Sum.inl (Sum.inl (B, s', q')) ∈ rhs1.flatMap insSym :=
            mem_flatMap_insSym_of_mem rhs1 _ hm
          obtain ⟨w, dw⟩ := msd_productive hd _ hm'
          have hw := mixedDerives_mem_closed _ _
            (insInterp_closed (invRules φ R) (fun c => φ c = []) (S, none, none)) dw
          obtain ⟨y₁, d₁, _⟩ := hw
          obtain ⟨u, _, hr⟩ := (inv_derives_iff φ R B s' q' y₁).1 d₁
          exact ⟨u, y₁, hr⟩
        obtain ⟨B, s', q'⟩ := Z
        exact annot_valid φ hA hX.1 hprod B s' q' hZ

theorem erasingInverse_bounded (R : MixedRules N Sig) (S : N) (m : Nat)
    (hR : ∀ A rhs, R A rhs → rhs.length ≤ m) :
    ∀ X' rhs, erasingInverseRules φ R S X' rhs → rhs.length ≤ 2 * m + 2 := by
  intro X' rhs h
  match X', h with
  | Sum.inr false, h =>
      rcases h with rfl | ⟨d, _, rfl⟩ <;> simp
  | Sum.inr true, h =>
      have h' : rhs = [Sum.inl (Sum.inl (S, none, none)), Sum.inl (Sum.inr false)] := h
      subst h'
      simp
  | Sum.inl X, h =>
      obtain ⟨rhs1, ⟨rhs0, h0, hA⟩, rfl⟩ := h
      have l1 := annot_length φ hA
      have l0 := hR _ _ h0
      have l2 := flatMap_insSym_length rhs1
      omega

end InverseImageGrammar

section Main

variable {N Γ Sig P : Type u}

/-- **CFLs are closed under (possibly erasing) inverse homomorphisms**, with an
explicit finite grammar: for a finite indexed CFG `G` with start `S` over `Σ`,
finite `Γ` and letter images `φ`, some finite indexed CFG over `Γ` generates
exactly `{y | φ(y) ∈ L(G, S)}`. -/
theorem cfl_inverseImage [Fintype N] [Fintype P] [Finite Γ]
    (G : IndexedMixedCFG N Sig P) (S : N) (φ : Γ → List Sig) :
    ∃ (N' P' : Type u) (_ : Fintype N') (_ : Fintype P')
      (G' : IndexedMixedCFG N' Γ P') (S' : N'),
      MixedNonterminalLanguage G'.toMixedRules S' =
        {y | y.flatMap φ ∈ MixedNonterminalLanguage G.toMixedRules S} := by
  classical
  let R := erasingInverseRules φ G.toMixedRules S
  let V := invValid (N := N) φ
  -- finiteness of the restricted nonterminals
  haveI : Finite (ValidState φ) := finite_validState φ
  have hfinV : Finite {x // V x} := by
    let g : {x // V x} → (N × ValidState φ × ValidState φ) ⊕ Bool := fun x =>
      match x with
      | ⟨Sum.inl (A, s, t), h⟩ => Sum.inl (A, ⟨s, h.1⟩, ⟨t, h.2⟩)
      | ⟨Sum.inr b, _⟩ => Sum.inr b
    apply Finite.of_injective g
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    match x, y, hx, hy, hxy with
    | Sum.inl (A, s, t), Sum.inl (A', s', t'), _, _, h =>
        simp only [g, Sum.inl.injEq, Prod.mk.injEq, Subtype.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rfl
    | Sum.inl _, Sum.inr _, _, _, h => cases h
    | Sum.inr _, Sum.inl _, _, _, h => cases h
    | Sum.inr b, Sum.inr b', _, _, h =>
        simp only [g, Sum.inr.injEq] at h
        subst h
        rfl
  -- bounded right-hand sides
  let m := Finset.univ.sup (fun p : P => (G.rhs p).length)
  have hm : ∀ A rhs, G.toMixedRules A rhs → rhs.length ≤ m := by
    rintro A rhs ⟨p, _, rfl⟩
    exact Finset.le_sup (f := fun p : P => (G.rhs p).length) (Finset.mem_univ p)
  have hbound : ∀ A rhs, restrictRules R V A rhs → rhs.length ≤ 2 * m + 2 := by
    intro A rhs h
    have := erasingInverse_bounded φ G.toMixedRules S m hm A.1 _ h
    simpa using this
  obtain ⟨P', hP', G', hG'⟩ := exists_indexed_of_bounded (restrictRules R V) _ hbound
  haveI := Fintype.ofFinite {x // V x}
  refine ⟨{x // V x}, P', inferInstance, hP', G', ⟨Sum.inr true, trivial⟩, ?_⟩
  ext y
  change MixedDerives G'.toMixedRules _ y ↔ MixedDerives G.toMixedRules S (y.flatMap φ)
  rw [hG', restrict_derives_iff R V (erasingInverse_valid φ G.toMixedRules S)]
  exact erasingInverse_language φ G.toMixedRules S y

/-- A word homomorphism is the `flatMap` of its letter images. -/
theorem wordHom_eq_flatMap {Γ Sig : Type u} (φ : Word Γ → Word Sig)
    (φ_nil : φ [] = []) (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y) :
    ∀ y : Word Γ, φ y = y.flatMap (fun c => φ [c])
  | [] => φ_nil
  | c :: y => by
      have := φ_append [c] y
      simp only [List.singleton_append] at this
      rw [this, wordHom_eq_flatMap φ φ_nil φ_append y]
      simp

/--
**`prop:finite-info-closure` (iii), complete for CFLs.**  For a finite-monoid
typing `H` on `Σ`, a (possibly erasing) homomorphism `φ : Γ* → Σ*` with finite
`Γ`, and `L = L(G, S)` generated by a finite indexed CFG and
`H`-substitutable, the inverse image `φ⁻¹(L)` is generated by a finite indexed
CFG and is substitutable for `ĥ = (H ∘ φ) × e_φ`.
-/
theorem finiteInfoClosure_iii_cfl {M : Type u} [Monoid M] [Fintype M]
    [Fintype N] [Fintype P] [Finite Γ]
    (H : FixedFiniteMonoidHom Sig M)
    (φ : Word Γ → Word Sig) (φ_nil : φ [] = [])
    (φ_append : ∀ x y, φ (x ++ y) = φ x ++ φ y)
    (G : IndexedMixedCFG N Sig P) (S : N)
    (hL : FixedHSubstitutable H (MixedNonterminalLanguage G.toMixedRules S)) :
    (∃ (N' P' : Type u) (_ : Fintype N') (_ : Fintype P')
      (G' : IndexedMixedCFG N' Γ P') (S' : N'),
      MixedNonterminalLanguage G'.toMixedRules S' =
        wordInverseImage φ (MixedNonterminalLanguage G.toMixedRules S)) ∧
    FixedHSubstitutable (erasingInverseTyping H φ φ_nil φ_append)
      (wordInverseImage φ (MixedNonterminalLanguage G.toMixedRules S)) := by
  refine ⟨?_, inverseImage_fixedHSubstitutable_with_erasureFlag H φ φ_nil φ_append _ hL⟩
  obtain ⟨N', P', hN', hP', G', S', hlang⟩ := cfl_inverseImage G S (fun c => φ [c])
  refine ⟨N', P', hN', hP', G', S', ?_⟩
  rw [hlang]
  ext y
  show y.flatMap (fun c => φ [c]) ∈ MixedNonterminalLanguage G.toMixedRules S ↔
    φ y ∈ MixedNonterminalLanguage G.toMixedRules S
  rw [wordHom_eq_flatMap φ φ_nil φ_append y]

end Main

end InverseHom
end TCS1
end LeanCfgProject
