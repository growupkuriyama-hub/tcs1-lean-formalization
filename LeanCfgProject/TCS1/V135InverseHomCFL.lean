import LeanCfgProject.TCS1.V135InverseHomTransducer
import LeanCfgProject.TCS1.V135LiThicknessExactCorollary
import LeanCfgProject.TCS1.LinearMixedRhsDecomposition

/-!
# TCS #1 v135: CFLs are closed under (possibly erasing) inverse homomorphisms

CFL side of `prop:finite-info-closure` (iii), semantic part.  For a CFG `R`
over `Σ` with start `S` and letter images `φ : Γ → List Σ`:

1. `invRules R φ` refines every nonterminal by a pair of transducer states
   (`V135InverseHomTransducer`): `(A, s, t) ⇒* y ↔ ∃ u, A ⇒* u ∧ TRun φ s u t y`
   (`inv_derives_iff`).  From `(S, none, none)` it generates exactly the
   nonerasing-letter words `y` with `φ(y) ∈ L` (`inv_language`).
2. `insRules R Z S` inserts arbitrary `Z`-letters before every terminal and
   at the end (`ins_start_iff`).
3. `erasingInverseRules R φ S` composes both with `Z c := φ c = []`, and
   generates exactly `{y | φ(y) ∈ L}` (`erasingInverse_language`).

Soundness directions use rule-closed interpretations
(`mixedDerives_mem_closed`); completeness directions use the mutual
recursor `MixedDerives.rec`.  No nonerasing assumption is made.
-/

namespace LeanCfgProject
namespace TCS1
namespace InverseHom

set_option linter.unusedSectionVars false

universe u

section InvRules

variable {N Γ Sig : Type u} (φ : Γ → List Sig)

/-- Annotation of a source right-hand side by a threaded transducer run. -/
inductive Annot : TState Γ Sig → List (MixedSymbol N Sig) → TState Γ Sig →
    List (MixedSymbol (N × TState Γ Sig × TState Γ Sig) Γ) → Prop
  | nil (s : TState Γ Sig) : Annot s [] s []
  | nt {s q t : TState Γ Sig} {B : N} {rhs : List (MixedSymbol N Sig)}
      {rhs' : List (MixedSymbol (N × TState Γ Sig × TState Γ Sig) Γ)}
      (h : Annot q rhs t rhs') :
      Annot s (Sum.inl B :: rhs) t (Sum.inl (B, s, q) :: rhs')
  | tm {s q t : TState Γ Sig} {a : Sig} {o : List Γ} {rhs : List (MixedSymbol N Sig)}
      {rhs' : List (MixedSymbol (N × TState Γ Sig × TState Γ Sig) Γ)}
      (hs : TStep φ s a q o) (h : Annot q rhs t rhs') :
      Annot s (Sum.inr a :: rhs) t (o.map Sum.inr ++ rhs')

/-- The state-refined grammar. -/
def invRules (R : MixedRules N Sig) : MixedRules (N × TState Γ Sig × TState Γ Sig) Γ :=
  fun X rhs' => ∃ rhs, R X.1 rhs ∧ Annot φ X.2.1 rhs X.2.2 rhs'

/-- Intended meaning of a refined nonterminal. -/
def invInterp (R : MixedRules N Sig) :
    N × TState Γ Sig × TState Γ Sig → Set (List Γ) :=
  fun X => {y | ∃ u, MixedDerives R X.1 u ∧ TRun φ X.2.1 u X.2.2 y}

theorem annot_realizes (R : MixedRules N Sig) {s t : TState Γ Sig}
    {rhs : List (MixedSymbol N Sig)}
    {rhs' : List (MixedSymbol (N × TState Γ Sig × TState Γ Sig) Γ)}
    (h : Annot φ s rhs t rhs') :
    ∀ y, RhsRealizes (invInterp φ R) rhs' y →
      ∃ pieces, MixedSymbolsDerive R rhs pieces ∧ TRun φ s pieces.flatten t y := by
  induction h with
  | nil s =>
      intro y hy
      have hy0 : y = [] := hy
      subst hy0
      exact ⟨[], MixedSymbolsDerive.nil, TRun.nil s⟩
  | @nt s q t B rhs rhs' h ih =>
      intro y hy
      obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := hy
      obtain ⟨u₁, d₁, r₁⟩ := hy₁
      obtain ⟨pieces, hp, hr⟩ := ih y₂ hy₂
      refine ⟨u₁ :: pieces, MixedSymbolsDerive.nonterminal d₁ hp, ?_⟩
      rw [List.flatten_cons]
      exact trun_append φ r₁ hr
  | @tm s q t a o rhs rhs' hs h ih =>
      intro y hy
      obtain ⟨tail, rfl, htail⟩ := (rhsRealizes_terminalPrefix_iff _ o rhs' y).1 hy
      obtain ⟨pieces, hp, hr⟩ := ih tail htail
      exact ⟨[a] :: pieces, MixedSymbolsDerive.terminal hp, TRun.cons hs hr⟩

theorem invInterp_closed (R : MixedRules N Sig) :
    GrammarClosed (invRules φ R) (invInterp φ R) := by
  intro X y hy
  obtain ⟨rhs', ⟨rhs, hR, hA⟩, hreal⟩ := hy
  obtain ⟨pieces, hp, hr⟩ := annot_realizes φ R hA y hreal
  exact ⟨pieces.flatten, MixedDerives.rule hR hp, hr⟩

theorem inv_complete (R : MixedRules N Sig) {A : N} {u : List Sig}
    (d : MixedDerives R A u) :
    ∀ s t y, TRun φ s u t y → MixedDerives (invRules φ R) (A, s, t) y := by
  refine MixedDerives.rec
    (motive_1 := fun A u _ => ∀ s t y, TRun φ s u t y →
      MixedDerives (invRules φ R) (A, s, t) y)
    (motive_2 := fun rhs pieces _ => ∀ s t y, TRun φ s pieces.flatten t y →
      ∃ rhs', Annot φ s rhs t rhs' ∧
        RhsRealizes (MixedNonterminalLanguage (invRules φ R)) rhs' y)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR _ ih s t y hrun
    obtain ⟨rhs', hA, hreal⟩ := ih s t y hrun
    exact (mixedDerives_iff_ruleStep).2 ⟨rhs', ⟨rhs, hR, hA⟩, hreal⟩
  case nil =>
    intro s t y hrun
    have h0 : TRun φ s [] t y := hrun
    cases h0
    exact ⟨[], Annot.nil _, rfl⟩
  case terminal =>
    intro a rhs pieces _ ih s t y hrun
    have h0 : TRun φ s (a :: pieces.flatten) t y := hrun
    cases h0 with
    | cons hs hr =>
        obtain ⟨rhs', hA, hreal⟩ := ih _ _ _ hr
        exact ⟨_, Annot.tm hs hA,
          (rhsRealizes_terminalPrefix_iff _ _ _ _).2 ⟨_, rfl, hreal⟩⟩
  case nonterminal =>
    intro A rhs w pieces _ _ ihA ihT s t y hrun
    have h0 : TRun φ s (w ++ pieces.flatten) t y := hrun
    obtain ⟨q, y₁, y₂, rfl, h₁, h₂⟩ := trun_append_split φ h0
    obtain ⟨rhs', hA, hreal⟩ := ihT q t y₂ h₂
    exact ⟨_, Annot.nt hA, ⟨y₁, y₂, rfl, ihA s q y₁ h₁, hreal⟩⟩

/-- **Semantics of the state-refined grammar.** -/
theorem inv_derives_iff (R : MixedRules N Sig) (A : N) (s t : TState Γ Sig)
    (y : List Γ) :
    MixedDerives (invRules φ R) (A, s, t) y ↔
      ∃ u, MixedDerives R A u ∧ TRun φ s u t y := by
  constructor
  · intro d
    exact mixedDerives_mem_closed _ _ (invInterp_closed φ R) d
  · rintro ⟨u, d, hr⟩
    exact inv_complete φ R d s t y hr

/-- From `(S, none, none)`: exactly the nonerasing-letter words in `φ⁻¹(L)`. -/
theorem inv_language (R : MixedRules N Sig) (S : N) (y : List Γ) :
    MixedDerives (invRules φ R) (S, none, none) y ↔
      MixedDerives R S (y.flatMap φ) ∧ ∀ c, c ∈ y → φ c ≠ [] := by
  rw [inv_derives_iff]
  constructor
  · rintro ⟨u, d, hr⟩
    obtain ⟨rfl, h⟩ := (trun_none_none_iff φ u y).1 hr
    exact ⟨d, h⟩
  · rintro ⟨d, h⟩
    exact ⟨_, d, (trun_none_none_iff φ _ y).2 ⟨rfl, h⟩⟩

end InvRules

section Insertion

variable {X Γ : Type u}

/-- Each terminal `c` becomes `E c`; nonterminals are kept. -/
def insSym : MixedSymbol X Γ → List (MixedSymbol (X ⊕ Bool) Γ)
  | Sum.inl B => [Sum.inl (Sum.inl B)]
  | Sum.inr c => [Sum.inl (Sum.inr false), Sum.inr c]

/-- Insertion grammar: `inr false` is the block nonterminal `E → λ | d E`
(`d ∈ Z`), `inr true` the new start `S' → S E`. -/
def insRules (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) :
    MixedRules (X ⊕ Bool) Γ
  | Sum.inl A, rhs' => ∃ rhs, R A rhs ∧ rhs' = rhs.flatMap insSym
  | Sum.inr false, rhs' =>
      rhs' = [] ∨ ∃ d, Z d ∧ rhs' = [Sum.inr d, Sum.inl (Sum.inr false)]
  | Sum.inr true, rhs' => rhs' = [Sum.inl (Sum.inl S), Sum.inl (Sum.inr false)]

/-- Intended meaning of the insertion grammar's nonterminals. -/
def insInterp (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) :
    X ⊕ Bool → Set (List Γ)
  | Sum.inl A => {y | ∃ y₁, MixedDerives R A y₁ ∧ InsertZ Z y₁ y}
  | Sum.inr false => {e | ∀ d, d ∈ e → Z d}
  | Sum.inr true => {y | ∃ y₁, MixedDerives R S y₁ ∧
      ∃ y' e, y = y' ++ e ∧ InsertZ Z y₁ y' ∧ ∀ d, d ∈ e → Z d}

theorem insertZ_append {Z : Γ → Prop} {u₁ y₁ u₂ y₂ : List Γ}
    (h₁ : InsertZ Z u₁ y₁) (h₂ : InsertZ Z u₂ y₂) :
    InsertZ Z (u₁ ++ u₂) (y₁ ++ y₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | @cons c u y e he h ih =>
      have := InsertZ.cons (c := c) he ih
      simpa [List.append_assoc] using this

theorem insertZ_append_split {Z : Γ → Prop} :
    ∀ {u₁ u₂ y : List Γ}, InsertZ Z (u₁ ++ u₂) y →
      ∃ y₁ y₂, y = y₁ ++ y₂ ∧ InsertZ Z u₁ y₁ ∧ InsertZ Z u₂ y₂ := by
  intro u₁
  induction u₁ with
  | nil => intro u₂ y h; exact ⟨[], y, rfl, InsertZ.nil, h⟩
  | cons c u₁ ih =>
      intro u₂ y h
      have h' : InsertZ Z (c :: (u₁ ++ u₂)) y := h
      cases h' with
      | @cons _ _ y' e he h'' =>
          obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := ih h''
          exact ⟨e ++ c :: y₁, y₂, by simp, InsertZ.cons he hy₁, hy₂⟩

theorem ins_realizes (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) :
    ∀ (rhs : List (MixedSymbol X Γ)) (y : List Γ),
      RhsRealizes (insInterp R Z S) (rhs.flatMap insSym) y →
      ∃ pieces, MixedSymbolsDerive R rhs pieces ∧ InsertZ Z pieces.flatten y
  | [], y, hy => by
      have hy0 : y = [] := hy
      subst hy0
      exact ⟨[], MixedSymbolsDerive.nil, InsertZ.nil⟩
  | Sum.inl B :: rhs, y, hy => by
      change RhsRealizes _ (Sum.inl (Sum.inl B) :: rhs.flatMap insSym) y at hy
      obtain ⟨y₁, y₂, rfl, hy₁, hy₂⟩ := hy
      obtain ⟨u₁, d₁, i₁⟩ := hy₁
      obtain ⟨pieces, hp, hi⟩ := ins_realizes R Z S rhs y₂ hy₂
      refine ⟨u₁ :: pieces, MixedSymbolsDerive.nonterminal d₁ hp, ?_⟩
      rw [List.flatten_cons]
      exact insertZ_append i₁ hi
  | Sum.inr c :: rhs, y, hy => by
      change RhsRealizes _ (Sum.inl (Sum.inr false) :: Sum.inr c ::
        rhs.flatMap insSym) y at hy
      obtain ⟨e, v, rfl, he, hv⟩ := hy
      obtain ⟨v', rfl, hv'⟩ := hv
      obtain ⟨pieces, hp, hi⟩ := ins_realizes R Z S rhs v' hv'
      exact ⟨[c] :: pieces, MixedSymbolsDerive.terminal hp, InsertZ.cons he hi⟩

theorem insInterp_closed (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) :
    GrammarClosed (insRules R Z S) (insInterp R Z S) := by
  intro X' y hy
  obtain ⟨rhs', hR, hreal⟩ := hy
  match X', hR with
  | Sum.inl A, hR =>
      obtain ⟨rhs, hRA, rfl⟩ := hR
      obtain ⟨pieces, hp, hi⟩ := ins_realizes R Z S rhs y hreal
      exact ⟨pieces.flatten, MixedDerives.rule hRA hp, hi⟩
  | Sum.inr false, hR =>
      rcases hR with rfl | ⟨d, hd, rfl⟩
      · have hy0 : y = [] := hreal
        subst hy0
        intro d hd
        cases hd
      · obtain ⟨tail, rfl, htail⟩ := hreal
        obtain ⟨e, v, rfl, he, hv⟩ := htail
        have hv0 : v = [] := hv
        subst hv0
        intro d' hd'
        rcases List.mem_cons.mp hd' with rfl | hd'
        · exact hd
        · exact he d' (by simpa using hd')
  | Sum.inr true, hR =>
      have hR' : rhs' = [Sum.inl (Sum.inl S), Sum.inl (Sum.inr false)] := hR
      subst hR'
      obtain ⟨y₁, v, rfl, hy₁, hv⟩ := hreal
      obtain ⟨e, v', rfl, he, hv'⟩ := hv
      have hv0 : v' = [] := hv'
      subst hv0
      obtain ⟨u₁, d₁, i₁⟩ := hy₁
      exact ⟨u₁, d₁, y₁, e, by simp, i₁, he⟩

theorem ins_block_complete (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) :
    ∀ e : List Γ, (∀ d, d ∈ e → Z d) →
      MixedDerives (insRules R Z S) (Sum.inr false) e
  | [], _ => by
      apply (mixedDerives_iff_ruleStep).2
      exact ⟨[], Or.inl rfl, rfl⟩
  | d :: e, he => by
      have ih := ins_block_complete R Z S e (fun d' hd' => he d' (by simp [hd']))
      apply (mixedDerives_iff_ruleStep).2
      refine ⟨[Sum.inr d, Sum.inl (Sum.inr false)],
        Or.inr ⟨d, he d (by simp), rfl⟩, ?_⟩
      exact ⟨e, rfl, e, [], by simp, ih, rfl⟩

theorem ins_complete (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) {A : X}
    {y₁ : List Γ} (d : MixedDerives R A y₁) :
    ∀ y, InsertZ Z y₁ y → MixedDerives (insRules R Z S) (Sum.inl A) y := by
  refine MixedDerives.rec
    (motive_1 := fun A y₁ _ => ∀ y, InsertZ Z y₁ y →
      MixedDerives (insRules R Z S) (Sum.inl A) y)
    (motive_2 := fun rhs pieces _ => ∀ y, InsertZ Z pieces.flatten y →
      RhsRealizes (MixedNonterminalLanguage (insRules R Z S))
        (rhs.flatMap insSym) y)
    ?rule ?nil ?terminal ?nonterminal d
  case rule =>
    intro A rhs pieces hR _ ih y hy
    exact (mixedDerives_iff_ruleStep).2 ⟨_, ⟨rhs, hR, rfl⟩, ih y hy⟩
  case nil =>
    intro y hy
    have h0 : InsertZ Z [] y := hy
    cases h0
    rfl
  case terminal =>
    intro c rhs pieces _ ih y hy
    have h0 : InsertZ Z (c :: pieces.flatten) y := hy
    cases h0 with
    | @cons _ _ y' e he h =>
        show RhsRealizes _ (Sum.inl (Sum.inr false) :: Sum.inr c ::
          rhs.flatMap insSym) (e ++ c :: y')
        exact ⟨e, c :: y', rfl, ins_block_complete R Z S e he, y', rfl, ih y' h⟩
  case nonterminal =>
    intro B rhs w pieces _ _ ihA ihT y hy
    have h0 : InsertZ Z (w ++ pieces.flatten) y := hy
    obtain ⟨y₁, y₂, rfl, h₁, h₂⟩ := insertZ_append_split h0
    show RhsRealizes _ (Sum.inl (Sum.inl B) :: rhs.flatMap insSym) (y₁ ++ y₂)
    exact ⟨y₁, y₂, rfl, ihA y₁ h₁, ihT y₂ h₂⟩

/-- **Semantics of the insertion grammar's start symbol.** -/
theorem ins_start_iff (R : MixedRules X Γ) (Z : Γ → Prop) (S : X) (y : List Γ) :
    MixedDerives (insRules R Z S) (Sum.inr true) y ↔
      ∃ y₁, MixedDerives R S y₁ ∧
        ∃ y' e, y = y' ++ e ∧ InsertZ Z y₁ y' ∧ ∀ d, d ∈ e → Z d := by
  constructor
  · intro d
    exact mixedDerives_mem_closed _ _ (insInterp_closed R Z S) d
  · rintro ⟨y₁, d, y', e, rfl, hi, he⟩
    apply (mixedDerives_iff_ruleStep).2
    refine ⟨[Sum.inl (Sum.inl S), Sum.inl (Sum.inr false)], rfl, ?_⟩
    exact ⟨y', e, rfl, ins_complete R Z S d y' hi, e, [], by simp,
      ins_block_complete R Z S e he, rfl⟩

end Insertion

section Composition

variable {N Γ Sig : Type u}

/-- Erasing inverse homomorphism grammar. -/
def erasingInverseRules (φ : Γ → List Sig) (R : MixedRules N Sig) (S : N) :
    MixedRules ((N × TState Γ Sig × TState Γ Sig) ⊕ Bool) Γ :=
  insRules (invRules φ R) (fun c => φ c = []) (S, none, none)

theorem flatMap_filter_nonerasing (φ : Γ → List Sig)
    [DecidablePred (fun c : Γ => φ c = [])] :
    ∀ y : List Γ, (y.filter (fun c => !decide (φ c = []))).flatMap φ = y.flatMap φ
  | [] => rfl
  | c :: y => by
      by_cases hc : φ c = []
      · rw [List.filter_cons_of_neg (by simp [hc]), flatMap_filter_nonerasing φ y]
        simp [hc]
      · rw [List.filter_cons_of_pos (by simp [hc])]
        simp [flatMap_filter_nonerasing φ y]

/-- **The erasing inverse-image grammar generates exactly `φ⁻¹(L)`.** -/
theorem erasingInverse_language (φ : Γ → List Sig) (R : MixedRules N Sig) (S : N)
    (y : List Γ) :
    MixedDerives (erasingInverseRules φ R S) (Sum.inr true) y ↔
      MixedDerives R S (y.flatMap φ) := by
  classical
  unfold erasingInverseRules
  rw [ins_start_iff]
  constructor
  · rintro ⟨y₁, d, hy⟩
    obtain ⟨hd, hne⟩ := (inv_language φ R S y₁).1 d
    have hfil := (insertZ_trailing_iff (fun c => φ c = []) y₁ y hne).1 hy
    rw [← flatMap_filter_nonerasing φ y, hfil]
    exact hd
  · intro d
    refine ⟨y.filter (fun c => !decide (φ c = [])), ?_, ?_⟩
    · apply (inv_language φ R S _).2
      refine ⟨by rw [flatMap_filter_nonerasing]; exact d, ?_⟩
      intro c hc
      have := (List.mem_filter.mp hc).2
      simpa using this
    · apply (insertZ_trailing_iff (fun c => φ c = []) _ y ?_).2 rfl
      intro c hc
      have := (List.mem_filter.mp hc).2
      simpa using this

end Composition

end InverseHom
end TCS1
end LeanCfgProject
