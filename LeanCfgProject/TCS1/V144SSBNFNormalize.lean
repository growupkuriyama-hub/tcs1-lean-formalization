import LeanCfgProject.TCS1.V144SSBNFFrontEnd

/-!
# TCS #1 v144: `prop:thick-ssbnf-normal` — executable normalization in polynomial time

`normalizeSSBNF nts alph prs A` is the executable normalizer (front end of
`V144SSBNFFrontEnd` followed by `normalizeTrace` of `V144SSBNFNormalizer`).
It returns the written reduced SSBNF grammar (`SSBNFCode`) and its step count.

For an `IndexedMixedCFG` given by complete listings (`Listing`) this file proves

* `codeMatches_indexed`: the front end writes exactly the existing finite
  front-end grammar `indexedFiniteFrontEndGrammar G`;
* `normalizeSSBNF_steps_le`: at most `900 · (m + 1)^6` steps, where `m` is the
  list size of the input (`inputScale`), which equals `G.normalizationScale`
  for duplicate-free listings;
* `prop_thickSSBNFNormal_executable` (paper-facing): the written grammar
  generates the source language, its nonterminals and rules are exactly those
  of the existing reduced SSBNF grammar of `indexed_proposition74_full_package`
  (so the existing size and thickness bounds apply to it), every written
  nonterminal is reachable and has a short yield, and the step count is
  polynomial.
-/

namespace LeanCfgProject
namespace TCS1
namespace SSBNFNorm

open Horn PolyBuild

universe u v w

section Indexed

variable {N : Type u} {α : Type v} {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P] [DecidableEq N] [DecidableEq α]

/-- Explicit input: duplicate-free complete listings of nonterminals, letters and
productions.  (The algorithm reads the lists; no `Finset` is enumerated.) -/
structure Listing (G : IndexedMixedCFG N α P) where
  nts : List N
  alph : List α
  prods : List P
  nts_complete : ∀ A, A ∈ nts
  alph_complete : ∀ a, a ∈ alph
  prods_complete : ∀ p, p ∈ prods
  nts_nodup : nts.Nodup
  alph_nodup : alph.Nodup
  prods_nodup : prods.Nodup

/-- The productions as explicit `(lhs, rhs)` records. -/
def Listing.prs {G : IndexedMixedCFG N α P} (L : Listing G) :
    List (N × List (MixedSymbol N α)) :=
  L.prods.map (fun p => (G.lhs p, G.rhs p))

/-- **The executable normalizer.** -/
def normalizeSSBNF (nts : List N) (alph : List α) (prs : List (N × List (MixedSymbol N α)))
    (A : N) : SSBNFCode (FrontEndState N α) α × Nat :=
  ((normalizeTrace stateEqC (frontCodeC nts alph prs).1 (BinarizedState.old (Sum.inl A))).out,
    (frontCodeC nts alph prs).2 +
      (normalizeTrace stateEqC (frontCodeC nts alph prs).1
        (BinarizedState.old (Sum.inl A))).steps)

variable (G : IndexedMixedCFG N α P) (L : Listing G)

theorem Listing.mem_prs (B : N) (r : List (MixedSymbol N α)) :
    (B, r) ∈ L.prs ↔ G.toMixedRules B r := by
  unfold Listing.prs IndexedMixedCFG.toMixedRules
  rw [List.mem_map]
  constructor
  · rintro ⟨p, _, he⟩
    simp only [Prod.mk.injEq] at he
    exact ⟨p, he.1, he.2⟩
  · rintro ⟨p, h1, h2⟩
    exact ⟨p, L.prods_complete p, by rw [h1, h2]⟩

theorem Listing.mem_prs' (pr : N × List (MixedSymbol N α)) :
    pr ∈ L.prs ↔ G.toMixedRules pr.1 pr.2 := L.mem_prs G pr.1 pr.2

/-- The support of the existing finite front end. -/
abbrev frontSupport : Finset (FrontEndState N α) :=
  (indexedNormalizationSupportCertificate G).support

theorem old_mem_frontSupport (X : N ⊕ α) :
    BinarizedState.old X ∈ frontSupport G :=
  indexedClosedFrontSupport_old_mem G X

theorem suffix_mem_frontSupport_iff (l : List (MixedSymbol N α)) :
    BinarizedState.suffix l ∈ frontSupport G ↔
      ∃ pr, pr ∈ L.prs ∧ ∃ i, i < pr.2.length ∧ l = pr.2.drop i := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := indexedClosedFrontSupport_suffix_exists G l h
    refine ⟨(G.lhs o.1, G.rhs o.1), ?_, o.2.1, o.2.2, ho.symm⟩
    exact List.mem_map.mpr ⟨o.1, L.prods_complete o.1, rfl⟩
  · rintro ⟨pr, hpr, i, hi, rfl⟩
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hpr
    exact indexedClosedFrontSupport_suffix_mem G ⟨p, ⟨i, hi⟩⟩

include L in
theorem frontSupport_suffix_ne_nil {l : List (MixedSymbol N α)}
    (h : BinarizedState.suffix l ∈ frontSupport G) : l ≠ [] := by
  obtain ⟨pr, _, i, hi, rfl⟩ := (suffix_mem_frontSupport_iff G L l).mp h
  intro hnil
  rw [List.drop_eq_nil_iff] at hnil
  omega

theorem mem_states_iff (x : FrontEndState N α) :
    x ∈ (frontCodeC L.nts L.alph L.prs).1.states ↔ x ∈ frontSupport G := by
  rw [frontCode_states]
  simp only [List.mem_append, List.mem_map, mem_allSuffixStates]
  rcases x with X | l
  · refine ⟨fun _ => old_mem_frontSupport G X, fun _ => ?_⟩
    rcases X with A | a
    · exact Or.inl ⟨A, L.nts_complete A, rfl⟩
    · exact Or.inr (Or.inl ⟨a, L.alph_complete a, rfl⟩)
  · rw [suffix_mem_frontSupport_iff G L]
    constructor
    · rintro (⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨pr, hpr, i, hi, h⟩)
      · cases h
      · cases h
      · cases h; exact ⟨pr, hpr, i, hi, rfl⟩
    · rintro ⟨pr, hpr, i, hi, rfl⟩
      exact Or.inr (Or.inr ⟨pr, hpr, i, hi, rfl⟩)

theorem mem_allSuffixStates_iff (X : FrontEndState N α) :
    X ∈ allSuffixStates L.prs ↔
      (∃ l, X = BinarizedState.suffix l) ∧ X ∈ frontSupport G := by
  rw [mem_allSuffixStates]
  constructor
  · rintro ⟨pr, hpr, i, hi, rfl⟩
    exact ⟨⟨_, rfl⟩, (suffix_mem_frontSupport_iff G L _).mpr ⟨pr, hpr, i, hi, rfl⟩⟩
  · rintro ⟨⟨l, rfl⟩, h⟩
    obtain ⟨pr, hpr, i, hi, rfl⟩ := (suffix_mem_frontSupport_iff G L l).mp h
    exact ⟨pr, hpr, i, hi, rfl⟩

/-- Shorthand for the existing finite front-end grammar. -/
abbrev Gf : BinaryNullableGrammar {x // x ∈ frontSupport G} α :=
  indexedFiniteFrontEndGrammar G

theorem closed_children {x y z : FrontEndState N α} (hx : x ∈ frontSupport G)
    (h : (frontEndBinaryGrammar G.toMixedRules).binaryRule x y z) :
    y ∈ frontSupport G ∧ z ∈ frontSupport G :=
  (indexedNormalizationSupportCertificate G).closed.binaryChildren hx h

theorem closed_unit {x y : FrontEndState N α} (hx : x ∈ frontSupport G)
    (h : (frontEndBinaryGrammar G.toMixedRules).unitRule x y) : y ∈ frontSupport G :=
  (indexedNormalizationSupportCertificate G).closed.unitChild hx h

/-- **The written front end is exactly the existing finite front-end grammar.** -/
theorem codeMatches_indexed :
    CodeMatches (P := fun x => x ∈ frontSupport G)
      (frontCodeC L.nts L.alph L.prs).1 (Gf G) where
  states x := mem_states_iff G L x
  term x a := by
    show _ ↔ ∃ hx, (frontEndBinaryGrammar G.toMixedRules).terminalRule x a
    rw [frontCode_term, List.mem_append, forListC_const_mem, List.mem_map]
    constructor
    · rintro (⟨pr, hpr, hm⟩ | ⟨b, _, he⟩)
      · obtain ⟨h1, rfl⟩ := (mem_termOfProd pr x a).mp hm
        refine ⟨old_mem_frontSupport G _, (frontEnd_terminal_iff _ _ a).mpr
          (Or.inl ⟨pr.1, rfl, ?_⟩)⟩
        have := (L.mem_prs' G pr).mp hpr
        rwa [h1] at this
      · simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨old_mem_frontSupport G _, (frontEnd_terminal_iff _ _ b).mpr (Or.inr rfl)⟩
    · rintro ⟨_, h⟩
      rcases (frontEnd_terminal_iff _ x a).mp h with ⟨B, rfl, hR⟩ | rfl
      · exact Or.inl ⟨(B, [Sum.inr a]), (L.mem_prs G B _).mpr hR,
          (mem_termOfProd _ _ a).mpr ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨a, L.alph_complete a, rfl⟩
  bin x y z := by
    show _ ↔ ∃ hx hy hz, (frontEndBinaryGrammar G.toMixedRules).binaryRule x y z
    rw [frontCode_bin, List.mem_append, forListC_const_mem, forListC_const_mem]
    constructor
    · intro hm
      have hrule : x ∈ frontSupport G ∧
          (frontEndBinaryGrammar G.toMixedRules).binaryRule x y z := by
        rcases hm with ⟨pr, hpr, hm⟩ | ⟨X, hX, hm⟩
        · obtain ⟨rfl, hshape⟩ := (mem_binOfProd pr x y z).mp hm
          refine ⟨old_mem_frontSupport G _, (frontEnd_binary_iff _ _ _ _).mpr
            (Or.inl ⟨pr.1, pr.2, rfl, (L.mem_prs' G pr).mp hpr, hshape⟩)⟩
        · obtain ⟨rfl, hshape⟩ := (mem_binOfSuffix X x y z).mp hm
          refine ⟨((mem_allSuffixStates_iff G L x).mp hX).2,
            (frontEnd_binary_iff _ _ _ _).mpr (Or.inr hshape)⟩
      obtain ⟨hx, hr⟩ := hrule
      obtain ⟨hy, hz⟩ := closed_children G hx hr
      exact ⟨hx, hy, hz, hr⟩
    · rintro ⟨hx, _, _, h⟩
      rcases (frontEnd_binary_iff _ x y z).mp h with ⟨B, rhs, rfl, hR, hshape⟩ | hsuf | hsuf
      · exact Or.inl ⟨(B, rhs), (L.mem_prs G B rhs).mpr hR,
          (mem_binOfProd _ _ _ _).mpr ⟨rfl, hshape⟩⟩
      · obtain ⟨B, C, rfl, hy, hz⟩ := hsuf
        exact Or.inr ⟨_, (mem_allSuffixStates_iff G L _).mpr ⟨⟨_, rfl⟩, hx⟩,
          (mem_binOfSuffix _ _ _ _).mpr ⟨rfl, Or.inl ⟨B, C, rfl, hy, hz⟩⟩⟩
      · obtain ⟨B, C, D, rest, rfl, hy, hz⟩ := hsuf
        exact Or.inr ⟨_, (mem_allSuffixStates_iff G L _).mpr ⟨⟨_, rfl⟩, hx⟩,
          (mem_binOfSuffix _ _ _ _).mpr ⟨rfl, Or.inr ⟨B, C, D, rest, rfl, hy, hz⟩⟩⟩
  unit x y := by
    show _ ↔ ∃ hx hy, (frontEndBinaryGrammar G.toMixedRules).unitRule x y
    rw [frontCode_unit, List.mem_append, forListC_const_mem, forListC_const_mem]
    constructor
    · intro hm
      have hrule : x ∈ frontSupport G ∧
          (frontEndBinaryGrammar G.toMixedRules).unitRule x y := by
        rcases hm with ⟨pr, hpr, hm⟩ | ⟨X, hX, hm⟩
        · obtain ⟨C, h1, rfl, rfl⟩ := (mem_unitOfProd pr x y).mp hm
          refine ⟨old_mem_frontSupport G _, (frontEnd_unit_iff _ _ _).mpr
            (Or.inl ⟨pr.1, C, rfl, ?_, rfl⟩)⟩
          have := (L.mem_prs' G pr).mp hpr
          rwa [h1] at this
        · obtain ⟨rfl, hshape⟩ := (mem_unitOfSuffix X x y).mp hm
          exact ⟨((mem_allSuffixStates_iff G L x).mp hX).2,
            (frontEnd_unit_iff _ _ _).mpr (Or.inr hshape)⟩
      obtain ⟨hx, hr⟩ := hrule
      exact ⟨hx, closed_unit G hx hr, hr⟩
    · rintro ⟨hx, _, h⟩
      rcases (frontEnd_unit_iff _ x y).mp h with ⟨B, C, rfl, hR, rfl⟩ | hsuf
      · exact Or.inl ⟨(B, [Sum.inl C]), (L.mem_prs G B _).mpr hR,
          (mem_unitOfProd _ _ _).mpr ⟨C, rfl, rfl, rfl⟩⟩
      · obtain ⟨B, rfl, hy⟩ := hsuf
        exact Or.inr ⟨_, (mem_allSuffixStates_iff G L _).mpr ⟨⟨_, rfl⟩, hx⟩,
          (mem_unitOfSuffix _ _ _).mpr ⟨rfl, B, rfl, hy⟩⟩
  eps x := by
    show _ ↔ ∃ hx, (frontEndBinaryGrammar G.toMixedRules).epsilonRule x
    rw [frontCode_eps, forListC_const_mem]
    constructor
    · rintro ⟨pr, hpr, hm⟩
      obtain ⟨h1, rfl⟩ := (mem_epsOfProd pr x).mp hm
      refine ⟨old_mem_frontSupport G _, (frontEnd_epsilon_iff _ _).mpr
        (Or.inl ⟨pr.1, rfl, ?_⟩)⟩
      have := (L.mem_prs' G pr).mp hpr
      rwa [h1] at this
    · rintro ⟨hx, h⟩
      rcases (frontEnd_epsilon_iff _ x).mp h with ⟨B, rfl, hR⟩ | rfl
      · exact ⟨(B, []), (L.mem_prs G B []).mpr hR, (mem_epsOfProd _ _).mpr ⟨rfl, rfl⟩⟩
      · exact absurd rfl (frontSupport_suffix_ne_nil G L hx)


/-! ### Input scale and operation count -/

theorem length_eq_card_of_listing {β : Type*} [Fintype β] [DecidableEq β] (l : List β)
    (hc : ∀ b, b ∈ l) (hn : l.Nodup) : l.length = Fintype.card β := by
  rw [← List.toFinset_card_of_nodup hn]
  have : l.toFinset = Finset.univ :=
    Finset.eq_univ_iff_forall.mpr (fun b => List.mem_toFinset.mpr (hc b))
  rw [this, Finset.card_univ]

/-- For duplicate-free complete listings the list size is the paper's encoding size. -/
theorem inputScale_eq_normalizationScale :
    inputScale L.nts L.alph L.prs = G.normalizationScale := by
  classical
  unfold inputScale IndexedMixedCFG.normalizationScale IndexedMixedCFG.totalRhsLength
  have h1 := length_eq_card_of_listing L.nts L.nts_complete L.nts_nodup
  have h2 := length_eq_card_of_listing L.alph L.alph_complete L.alph_nodup
  have h3 := length_eq_card_of_listing L.prods L.prods_complete L.prods_nodup
  have h4 : (L.prs.map (fun pr => pr.2.length)).sum = ∑ p : P, (G.rhs p).length := by
    unfold Listing.prs
    rw [List.map_map]
    have hu : L.prods.toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr (fun p => List.mem_toFinset.mpr (L.prods_complete p))
    rw [← hu, List.sum_toFinset _ L.prods_nodup]
    rfl
  have h5 : L.prs.length = L.prods.length := by simp [Listing.prs]
  omega

theorem start_mem_states (A : N) :
    BinarizedState.old (Sum.inl A) ∈ (frontCodeC L.nts L.alph L.prs).1.states :=
  (mem_states_iff G L _).mpr (old_mem_frontSupport G _)

/-- **Operation count of the executable normalizer.** -/
theorem normalizeSSBNF_steps_le (A : N) :
    (normalizeSSBNF L.nts L.alph L.prs A).2 ≤ 900 * (G.normalizationScale + 1) ^ 6 := by
  have hfront := frontCodeC_snd_le L.nts L.alph L.prs
  have htrace := normalizeTrace_steps_le (BinarizedState.old (Sum.inl A))
    stateEqC_correct (codeMatches_indexed G L).wf
    (frontCode_sizeBound L.nts L.alph L.prs) (frontCode_ceqBound L.nts L.alph L.prs)
    (start_mem_states G L A)
  rw [inputScale_eq_normalizationScale G L] at hfront htrace
  show (frontCodeC L.nts L.alph L.prs).2 + (normalizeTrace stateEqC
      (frontCodeC L.nts L.alph L.prs).1 (BinarizedState.old (Sum.inl A))).steps ≤ _
  set n := G.normalizationScale
  have e1 : 400 * ((n + 1) ^ 5 * (n + 1 + 1)) ≤ 800 * (n + 1) ^ 6 := by
    have : (n + 1) ^ 5 * (n + 1 + 1) ≤ (n + 1) ^ 5 * (2 * (n + 1)) :=
      Nat.mul_le_mul_left _ (by omega)
    calc 400 * ((n + 1) ^ 5 * (n + 1 + 1)) ≤ 400 * ((n + 1) ^ 5 * (2 * (n + 1))) := by omega
      _ = 800 * (n + 1) ^ 6 := by ring
  have e2 : 60 * (n + 1) ≤ 60 * (n + 1) ^ 6 := by
    have : n + 1 ≤ (n + 1) ^ 6 := by
      calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

/-! ### The paper-facing theorem -/

/-- The start state of the existing package (old copy of the source start). -/
noncomputable abbrev pkgStart (A : N)
    (hprod : ∃ u : Word α, u ∈ LeastClosedLanguage G.toMixedRules A ∧ u ≠ []) :
    ProductiveUnitFreeState (Gf G) :=
  indexedProductiveUnitFreeState_of_nonempty G A hprod

theorem pkgStart_raw (A : N)
    (hprod : ∃ u : Word α, u ∈ LeastClosedLanguage G.toMixedRules A ∧ u ≠ []) :
    (pkgStart G A hprod).1.1 = BinarizedState.old (Sum.inl A) := rfl

/-- The trace of the normalizer on the indexed input. -/
abbrev idxTrace (A : N) : Trace (FrontEndState N α) α :=
  normalizeTrace stateEqC (frontCodeC L.nts L.alph L.prs).1 (BinarizedState.old (Sum.inl A))

theorem normalizeSSBNF_fst (A : N) :
    (normalizeSSBNF L.nts L.alph L.prs A).1 = (idxTrace G L A).out := rfl

/--
**`prop:thick-ssbnf-normal`, executable form.**  For a finite CFG given by
duplicate-free complete listings, a start nonterminal `A` with a nonempty word,
and the source thickness hypothesis `τR`, the executable normalizer
`normalizeSSBNF` writes a reduced separated-start SSBNF grammar such that

1. it generates exactly `L(G, A)` (with the start ε flag);
2. its nonterminals, terminal rules and binary rules are exactly those of the
   reduced SSBNF grammar `Nf` of the existing `indexed_proposition74_full_package`;
3. the distinct nonterminals / terminal rules / binary rules number at most
   `indexedSSBNFGrammarSizeEnvelope n` (`n = G.normalizationScale`), and the
   written lists have length at most `n`, `n³`, `n³`;
4. every written nonterminal is reachable from the start in the written grammar
   and derives a word of length at most `ssbnfThicknessEnvelope 1 1 n τR`
   `= 1 + n² · thicknessBar τR`;
5. the normalizer runs in at most `900 · (n + 1)^6` steps.
-/
theorem prop_thickSSBNFNormal_executable (A : N)
    (hprod : ∃ u : Word α, u ∈ LeastClosedLanguage G.toMixedRules A ∧ u ≠ [])
    (τR : Nat) (hn : 0 < G.normalizationScale)
    (hsource : YieldBound (fun B => LeastClosedLanguage G.toMixedRules B) τR) :
    let out := (normalizeSSBNF L.nts L.alph L.prs A).1
    let start := pkgStart G A hprod
    let Nf := ReducedUnitFreeState (Gf G) start
    -- (1) language
    UntypedStartLanguage (codeTerminalRule out) (codeBinaryRule out) (codeStartRule out)
        (out.epsilon = true) = LeastClosedLanguage G.toMixedRules A
    -- (2) exactly the existing reduced grammar
    ∧ (∀ x, x ∈ out.nonterminals ↔ ∃ X : Nf, X.1.1.1 = x)
    ∧ (∀ x a, (x, a) ∈ out.terminal ↔
        ∃ X : Nf, X.1.1.1 = x ∧ reducedSSBNFTerminalRule (Gf G) start X a)
    ∧ (∀ x y z, (x, y, z) ∈ out.binary ↔
        ∃ X Y Z : Nf, X.1.1.1 = x ∧ Y.1.1.1 = y ∧ Z.1.1.1 = z ∧
          reducedSSBNFBinaryRule (Gf G) start X Y Z)
    ∧ out.start = some (BinarizedState.old (Sum.inl A))
    -- (3) size
    ∧ (@Fintype.card Nf (Fintype.ofFinite _)) ≤
        indexedSSBNFGrammarSizeEnvelope G.normalizationScale
    ∧ (@Fintype.card (UntypedTerminalRuleIndex (reducedSSBNFTerminalRule (Gf G) start))
        (Fintype.ofFinite _)) ≤ indexedSSBNFGrammarSizeEnvelope G.normalizationScale
    ∧ (@Fintype.card (UntypedBinaryRuleIndex (reducedSSBNFBinaryRule (Gf G) start))
        (Fintype.ofFinite _)) ≤ indexedSSBNFGrammarSizeEnvelope G.normalizationScale
    ∧ out.nonterminals.length ≤ G.normalizationScale
    ∧ out.terminal.length ≤ G.normalizationScale ^ 3
    ∧ out.binary.length ≤ G.normalizationScale ^ 3
    -- (4) reduced and thin
    ∧ (∀ x, x ∈ out.nonterminals →
        CodeReachable out (BinarizedState.old (Sum.inl A)) x ∧
        ∃ z : Word α, UntypedDerives (codeTerminalRule out) (codeBinaryRule out) x z ∧
          z.length ≤ ssbnfThicknessEnvelope 1 1 G.normalizationScale τR)
    ∧ ssbnfThicknessEnvelope 1 1 G.normalizationScale τR =
        1 + G.normalizationScale ^ 2 * thicknessBar τR
    -- (5) time
    ∧ (normalizeSSBNF L.nts L.alph L.prs A).2 ≤ 900 * (G.normalizationScale + 1) ^ 6 := by
  intro out start Nf
  have hc := stateEqC_correct (N := N) (α := α)
  have cm := codeMatches_indexed G L
  have hs : start.1.1 = BinarizedState.old (Sum.inl A) := rfl
  have pkg := indexed_proposition74_full_package G A hprod τR hn hsource
  obtain ⟨hlang, hN, hT, hB, hthick, henv⟩ := pkg
  have hout : out = (idxTrace G L A).out := rfl
  -- size facts of the trace
  have hwf := cm.wf
  have hsz := frontCode_sizeBound L.nts L.alph L.prs
  have hb := frontCode_ceqBound L.nts L.alph L.prs
  have hsm := start_mem_states G L A
  rw [inputScale_eq_normalizationScale G L] at hsz hb
  set n := G.normalizationScale with hn_def
  have hreachF := trace_reach_facts (BinarizedState.old (Sum.inl A)) hc hwf hsz hb hsm
  have hutF := trace_uterm_facts (BinarizedState.old (Sum.inl A)) hc hwf hsz hb
  have hpbF := trace_pbin_facts (BinarizedState.old (Sum.inl A)) hc hwf hsz hb
  have hOut := trace_out_eq hc cm start hs
  refine ⟨?_, ?_, ?_, ?_, ?_, hN, hT, hB, ?_, ?_, ?_, ?_, henv, ?_⟩
  · -- (1)
    rw [hout, codeStartLanguage_eq hc cm start hs]
    have hnull : BinaryNullable (Gf G) start.1 ↔ [] ∈ LeastClosedLanguage G.toMixedRules A :=
      indexedFiniteFrontEnd_old_language_iff_source G A []
    rw [show BinaryNullable (Gf G) start.1 = ([] ∈ LeastClosedLanguage G.toMixedRules A) from
      propext hnull]
    exact hlang
  · exact out_nonterminal_iff hc cm start hs
  · exact out_terminal_iff hc cm start hs
  · exact out_binary_iff hc cm start hs
  · exact out_start_eq hc cm start hs
  · rw [hout, hOut]; exact hreachF.2
  · rw [hout, hOut]
    show (outTermC stateEqC _ _).1.length ≤ _
    refine le_trans (filterC_length_le _ _) (le_trans hutF.2 (le_of_eq (by ring)))
  · rw [hout, hOut]
    show (outBinC stateEqC _ _).1.length ≤ _
    refine le_trans (filterC_length_le _ _) (le_trans hpbF.2 (le_of_eq (by ring)))
  · intro x hx
    refine ⟨out_reachable hc cm start hs x hx, ?_⟩
    obtain ⟨X, rfl⟩ := (out_nonterminal_iff hc cm start hs x).mp hx
    obtain ⟨z, hz, hlen⟩ := hthick X
    exact ⟨z, (codeDerives_iff hc cm start hs _ z).mpr ⟨X, rfl, hz⟩, hlen⟩
  · exact normalizeSSBNF_steps_le G L A


/--
**The degenerate case.**  If the start nonterminal has no nonempty word, the
normalizer writes no nonterminal, no rule and no start rule, and the written
grammar (only the ε flag) still generates exactly `L(G, A)`.  Together with
`prop_thickSSBNFNormal_executable`, the executable normalizer is correct on
every input.
-/
theorem prop_thickSSBNFNormal_executable_degenerate (A : N)
    (hnone : ¬ ∃ u : Word α, u ∈ LeastClosedLanguage G.toMixedRules A ∧ u ≠ []) :
    let out := (normalizeSSBNF L.nts L.alph L.prs A).1
    out.nonterminals = [] ∧ out.terminal = [] ∧ out.binary = [] ∧ out.start = none ∧
    UntypedStartLanguage (codeTerminalRule out) (codeBinaryRule out) (codeStartRule out)
        (out.epsilon = true) = LeastClosedLanguage G.toMixedRules A := by
  intro out
  have hc := stateEqC_correct (N := N) (α := α)
  have cm := codeMatches_indexed G L
  have hnp : (memC stateEqC (BinarizedState.old (Sum.inl A)) (idxTrace G L A).prod).1 = false := by
    rw [memC_fst hc, decide_eq_false_iff_not]
    intro hmem
    rw [trace_prod_iff hc cm] at hmem
    obtain ⟨hx, w, d⟩ := hmem
    apply hnone
    have hE := unitFreeDerives_to_epsilonFree (Gf G) d
    have hne := epsilonFreeDerives_nonempty (Gf G) hE
    have hB := epsilonFreeDerives_to_binaryNullable (Gf G) hE
    exact ⟨w, (indexedFiniteFrontEnd_old_language_iff_source G A w).mp hB, hne⟩
  have hout : out = SSBNFCode.mk [] [] [] none
      (memC stateEqC (BinarizedState.old (Sum.inl A)) (idxTrace G L A).null).1 := by
    show (idxTrace G L A).out = _
    rw [trace_out, hnp]
    rfl
  have heps : (memC stateEqC (BinarizedState.old (Sum.inl A)) (idxTrace G L A).null).1 = true ↔
      [] ∈ LeastClosedLanguage G.toMixedRules A := by
    rw [memC_fst hc, decide_eq_true_iff, trace_null, mem_null_iff hc cm]
    constructor
    · rintro ⟨_, h⟩
      exact (indexedFiniteFrontEnd_old_language_iff_source G A []).mp h
    · intro h
      exact ⟨old_mem_frontSupport G _,
        (indexedFiniteFrontEnd_old_language_iff_source G A []).mpr h⟩
  refine ⟨by rw [hout], by rw [hout], by rw [hout], by rw [hout], ?_⟩
  ext w
  show UntypedStartDerives _ _ _ _ w ↔ w ∈ LeastClosedLanguage G.toMixedRules A
  constructor
  · intro h
    cases h with
    | @nonempty x _ hstart _ =>
        have : out.start = some x := hstart
        rw [hout] at this
        cases this
    | epsilon h =>
        have : out.epsilon = true := h
        rw [hout] at this
        exact heps.mp this
  · intro hw
    by_cases hne : w = []
    · subst hne
      refine UntypedStartDerives.epsilon ?_
      show out.epsilon = true
      rw [hout]
      exact heps.mpr hw
    · exact absurd ⟨w, hw, hne⟩ hnone

end Indexed

end SSBNFNorm
end TCS1
end LeanCfgProject
