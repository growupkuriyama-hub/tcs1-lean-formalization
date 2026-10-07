import LeanCfgProject.TCS1.V115InverseHomClosure
import LeanCfgProject.TCS1.LeastClosedCFGLanguage
import LeanCfgProject.TCS1.FiniteCFGEncoding

/-!
# TCS #1 v115: constructive homomorphic image of a CFG

A standard ingredient for the remaining CFL part of Proposition 3.2(iii).

For an arbitrary mixed CFG R over alpha and a letter-to-word map
psi : alpha -> beta*, map every terminal occurrence a in every RHS to
the literal terminal word psi(a), leaving nonterminals unchanged.
We prove from the least-closed semantics that the resulting grammar
generates exactly the homomorphic image of every source nonterminal language.

This theorem permits erasing images psi(a)=epsilon. No closure theorem,
new axiom, or placeholder proof is assumed.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w z

section V115CFGHomomorphicImage

variable {N : Type u} {α : Type v} {β : Type w}

/-- Expand terminals of one mixed RHS by a word homomorphism. -/
def v115MapMixedRhs
    (ψ : α → Word β) :
    List (MixedSymbol N α) →
      List (MixedSymbol N β)
  | [] => []
  | Sum.inl A :: rhs =>
      Sum.inl A :: v115MapMixedRhs ψ rhs
  | Sum.inr a :: rhs =>
      (ψ a).map Sum.inr ++ v115MapMixedRhs ψ rhs

/-- Predicate presentation of the homomorphic-image grammar. -/
def v115HomImageRule
    (R : MixedRules N α)
    (ψ : α → Word β) :
    MixedRules N β :=
  fun A rhs' =>
    ∃ rhs,
      R A rhs ∧
      rhs' = v115MapMixedRhs ψ rhs

/-- Semantic homomorphic image of a family of nonterminal languages. -/
def v115HomImageFamily
    (ψ : α → Word β)
    (L : N → Set (Word α)) :
    N → Set (Word β) :=
  fun A =>
    {v | ∃ w, w ∈ L A ∧
      v115WordSubstitution ψ w = v}

/--
A literal list of target terminals realizes exactly itself followed by
whatever the remaining RHS realizes.
-/
theorem v115_rhsRealizes_terminalList_append
    (L : N → Set (Word β))
    (pref : Word β)
    (rhs : List (MixedSymbol N β))
    (v : Word β) :
    RhsRealizes L
        (pref.map Sum.inr ++ rhs) v
      ↔
    ∃ tail,
      v = pref ++ tail ∧
      RhsRealizes L rhs tail := by
  induction pref generalizing v with
  | nil =>
      constructor
      · intro h
        exact ⟨v, by simp, by simpa using h⟩
      · rintro ⟨tail, hv, htail⟩
        have hvt : v = tail := by
          simpa using hv
        subst v
        simpa using htail
  | cons a restPref ih =>
      constructor
      · intro h
        change
          ∃ rest,
            v = a :: rest ∧
            RhsRealizes L
              (restPref.map Sum.inr ++ rhs) rest at h
        rcases h with ⟨rest, rfl, hrest⟩
        rcases (ih rest).mp hrest with
          ⟨tail, hrestEq, htail⟩
        subst rest
        exact ⟨tail, by simp, htail⟩
      · rintro ⟨tail, hv, htail⟩
        change
          ∃ rest,
            v = a :: rest ∧
            RhsRealizes L
              (restPref.map Sum.inr ++ rhs) rest
        refine ⟨restPref ++ tail, ?_, ?_⟩
        · simpa using hv
        · exact (ih (restPref ++ tail)).mpr
            ⟨tail, rfl, htail⟩

/--
RHS semantic compatibility for homomorphic image.

A transformed RHS realizes v in the image interpretation iff the source RHS
realizes some w whose homomorphic image is v.
-/
theorem v115_mapMixedRhs_realizes_iff
    (ψ : α → Word β)
    (L : N → Set (Word α))
    (rhs : List (MixedSymbol N α))
    (v : Word β) :
    RhsRealizes
        (v115HomImageFamily ψ L)
        (v115MapMixedRhs ψ rhs) v
      ↔
    ∃ w,
      RhsRealizes L rhs w ∧
      v115WordSubstitution ψ w = v := by
  induction rhs generalizing v with
  | nil =>
      constructor
      · intro hv
        change v = [] at hv
        refine ⟨[], rfl, ?_⟩
        simpa [v115WordSubstitution] using hv.symm
      · rintro ⟨w, hw, hmap⟩
        change w = [] at hw
        subst w
        change v = []
        simpa [v115WordSubstitution] using hmap.symm
  | cons s rhs ih =>
      cases s with
      | inl A =>
          constructor
          · intro hv
            rcases hv with
              ⟨u, tail, hvt, hu, htail⟩
            rcases hu with ⟨x, hxL, hxMap⟩
            rcases (ih tail).mp htail with
              ⟨y, hyReal, hyMap⟩
            refine ⟨x ++ y, ?_, ?_⟩
            · exact ⟨x, y, rfl, hxL, hyReal⟩
            · rw [v115WordSubstitution_append,
                hxMap, hyMap]
              exact hvt.symm
          · rintro ⟨w, hw, hmap⟩
            rcases hw with
              ⟨x, y, rfl, hxL, hyReal⟩
            have htail :=
              (ih (v115WordSubstitution ψ y)).mpr
                ⟨y, hyReal, rfl⟩
            refine
              ⟨v115WordSubstitution ψ x,
               v115WordSubstitution ψ y,
               ?_, ?_, htail⟩
            · simpa [v115WordSubstitution_append]
                using hmap.symm
            · exact ⟨x, hxL, rfl⟩
      | inr a =>
          constructor
          · intro hv
            have hsplit :=
              (v115_rhsRealizes_terminalList_append
                (v115HomImageFamily ψ L)
                (ψ a)
                (v115MapMixedRhs ψ rhs)
                v).mp hv
            rcases hsplit with
              ⟨tail, hvt, htail⟩
            rcases (ih tail).mp htail with
              ⟨y, hyReal, hyMap⟩
            refine ⟨a :: y, ?_, ?_⟩
            · exact ⟨y, rfl, hyReal⟩
            · change ψ a ++
                v115WordSubstitution ψ y = v
              rw [hyMap]
              exact hvt.symm
          · rintro ⟨w, hw, hmap⟩
            rcases hw with ⟨y, rfl, hyReal⟩
            rw [← hmap]
            apply
              (v115_rhsRealizes_terminalList_append
                (v115HomImageFamily ψ L)
                (ψ a)
                (v115MapMixedRhs ψ rhs)
                (v115WordSubstitution ψ (a :: y))).mpr
            refine
              ⟨v115WordSubstitution ψ y, ?_, ?_⟩
            · rfl
            · exact
                (ih (v115WordSubstitution ψ y)).mpr
                  ⟨y, hyReal, rfl⟩

/-- The least-generated family is itself closed under its grammar rules. -/
theorem v115_leastClosedLanguage_closed
    (R : MixedRules N α) :
    GrammarClosed R (LeastClosedLanguage R) := by
  intro A w hw
  intro L hL
  have hsub :
      ∀ B, LeastClosedLanguage R B ⊆ L B := by
    intro B z hz
    exact hz L hL
  have hw' :
      w ∈ RuleStepLanguage R L A :=
    ruleStepLanguage_mono R hsub A hw
  exact hL A hw'

/-- The image of the least source family is closed under the image grammar. -/
theorem v115_homImageFamily_closed
    (R : MixedRules N α)
    (ψ : α → Word β) :
    GrammarClosed
      (v115HomImageRule R ψ)
      (v115HomImageFamily ψ
        (LeastClosedLanguage R)) := by
  intro A v hv
  rcases hv with ⟨rhs', hRule, hReal⟩
  rcases hRule with ⟨rhs, hR, rfl⟩
  rcases
      (v115_mapMixedRhs_realizes_iff
        ψ (LeastClosedLanguage R) rhs v).mp hReal
    with ⟨w, hwReal, hmap⟩
  refine ⟨w, ?_, hmap⟩
  exact
    v115_leastClosedLanguage_closed R A
      ⟨rhs, hR, hwReal⟩

/-- Pull a target interpretation back through the word homomorphism. -/
def v115HomPreimageFamily
    (ψ : α → Word β)
    (Q : N → Set (Word β)) :
    N → Set (Word α) :=
  fun A => {w | v115WordSubstitution ψ w ∈ Q A}

/--
A closed interpretation of the image grammar pulls back to a closed
interpretation of the source grammar.
-/
theorem v115_homPreimageFamily_closed
    (R : MixedRules N α)
    (ψ : α → Word β)
    (Q : N → Set (Word β))
    (hQ : GrammarClosed
      (v115HomImageRule R ψ) Q) :
    GrammarClosed R
      (v115HomPreimageFamily ψ Q) := by
  intro A w hw
  apply hQ A
  rcases hw with ⟨rhs, hR, hReal⟩
  refine
    ⟨v115MapMixedRhs ψ rhs,
      ⟨rhs, hR, rfl⟩, ?_⟩
  have hImage :
      RhsRealizes
        (v115HomImageFamily ψ
          (v115HomPreimageFamily ψ Q))
        (v115MapMixedRhs ψ rhs)
        (v115WordSubstitution ψ w) :=
    (v115_mapMixedRhs_realizes_iff
      ψ (v115HomPreimageFamily ψ Q)
      rhs (v115WordSubstitution ψ w)).mpr
      ⟨w, hReal, rfl⟩
  have hsub :
      ∀ B,
        v115HomImageFamily ψ
            (v115HomPreimageFamily ψ Q) B
          ⊆ Q B := by
    intro B z hz
    rcases hz with ⟨x, hxQ, hxz⟩
    change v115WordSubstitution ψ x ∈ Q B at hxQ
    rw [← hxz]
    exact hxQ
  exact rhsRealizes_mono hsub hImage

/--
Exact homomorphic-image closure for arbitrary mixed CFG semantics.
Erasing letter images are allowed.
-/
theorem v115_homImage_leastClosedLanguage
    (R : MixedRules N α)
    (ψ : α → Word β)
    (A : N) :
    LeastClosedLanguage
        (v115HomImageRule R ψ) A
      =
    v115HomImageFamily ψ
      (LeastClosedLanguage R) A := by
  apply Set.ext
  intro v
  constructor
  · intro hv
    exact
      hv
        (v115HomImageFamily ψ
          (LeastClosedLanguage R))
        (v115_homImageFamily_closed R ψ)
  · rintro ⟨w, hw, hmap⟩
    intro Q hQ
    have hPre :
        GrammarClosed R
          (v115HomPreimageFamily ψ Q) :=
      v115_homPreimageFamily_closed R ψ Q hQ
    have hwQ :
        v115WordSubstitution ψ w ∈ Q A :=
      hw (v115HomPreimageFamily ψ Q) hPre
    simpa [hmap] using hwQ

end V115CFGHomomorphicImage

section V115IndexedCFGHomomorphicImage

variable {N : Type u} {α : Type v} {β : Type w} {P : Type z}

/-- Finite indexed grammar obtained by mapping every terminal RHS occurrence. -/
def IndexedMixedCFG.v115HomImage
    (G : IndexedMixedCFG N α P)
    (ψ : α → Word β) :
    IndexedMixedCFG N β P where
  lhs := G.lhs
  rhs p := v115MapMixedRhs ψ (G.rhs p)

/-- The indexed presentation has exactly the predicate image rules above. -/
theorem indexed_v115HomImage_rules
    (G : IndexedMixedCFG N α P)
    (ψ : α → Word β) :
    (G.v115HomImage ψ).toMixedRules =
      v115HomImageRule G.toMixedRules ψ := by
  funext A rhs'
  apply propext
  constructor
  · rintro ⟨p, hpA, hpRhs⟩
    refine ⟨G.rhs p, ?_, ?_⟩
    · exact ⟨p, hpA, rfl⟩
    · exact hpRhs.symm
  · rintro ⟨rhs, ⟨p, hpA, hpRhs⟩, hmap⟩
    subst rhs
    exact ⟨p, hpA, hmap.symm⟩

/-- Finite indexed source grammars are constructively closed under homomorphic image. -/
theorem indexed_v115HomImage_language
    (G : IndexedMixedCFG N α P)
    (ψ : α → Word β)
    (A : N) :
    LeastClosedLanguage
        (G.v115HomImage ψ).toMixedRules A
      =
    v115HomImageFamily ψ
      (LeastClosedLanguage G.toMixedRules) A := by
  rw [indexed_v115HomImage_rules]
  exact
    v115_homImage_leastClosedLanguage
      G.toMixedRules ψ A

end V115IndexedCFGHomomorphicImage

end TCS1
end LeanCfgProject
