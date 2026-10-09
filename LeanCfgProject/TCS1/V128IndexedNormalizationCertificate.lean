import LeanCfgProject.TCS1.IndexedConcreteSSBNFNormalization

/-!
# TCS #1 v128: concrete indexed normalization quantitative certificate

This module packages *proved* finite-front-end cardinality and reduced
separated-start yield bounds at the actual normalized grammar. In particular,
the witness for each surviving non-start symbol is obtained from the indexed
source grammar, not assumed as an abstract `hshort` parameter.

This is one normalization bridge for `cor:li-thickness`.  The separate
identification of these derivations with the `UntypedDerives` presentation
used by the characteristic-data facade, and the full source-size and language
transfer package, remain explicit tasks.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section V128IndexedNormalizationCertificate

variable {N : Type u} {α : Type v} {P : Type w}
variable [Fintype N] [Fintype α] [Fintype P]
variable [DecidableEq N] [DecidableEq α]

/-- An indexed source grammar gives both a concrete finite-front-end
cardinality bound and a bounded yield for every surviving non-start symbol
of its separated-start SSBNF normalization. -/
theorem v128_indexed_normalization_size_and_nonstart_witnesses
    (G : IndexedMixedCFG N α P)
    (τR : Nat)
    (hn : 0 < G.normalizationScale)
    (hsource :
      YieldBound
        (fun A => LeastClosedLanguage G.toMixedRules A)
        τR)
    (start :
      ProductiveUnitFreeState
        (indexedFiniteFrontEndGrammar G))
    (keepEmpty : Prop) :
    Fintype.card
        (SupportedState
          (indexedNormalizationSupportCertificate G).support)
      ≤ G.normalizationScale
    ∧
    (∀ A :
      ReducedUnitFreeState
        (indexedFiniteFrontEndGrammar G) start,
      ∃ w : List α,
        BinaryNullableDerives
          (separatedStartGrammar
            (indexedFiniteFrontEndGrammar G)
            start keepEmpty)
          (some A) w
        ∧ w.length ≤
          1 + G.normalizationScale ^ 2 * (τR + 1)) := by
  constructor
  · exact indexedFiniteFrontEnd_card_le_scale G
  · intro A
    obtain ⟨w, hw, hlen⟩ :=
      indexed_proposition74_separatedNonstart_thickness
        G τR hn hsource start keepEmpty A
    refine ⟨w, hw, ?_⟩
    simpa [indexed_proposition74_explicit_envelope,
      thicknessBar] using hlen

end V128IndexedNormalizationCertificate

end TCS1
end LeanCfgProject
