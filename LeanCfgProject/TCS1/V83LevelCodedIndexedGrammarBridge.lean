import LeanCfgProject.TCS1.V83LevelCodedIndexedGrammar
import LeanCfgProject.TCS1.GeneralCFGDerivation

/-!
# TCS #1 v83: direct-to-indexed derivation bridge for R_n

This module starts the semantic bridge from the paper-facing derivation
relations to the actual finite indexed CFG presentation of R_n.  It proves
that every direct Z_i or A_i derivation is realized by the generic
MixedDerives semantics, and hence every word of T_n is generated from the
indexed start symbol.

The converse direction is kept separate so that the two inclusions can be
audited independently.
-/

namespace LeanCfgProject
namespace TCS1

open LevelTreeSymbol

/-- Direct Z_i derivations are realized by the indexed grammar R_n. -/
theorem levelCodeZDerives_to_indexed
    {i n : Nat}
    {w : Word LevelTreeSymbol}
    (d : LevelCodeZDerives i w)
    (hi : i ≤ n) :
    MixedDerives
      (levelCodeRIndexedGrammar n).toMixedRules
      (.z ⟨i, by omega⟩) w := by
  induction d with
  | zero =>
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinZero n))
            [Sum.inr zero] :=
        ⟨LevelCodeRProd.z0, rfl, rfl⟩
      have hd :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinZero n))
            [zero] :=
        mixedDerives_terminal
          (levelCodeRIndexedGrammar n).toMixedRules hr
      simpa [levelCodeFinZero] using hd
  | @succ i w d ih =>
      have hi' : i < n := by omega
      let fi : Fin n := ⟨i, hi'⟩
      have hchild :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinEmbed fi)) w := by
        simpa [fi, levelCodeFinEmbed] using
          (ih (show i ≤ n by omega))
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.z (levelCodeFinSucc fi))
            [Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr zero] :=
        ⟨LevelCodeRProd.zSucc fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inl (.z (levelCodeFinEmbed fi)),
              Sum.inr zero]
            [w, [zero]] :=
        MixedSymbolsDerive.nonterminal hchild
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nil))
      have hd :=
        MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc,
        List.flatten_cons] using hd

/-- Direct A_i derivations are realized by the indexed grammar R_n. -/
theorem levelCodeADerives_to_indexed
    {i n : Nat}
    {w : Word LevelTreeSymbol}
    (d : LevelCodeADerives i w)
    (hi : i ≤ n) :
    MixedDerives
      (levelCodeRIndexedGrammar n).toMixedRules
      (.a ⟨i, by omega⟩) w := by
  induction d with
  | clean0 =>
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinZero n))
            [Sum.inr l, Sum.inr a, Sum.inr r] :=
        ⟨LevelCodeRProd.a0Clean, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inr l, Sum.inr a, Sum.inr r]
            [[l], [a], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.terminal
              (MixedSymbolsDerive.nil)))
      have hd :=
        MixedDerives.rule hr hs
      simpa [levelCodeFinZero] using hd
  | @shortcut i z dz =>
      let fi : Fin (n + 1) := ⟨i, by omega⟩
      have hz :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.z fi) z := by
        simpa [fi] using
          (levelCodeZDerives_to_indexed dz hi)
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.a fi)
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z fi),
              Sum.inr d, Sum.inr r] :=
        ⟨LevelCodeRProd.aShortcut fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inr l, Sum.inr c,
              Sum.inl (.z fi),
              Sum.inr d, Sum.inr r]
            [[l], [c], z, [d], [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.terminal
            (MixedSymbolsDerive.nonterminal hz
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.terminal
                  (MixedSymbolsDerive.nil)))))
      have hd :=
        MixedDerives.rule hr hs
      simpa [fi, List.flatten_cons,
        List.append_assoc] using hd
  | @node i x y dx dy ihX ihY =>
      have hi' : i < n := by omega
      let fi : Fin n := ⟨i, hi'⟩
      have hx :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinEmbed fi)) x := by
        simpa [fi, levelCodeFinEmbed] using
          (ihX (show i ≤ n by omega))
      have hy :
          MixedDerives
            (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinEmbed fi)) y := by
        simpa [fi, levelCodeFinEmbed] using
          (ihY (show i ≤ n by omega))
      have hr :
          (levelCodeRIndexedGrammar n).toMixedRules
            (.a (levelCodeFinSucc fi))
            [Sum.inr l,
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inr r] :=
        ⟨LevelCodeRProd.aNode fi, rfl, rfl⟩
      have hs :
          MixedSymbolsDerive
            (levelCodeRIndexedGrammar n).toMixedRules
            [Sum.inr l,
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inl (.a (levelCodeFinEmbed fi)),
              Sum.inr r]
            [[l], x, y, [r]] :=
        MixedSymbolsDerive.terminal
          (MixedSymbolsDerive.nonterminal hx
            (MixedSymbolsDerive.nonterminal hy
              (MixedSymbolsDerive.terminal
                (MixedSymbolsDerive.nil))))
      have hd :=
        MixedDerives.rule hr hs
      simpa [fi, levelCodeFinSucc,
        List.flatten_cons, List.append_assoc] using hd

/-- Every T_n word is generated from the actual indexed start symbol of R_n. -/
theorem levelTreeLanguage_to_indexed_start
    (n : Nat)
    {w : Word LevelTreeSymbol}
    (hw : w ∈ LevelTreeLanguage n) :
    MixedDerives
      (levelCodeRIndexedGrammar n).toMixedRules
      (LevelCodeRNT.start) w := by
  rcases hw with ⟨t, rfl⟩
  have hA :
      MixedDerives
        (levelCodeRIndexedGrammar n).toMixedRules
        (.a (levelCodeFinTop n))
        t.serialize := by
    simpa [levelCodeFinTop] using
      (levelCodeADerives_to_indexed
        (levelTree_to_levelCodeADerives t)
        (le_rfl : n ≤ n))
  have hr :
      (levelCodeRIndexedGrammar n).toMixedRules
        (LevelCodeRNT.start)
        [Sum.inl (.a (levelCodeFinTop n))] :=
    ⟨LevelCodeRProd.start, rfl, rfl⟩
  exact mixedDerives_unit
    (levelCodeRIndexedGrammar n).toMixedRules
    hr hA

end TCS1
end LeanCfgProject
