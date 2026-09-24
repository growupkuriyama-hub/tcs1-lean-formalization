import LeanCfgProject.TCS1.DeltaStarDisplayedGrammar
import LeanCfgProject.TCS1.DeltaStarNonregular

/-!
# TCS #1 v78: semantic bridge used by the non-linearity argument

The manuscript proves that Delta-star is not linear by intersecting it with
the regular four-block language a* b* a* b*.  The intersection is exactly

  Delta Delta
    = { a^m b^m a^n b^n : m,n >= 0 },

and the cited literature supplies that Delta Delta is not linear.

This module machine-checks the exact intersection identity.  The subsequent
modules formalize the four-block DFA and the closure of finite raw-linear
presentations under DFA intersection.  The final cited theorem that Delta
Delta is not linear remains external and is exposed explicitly as a
hypothesis in the paper-facing reduction rather than encoded as an axiom.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/-- One monotone balanced block a^n b^n. -/
def balancedBlock (n : Nat) : Word Symbol :=
  List.replicate n a ++
    List.replicate n b

/-- The regular shape language a* b* a* b*, written extensionally. -/
def FourBlockLanguage : Set (Word Symbol) :=
  { w |
      ∃ p q r s : Nat,
        w =
          List.replicate p a ++
            List.replicate q b ++
              List.replicate r a ++
                List.replicate s b }

/-- Delta Delta, written as the concatenation of two balanced blocks. -/
def DoubleDeltaLanguage : Set (Word Symbol) :=
  { w |
      ∃ m n : Nat,
        w =
          balancedBlock m ++
            balancedBlock n }

/-- Two arbitrary balanced blocks are accepted by the Delta-star parser. -/
theorem two_arbitrary_blocks_mem
    (m n : Nat) :
    balancedBlock m ++
        balancedBlock n ∈ Language := by
  change
    scan .zero
        ((List.replicate m a ++
            List.replicate m b) ++
          (List.replicate n a ++
            List.replicate n b)) =
      some .zero
  rw [scan_append, scan_block]
  exact scan_block n

/-- Delta Delta is contained in both Delta-star and the four-block shape. -/
theorem doubleDelta_subset_intersection :
    DoubleDeltaLanguage ⊆
      Language ∩ FourBlockLanguage := by
  intro w hw
  rcases hw with ⟨m, n, rfl⟩
  constructor
  · exact two_arbitrary_blocks_mem m n
  · exact
      ⟨m, m, n, n,
        by simp [balancedBlock,
          List.append_assoc]⟩

/--
If an accepted four-block word has a genuine central b/a boundary, then the
prefix before that boundary is itself a complete balanced block.
-/
theorem fourBlock_central_boundary_forces_balance
    {p q r s : Nat}
    (hq : 0 < q)
    (hr : 0 < r)
    (hmem :
      List.replicate p a ++
          List.replicate q b ++
            List.replicate r a ++
              List.replicate s b ∈ Language) :
    p = q := by
  have hall :
      scan .zero
          ((List.replicate p a ++
              List.replicate q b) ++
            (List.replicate r a ++
              List.replicate s b)) =
        some .zero := by
    simpa [List.append_assoc] using hmem
  rw [scan_append] at hall
  cases hpref :
      scan .zero
        (List.replicate p a ++
          List.replicate q b) with
  | none =>
      simp [hpref] at hall
  | some mode =>
      rw [hpref] at hall
      simp only at hall
      have hpref_ne :
          List.replicate p a ++
              List.replicate q b ≠ [] := by
        intro hnil
        have hlen :=
          congrArg List.length hnil
        simp at hlen
        omega
      have hlast :
          lastSymbol?
              (List.replicate p a ++
                List.replicate q b) =
            some b :=
        lastSymbol_mixed hq
      rcases
          scan_result_of_last_b
            hpref_ne hlast hpref with
          hzero | ⟨n, hfall⟩
      · subst mode
        exact
          block_exponents_eq_of_mem
            (show
              List.replicate p a ++
                  List.replicate q b ∈ Language
              from hpref)
      · subst mode
        cases r with
        | zero =>
            omega
        | succ r =>
            rw [List.replicate_succ] at hall
            simp [scan, step] at hall

/--
Exact identity used in the manuscript's non-linearity proof:
Delta-star intersected with a* b* a* b* is Delta Delta.
-/
theorem language_inter_fourBlock_eq_doubleDelta :
    Language ∩ FourBlockLanguage =
      DoubleDeltaLanguage := by
  apply Set.Subset.antisymm
  · intro w hw
    rcases hw with ⟨hmem, hshape⟩
    rcases hshape with
      ⟨p, q, r, s, rfl⟩
    have hbal :=
      balance_mem_zero hmem
    simp only [balance_append,
      balance_replicate_a,
      balance_replicate_b] at hbal
    by_cases hq0 : q = 0
    · subst q
      have hs : s = p + r := by
        omega
      subst s
      refine ⟨p + r, 0, ?_⟩
      simp only [balancedBlock,
        List.replicate_zero,
        List.nil_append, List.append_nil,
        List.replicate_add,
        List.append_assoc]
    · by_cases hr0 : r = 0
      · subst r
        have hp : p = q + s := by
          omega
        subst p
        refine ⟨q + s, 0, ?_⟩
        simp only [balancedBlock,
          List.replicate_zero,
          List.nil_append, List.append_nil,
          List.replicate_add,
          List.append_assoc]
      · have hpq : p = q :=
          fourBlock_central_boundary_forces_balance
            (Nat.pos_of_ne_zero hq0)
            (Nat.pos_of_ne_zero hr0)
            hmem
        have hrs : r = s := by
          omega
        subst q
        subst s
        exact
          ⟨p, r,
            by simp [balancedBlock,
              List.append_assoc]⟩
  · exact doubleDelta_subset_intersection

end DeltaStar
end TCS1
end LeanCfgProject
