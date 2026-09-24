import LeanCfgProject.TCS1.DeltaStarFixedHSubstitutability

/-!
# TCS #1 v78: displayed CFG semantics for Delta-star

The manuscript uses the grammar

  S -> T S | epsilon
  T -> a T b | epsilon

for Delta* = ({a^n b^n : n >= 0})*.

This module gives that displayed grammar a direct derivation semantics and
proves exact equality with the deterministic parser language used by the
fixed-h and fixed-window proofs.  Thus the parser-side separation arguments
and the manuscript's context-free presentation are connected by a
machine-checked semantic bridge.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

/--
If a scan starts in falling mode at height n+1 and eventually returns to
zero, its first n+1 symbols are b's; the remaining suffix is accepted from
zero.
-/
theorem scan_falling_to_zero_shape
    (n : Nat)
    {w : Word Symbol}
    (hscan :
      scan (.falling n) w = some .zero) :
    ∃ rest : Word Symbol,
      w =
          List.replicate (n + 1) b ++ rest
        ∧
      scan .zero rest = some .zero := by
  induction n generalizing w with
  | zero =>
      cases w with
      | nil =>
          simp [scan] at hscan
      | cons s w =>
          cases s with
          | a =>
              simp [scan, step] at hscan
          | b =>
              refine ⟨w, ?_, ?_⟩
              · simp [List.replicate_succ]
              · simpa [scan, step] using hscan
  | succ n ih =>
      cases w with
      | nil =>
          simp [scan] at hscan
      | cons s w =>
          cases s with
          | a =>
              simp [scan, step] at hscan
          | b =>
              have htail :
                  scan (.falling n) w =
                    some .zero := by
                simpa [scan, step] using hscan
              obtain ⟨rest, hw, hr⟩ :=
                ih htail
              refine ⟨rest, ?_, hr⟩
              rw [hw]
              simp [List.replicate_succ,
                Nat.add_assoc]

/--
If a scan starts in rising mode at height n+1 and eventually returns to zero,
then it first reads p additional a's, then exactly n+p+1 b's, and continues
with a suffix accepted from zero.
-/
theorem scan_rising_to_zero_shape
    (n : Nat)
    {w : Word Symbol}
    (hscan :
      scan (.rising n) w = some .zero) :
    ∃ p : Nat, ∃ rest : Word Symbol,
      w =
          List.replicate p a ++
            List.replicate (n + p + 1) b ++
              rest
        ∧
      scan .zero rest = some .zero := by
  induction w generalizing n with
  | nil =>
      simp [scan] at hscan
  | cons s w ih =>
      cases s with
      | a =>
          have htail :
              scan (.rising (n + 1)) w =
                some .zero := by
            simpa [scan, step] using hscan
          obtain ⟨p, rest, hw, hr⟩ :=
            ih (n := n + 1) htail
          refine ⟨p + 1, rest, ?_, hr⟩
          rw [hw]
          simp [List.replicate_succ,
            List.append_assoc,
            Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm]
      | b =>
          cases n with
          | zero =>
              refine ⟨0, w, ?_, ?_⟩
              · simp [List.replicate_succ]
              · simpa [scan, step] using hscan
          | succ n =>
              have hfall :
                  scan (.falling n) w =
                    some .zero := by
                simpa [scan, step] using hscan
              obtain ⟨rest, hw, hr⟩ :=
                scan_falling_to_zero_shape
                  n hfall
              refine ⟨0, rest, ?_, hr⟩
              rw [hw]
              simp [List.replicate_succ,
                Nat.add_assoc]

/--
Canonical Kleene-star semantics: prepend one balanced monotone block
a^n b^n to another derived word.
-/
inductive StarDerives : Word Symbol → Prop
  | epsilon :
      StarDerives []
  | prepend
      (n : Nat)
      {w : Word Symbol}
      (dw : StarDerives w) :
      StarDerives
        ((List.replicate n a ++
            List.replicate n b) ++ w)

/-- The canonical block-star semantics is accepted by the parser. -/
theorem starDerives_to_language
    {w : Word Symbol}
    (d : StarDerives w) :
    w ∈ Language := by
  induction d with
  | epsilon =>
      rfl
  | @prepend n w dw ih =>
      change
        scan .zero
            ((List.replicate n a ++
                List.replicate n b) ++ w) =
          some .zero
      rw [scan_append, scan_block]
      exact ih

/-- Length-indexed form of the parser-to-block-star decomposition. -/
theorem language_to_starDerives_aux :
    ∀ n : Nat, ∀ w : Word Symbol,
      w.length = n →
      w ∈ Language →
      StarDerives w := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro w hlen hw
      cases w with
      | nil =>
          exact StarDerives.epsilon
      | cons s tail =>
          cases s with
          | b =>
              change
                scan .zero (b :: tail) =
                  some .zero at hw
              simp [scan, step] at hw
          | a =>
              have hrun :
                  scan (.rising 0) tail =
                    some .zero := by
                simpa [scan, step] using hw
              obtain ⟨p, rest, hshape, hrest⟩ :=
                scan_rising_to_zero_shape
                  0 hrun
              have htail :
                  tail.length =
                    p + (p + 1) + rest.length := by
                calc
                  tail.length =
                      (List.replicate p a ++
                        List.replicate (0 + p + 1) b ++
                          rest).length :=
                    congrArg List.length hshape
                  _ = p + (p + 1) + rest.length := by
                    simp only [List.length_append,
                      List.length_replicate, Nat.zero_add]
              have hrestlt :
                  rest.length < n := by
                simp only [List.length_cons] at hlen
                omega
              have drest :
                  StarDerives rest :=
                ih rest.length hrestlt
                  rest rfl
                  (show rest ∈ Language from hrest)
              have heq :
                  a :: tail =
                    ((List.replicate (p + 1) a ++
                        List.replicate (p + 1) b) ++
                      rest) := by
                rw [hshape]
                simp [List.replicate_succ,
                  List.append_assoc,
                  Nat.add_assoc, Nat.add_comm,
                  Nat.add_left_comm]
              rw [heq]
              exact
                StarDerives.prepend
                  (p + 1) drest

/-- Every parser-accepted word decomposes into balanced monotone blocks. -/
theorem language_to_starDerives
    {w : Word Symbol}
    (hw : w ∈ Language) :
    StarDerives w :=
  language_to_starDerives_aux
    w.length w rfl hw

/-- Exact parser/Kleene-star semantic equality. -/
theorem starDerives_iff_language
    (w : Word Symbol) :
    StarDerives w ↔ w ∈ Language :=
  ⟨starDerives_to_language,
    language_to_starDerives⟩

/-- Direct semantics of the displayed nonterminal T -> a T b | epsilon. -/
inductive TDerives : Word Symbol → Prop
  | epsilon :
      TDerives []
  | wrap
      {w : Word Symbol}
      (d : TDerives w) :
      TDerives (a :: w ++ [b])

/-- Direct semantics of the displayed start rules S -> T S | epsilon. -/
inductive SDerives : Word Symbol → Prop
  | epsilon :
      SDerives []
  | concat
      {x y : Word Symbol}
      (dx : TDerives x)
      (dy : SDerives y) :
      SDerives (x ++ y)

/-- Every displayed T-derivation is exactly one a^n b^n block. -/
theorem tDerives_shape
    {w : Word Symbol}
    (d : TDerives w) :
    ∃ n : Nat,
      w =
        List.replicate n a ++
          List.replicate n b := by
  induction d with
  | epsilon =>
      exact ⟨0, by simp⟩
  | @wrap w d ih =>
      obtain ⟨n, rfl⟩ := ih
      refine ⟨n + 1, ?_⟩
      simp [List.replicate_succ,
        replicate_succ_right,
        List.append_assoc]

/-- Every balanced monotone block has a displayed T-derivation. -/
theorem block_to_tDerives
    (n : Nat) :
    TDerives
      (List.replicate n a ++
        List.replicate n b) := by
  induction n with
  | zero =>
      simpa using TDerives.epsilon
  | succ n ih =>
      have h := TDerives.wrap ih
      simpa [List.replicate_succ,
        replicate_succ_right,
        List.append_assoc] using h

/-- Displayed S-derivations imply canonical block-star derivations. -/
theorem sDerives_to_star
    {w : Word Symbol}
    (d : SDerives w) :
    StarDerives w := by
  induction d with
  | epsilon =>
      exact StarDerives.epsilon
  | @concat x y dx dy ih =>
      obtain ⟨n, rfl⟩ :=
        tDerives_shape dx
      exact
        StarDerives.prepend n ih

/-- Canonical block-star derivations are generated by the displayed grammar. -/
theorem star_to_sDerives
    {w : Word Symbol}
    (d : StarDerives w) :
    SDerives w := by
  induction d with
  | epsilon =>
      exact SDerives.epsilon
  | @prepend n w dw ih =>
      exact
        SDerives.concat
          (block_to_tDerives n) ih

/--
Exact semantic bridge for the manuscript grammar
S -> T S | epsilon, T -> a T b | epsilon.
-/
theorem displayedDerives_iff_language
    (w : Word Symbol) :
    SDerives w ↔ w ∈ Language := by
  constructor
  · intro d
    exact
      starDerives_to_language
        (sDerives_to_star d)
  · intro hw
    exact
      star_to_sDerives
        (language_to_starDerives hw)

end DeltaStar
end TCS1
end LeanCfgProject
