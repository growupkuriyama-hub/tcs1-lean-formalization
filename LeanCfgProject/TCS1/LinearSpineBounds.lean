import LeanCfgProject.TCS1.ShortestNonemptyPathBound
import Mathlib.Tactic

/-!
# TCS #1: linear-spine short-witness bounds

This module formalizes the combinatorial core of Lemma (short canonical
witnesses) for the linear subclass.

In the manuscript's linear-spine SSBNF, every continuing spine step emits
exactly one terminal through a fresh wrapper child. Hence a shortest
productive yield has length equal to the number of typed spine symbols on its
repetition-free spine. A reaching context of a spine symbol contains one
terminal per preceding spine step. For a wrapper symbol, the preceding
reaching spine contributes those terminals and the final spine child is
completed by one shortest productive yield.

The semantic normalization proving that concrete linear-spine SSBNF
derivations provide these certificates is kept separate. Here we verify the
finite pigeonhole and witness-length arithmetic exactly.
-/

namespace LeanCfgProject
namespace TCS1

universe u v

section LinearSpineBounds

variable {T : Type u}
variable {α : Type v}

/--
A shortest productive yield represented by a repetition-free typed spine.

The spine is written as root :: tail. In linear-spine SSBNF each spine
symbol contributes exactly one terminal: every continuing binary step emits
one wrapper terminal and the final spine symbol uses a terminal rule.
-/
structure LinearYieldSpineCertificate
    (root : T)
    (word : Word α) where
  tail : List T
  nodup : (root :: tail).Nodup
  length_eq :
    word.length = (root :: tail).length

/--
A terminal reaching context for a spine symbol.

stem ++ [target] lists the typed spine symbols visited from the non-start
child of the initial rule through the distinguished occurrence. Each
preceding step emits exactly one wrapper terminal into the surrounding
context.
-/
structure LinearSpineContextCertificate
    (target : T)
    (left right : Word α) where
  stem : List T
  nodup : (stem ++ [target]).Nodup
  context_length_eq :
    left.length + right.length = stem.length

/--
A terminal reaching context for a fresh wrapper symbol.

The repetition-free spine reaches parent; the final binary production has
the distinguished wrapper as one child and a continuing spine child whose
completion has length childYieldLength.
-/
structure LinearWrapperContextCertificate
    [Fintype T]
    (parent : T)
    (left right : Word α) where
  stem : List T
  nodup : (stem ++ [parent]).Nodup
  childYieldLength : Nat
  childYield_le :
    childYieldLength ≤ Fintype.card T
  context_length_le :
    left.length + right.length ≤
      stem.length + childYieldLength

/--
A repetition-free nonempty spine has strictly fewer preceding steps than
available typed non-start symbols.
-/
theorem linearSpine_stem_length_lt_card
    [Fintype T] [DecidableEq T]
    (target : T)
    (stem : List T)
    (hnodup : (stem ++ [target]).Nodup) :
    stem.length < Fintype.card T := by
  have hpath :
      (stem ++ [target]).length ≤ Fintype.card T :=
    nodup_path_length_le_card
      (stem ++ [target]) hnodup
  simp only [List.length_append, List.length_singleton] at hpath
  omega

/--
The shortest productive yield represented by a linear spine has length at
most the number of typed non-start symbols.
-/
theorem linearYieldSpine_length_le_card
    [Fintype T] [DecidableEq T]
    {root : T}
    {word : Word α}
    (C : LinearYieldSpineCertificate root word) :
    word.length ≤ Fintype.card T := by
  rw [C.length_eq]
  exact nodup_path_length_le_card
    (root :: C.tail) C.nodup

/--
A repetition-free reaching spine for a spine symbol contributes strictly fewer
than n_t terminals to its terminal context.
-/
theorem linearSpineContext_length_lt_card
    [Fintype T] [DecidableEq T]
    {target : T}
    {left right : Word α}
    (C : LinearSpineContextCertificate target left right) :
    left.length + right.length < Fintype.card T := by
  rw [C.context_length_eq]
  exact
    linearSpine_stem_length_lt_card
      target C.stem C.nodup

/--
In particular, the spine-symbol context obeys the paper-facing common bound
|u_X| + |v_X| ≤ 2 n_t.
-/
theorem linearSpineContext_length_le_twice_card
    [Fintype T] [DecidableEq T]
    {target : T}
    {left right : Word α}
    (C : LinearSpineContextCertificate target left right) :
    left.length + right.length ≤
      2 * Fintype.card T := by
  have hlt :=
    linearSpineContext_length_lt_card C
  omega

/--
For a wrapper occurrence, the preceding reaching spine contributes fewer than
n_t terminals and the continuing child can be completed by at most n_t
terminals. Hence the constructed context has length strictly below 2 n_t.
-/
theorem linearWrapperContext_length_lt_twice_card
    [Fintype T] [DecidableEq T]
    {parent : T}
    {left right : Word α}
    (C : LinearWrapperContextCertificate parent left right) :
    left.length + right.length <
      2 * Fintype.card T := by
  have hstem :
      C.stem.length < Fintype.card T :=
    linearSpine_stem_length_lt_card
      parent C.stem C.nodup
  have hctx := C.context_length_le
  have hchild := C.childYield_le
  omega

/-- Paper-facing weak form of the wrapper context bound. -/
theorem linearWrapperContext_length_le_twice_card
    [Fintype T] [DecidableEq T]
    {parent : T}
    {left right : Word α}
    (C : LinearWrapperContextCertificate parent left right) :
    left.length + right.length ≤
      2 * Fintype.card T := by
  exact Nat.le_of_lt
    (linearWrapperContext_length_lt_twice_card C)

/--
Common context certificate: a typed non-start symbol is either itself on the
continuing spine or is a fresh terminal wrapper reached from a spine parent.
-/
inductive LinearCanonicalContextCertificate
    [Fintype T]
    (left right : Word α) : Prop
  | spine
      {target : T}
      (C : LinearSpineContextCertificate target left right) :
      LinearCanonicalContextCertificate left right
  | wrapper
      {parent : T}
      (C : LinearWrapperContextCertificate parent left right) :
      LinearCanonicalContextCertificate left right

/--
Every canonical context admitting the linear-spine certificate satisfies the
uniform 2 n_t bound from Lemma (short canonical witnesses).
-/
theorem linearCanonicalContext_length_le_twice_card
    [Fintype T] [DecidableEq T]
    {left right : Word α}
    (C : LinearCanonicalContextCertificate
      (T := T) left right) :
    left.length + right.length ≤
      2 * Fintype.card T := by
  cases C with
  | spine C =>
      exact linearSpineContext_length_le_twice_card C
  | wrapper C =>
      exact linearWrapperContext_length_le_twice_card C

/--
Anchor witnesses contain one canonical context and one shortest productive
yield, hence have length at most 3 n_t.
-/
theorem linear_anchorWitness_length_le
    {n : Nat}
    {left omegaWord right : Word α}
    (hctx : left.length + right.length ≤ 2 * n)
    (hyield : omegaWord.length ≤ n) :
    (left ++ omegaWord ++ right).length ≤ 3 * n := by
  simp only [List.length_append]
  omega

/--
Terminal-rule witnesses contain one canonical context and one terminal.
-/
theorem linear_terminalWitness_length_le
    {n : Nat}
    {left right : Word α}
    {a : α}
    (hctx : left.length + right.length ≤ 2 * n) :
    (left ++ [a] ++ right).length ≤ 2 * n + 1 := by
  simp only [List.length_append, List.length_singleton]
  omega

/--
Binary-rule witnesses contain one canonical context and two shortest
productive yields, hence have length at most 4 n_t.
-/
theorem linear_binaryWitness_length_le
    {n : Nat}
    {left omega₁ omega₂ right : Word α}
    (hctx : left.length + right.length ≤ 2 * n)
    (hyield₁ : omega₁.length ≤ n)
    (hyield₂ : omega₂.length ≤ n) :
    (left ++ omega₁ ++ omega₂ ++ right).length ≤
      4 * n := by
  simp only [List.length_append]
  omega

/--
One uniform paper-facing bound covers anchors, terminal witnesses, binary
witnesses, and the optional epsilon witness.
-/
def linearCanonicalWitnessLengthEnvelope
    (n : Nat) : Nat :=
  4 * n + 1

theorem linear_anchorWitness_length_le_envelope
    {n : Nat}
    {left omegaWord right : Word α}
    (hctx : left.length + right.length ≤ 2 * n)
    (hyield : omegaWord.length ≤ n) :
    (left ++ omegaWord ++ right).length ≤
      linearCanonicalWitnessLengthEnvelope n := by
  have h :=
    linear_anchorWitness_length_le hctx hyield
  unfold linearCanonicalWitnessLengthEnvelope
  omega

theorem linear_terminalWitness_length_le_envelope
    {n : Nat}
    {left right : Word α}
    {a : α}
    (hctx : left.length + right.length ≤ 2 * n) :
    (left ++ [a] ++ right).length ≤
      linearCanonicalWitnessLengthEnvelope n := by
  have h :=
    linear_terminalWitness_length_le
      (a := a) hctx
  unfold linearCanonicalWitnessLengthEnvelope
  omega

theorem linear_binaryWitness_length_le_envelope
    {n : Nat}
    {left omega₁ omega₂ right : Word α}
    (hctx : left.length + right.length ≤ 2 * n)
    (hyield₁ : omega₁.length ≤ n)
    (hyield₂ : omega₂.length ≤ n) :
    (left ++ omega₁ ++ omega₂ ++ right).length ≤
      linearCanonicalWitnessLengthEnvelope n := by
  have h :=
    linear_binaryWitness_length_le
      hctx hyield₁ hyield₂
  unfold linearCanonicalWitnessLengthEnvelope
  omega

end LinearSpineBounds

end TCS1
end LeanCfgProject
