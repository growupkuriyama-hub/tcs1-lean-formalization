import LeanCfgProject.TCS1.CanonicalWitnessCompleteness

/-!
# TCS #1 v63: constructing the canonical witness set

The previous file treated the membership facts for W(tilde G) as an abstract
interface.  This file removes that interface layer.

For every active typed nonterminal X we assume exactly the two facts supplied
by trimming/reducedness:

* productivity: X derives at least one nonempty terminal yield omega(X);
* reachability: there is a terminal context (left(X),right(X)) which embeds
  every yield of X into a successful start derivation.

The canonical witness language is then defined explicitly from anchors,
terminal-rule witnesses, binary-rule witnesses, and (when present) epsilon.
We prove:

1. every witness word is in the reduced typed target language;
2. over finite alphabets/nonterminal sets the witness language is finite;
3. if the witness language is contained in a positive sample K, the abstract
   CanonicalWitnessData required by the completeness theorem is obtained
   automatically.

This is the qualitative (non-size-bound) bridge from reducedness to the
finite characteristic witness set.
-/

namespace LeanCfgProject
namespace TCS1

universe u v w

section WitnessSetConstruction

variable {α : Type u}
variable {M : Type v} [Monoid M] [Fintype M]
variable {N : Type w}
variable {H : FixedFiniteMonoidHom α M}
variable {terminalRule : N → α → Prop}
variable {binaryRule : N → N → N → Prop}
variable {startRule : N → Prop}
variable {epsilonStart : Prop}
variable {Active : N × M → Prop}

/--
Canonical productive/reaching choices supplied by a reduced typed grammar.
The quantitative sections of the paper choose these objects minimally; the
qualitative completeness proof only needs the properties recorded here.
-/
structure ReducedWitnessChoices
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop) where
  omega : N × M → Word α
  left : N × M → Word α
  right : N × M → Word α

  omegaDerives :
    ∀ X, Active X →
      ReducedTypedDerives H terminalRule binaryRule Active X (omega X)

  reaches :
    ∀ X, Active X →
      ∀ {z : Word α},
        ReducedTypedDerives H terminalRule binaryRule Active X z →
        ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active
          (left X ++ z ++ right X)

  start_empty :
    ∀ (A : N) (μ : M),
      startRule A →
      Active (A, μ) →
      left (A, μ) = [] ∧ right (A, μ) = []

/--
Small helper: reduced typed derivations are nonerasing, because terminal
leaves contribute one symbol and binary nodes concatenate two nonempty yields.
-/
theorem reducedTypedDerives_nonempty
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (Active : N × M → Prop)
    {X : N × M} {z : Word α}
    (d : ReducedTypedDerives H terminalRule binaryRule Active X z) :
    z ≠ [] := by
  induction d with
  | terminal _ _ =>
      simp
  | binary _ _ _ _ ihB _ihC =>
      exact append_ne_nil_of_left_ne_nil ihB

/--
The explicit witness language W(tilde G).  It consists exactly of the four
families used in the manuscript's completeness proof.
-/
def CanonicalWitnessWords
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    Set (Word α) :=
  { word |
      (∃ X : N × M,
          Active X ∧
          word = C.left X ++ C.omega X ++ C.right X)
      ∨
      (∃ (A : N) (a : α),
          terminalRule A a ∧
          Active (A, H.h [a]) ∧
          word =
            C.left (A, H.h [a]) ++
              [a] ++
              C.right (A, H.h [a]))
      ∨
      (∃ (A B Cn : N) (μ ν : M),
          binaryRule A B Cn ∧
          Active (A, μ * ν) ∧
          Active (B, μ) ∧
          Active (Cn, ν) ∧
          word =
            C.left (A, μ * ν) ++
              C.omega (B, μ) ++
              C.omega (Cn, ν) ++
              C.right (A, μ * ν))
      ∨
      (epsilonStart ∧ word = []) }

/-- Every anchor is a witness word. -/
theorem anchor_mem_canonicalWitnessWords
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (X : N × M)
    (hX : Active X) :
    C.left X ++ C.omega X ++ C.right X ∈
      CanonicalWitnessWords
        H terminalRule binaryRule startRule epsilonStart Active C := by
  exact Or.inl ⟨X, hX, rfl⟩

/-- Every terminal-rule witness is a witness word. -/
theorem terminal_mem_canonicalWitnessWords
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (A : N) (a : α)
    (hterm : terminalRule A a)
    (hactive : Active (A, H.h [a])) :
    C.left (A, H.h [a]) ++ [a] ++ C.right (A, H.h [a]) ∈
      CanonicalWitnessWords
        H terminalRule binaryRule startRule epsilonStart Active C := by
  exact Or.inr <| Or.inl ⟨A, a, hterm, hactive, rfl⟩

/-- Every binary-rule witness is a witness word. -/
theorem binary_mem_canonicalWitnessWords
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (A B Cn : N) (μ ν : M)
    (hbin : binaryRule A B Cn)
    (hA : Active (A, μ * ν))
    (hB : Active (B, μ))
    (hC : Active (Cn, ν)) :
    C.left (A, μ * ν) ++
        C.omega (B, μ) ++ C.omega (Cn, ν) ++
        C.right (A, μ * ν) ∈
      CanonicalWitnessWords
        H terminalRule binaryRule startRule epsilonStart Active C := by
  exact Or.inr <| Or.inr <| Or.inl
    ⟨A, B, Cn, μ, ν, hbin, hA, hB, hC, rfl⟩

/-- Epsilon is included precisely when the reduced grammar has an epsilon start rule. -/
theorem epsilon_mem_canonicalWitnessWords
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (heps : epsilonStart) :
    ([] : Word α) ∈
      CanonicalWitnessWords
        H terminalRule binaryRule startRule epsilonStart Active C := by
  exact Or.inr <| Or.inr <| Or.inr ⟨heps, rfl⟩

/--
All explicitly constructed witnesses are positive target words.
This is where productivity and reachability of the reduced grammar are used.
-/
theorem canonicalWitnessWords_subset_target
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    CanonicalWitnessWords
        H terminalRule binaryRule startRule epsilonStart Active C ⊆
      ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active := by
  intro word hword
  rcases hword with
    ⟨X, hX, rfl⟩
    | ⟨A, a, hterm, hactive, rfl⟩
    | ⟨A, B, Cn, μ, ν, hbin, hA, hB, hC, rfl⟩
    | ⟨heps, rfl⟩
  · exact C.reaches X hX (C.omegaDerives X hX)
  · exact C.reaches (A, H.h [a]) hactive
      (ReducedTypedDerives.terminal hterm hactive)
  · have dB := C.omegaDerives (B, μ) hB
    have dC := C.omegaDerives (Cn, ν) hC
    have dParent :
        ReducedTypedDerives H terminalRule binaryRule Active
          (A, μ * ν) (C.omega (B, μ) ++ C.omega (Cn, ν)) :=
      ReducedTypedDerives.binary hbin hA dB dC
    change
      ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active
        (C.left (A, μ * ν) ++
          C.omega (B, μ) ++ C.omega (Cn, ν) ++
          C.right (A, μ * ν))
    simpa only [List.append_assoc] using
      C.reaches (A, μ * ν) hA dParent
  · exact ReducedTypedStartDerives.epsilon heps

/--
For finite alphabets and finite nonterminal sets, the witness language is
finite.  This is the qualitative finiteness statement; Section 7 supplies the
polynomial length/size bounds.
-/
theorem canonicalWitnessWords_finite
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    (CanonicalWitnessWords
        H terminalRule binaryRule startRule epsilonStart Active C).Finite := by
  classical
  let anchors : Set (Word α) :=
    Set.range (fun X : N × M =>
      C.left X ++ C.omega X ++ C.right X)
  let terminals : Set (Word α) :=
    Set.range (fun p : N × α =>
      C.left (p.1, H.h [p.2]) ++ [p.2] ++ C.right (p.1, H.h [p.2]))
  let binaries : Set (Word α) :=
    Set.range (fun p : N × N × N × M × M =>
      C.left (p.1, p.2.2.2.1 * p.2.2.2.2) ++
        C.omega (p.2.1, p.2.2.2.1) ++
        C.omega (p.2.2.1, p.2.2.2.2) ++
        C.right (p.1, p.2.2.2.1 * p.2.2.2.2))
  have hAnchors : anchors.Finite := Set.finite_range _
  have hTerminals : terminals.Finite := Set.finite_range _
  have hBinaries : binaries.Finite := Set.finite_range _
  have hSingleton : ({([] : Word α)} : Set (Word α)).Finite :=
    Set.finite_singleton []
  apply
    (hAnchors.union
      (hTerminals.union
        (hBinaries.union hSingleton))).subset
  intro word hword
  rcases hword with
    ⟨X, _hX, rfl⟩
    | ⟨A, a, _hterm, _hactive, rfl⟩
    | ⟨A, B, Cn, μ, ν, _hbin, _hA, _hB, _hC, rfl⟩
    | ⟨_heps, rfl⟩
  · exact Or.inl ⟨X, rfl⟩
  · exact Or.inr <| Or.inl ⟨(A, a), rfl⟩
  · exact Or.inr <| Or.inr <| Or.inl
      ⟨(A, B, Cn, μ, ν), rfl⟩
  · exact Or.inr <| Or.inr <| Or.inr rfl

/--
The finite characteristic witness set obtained from the explicit witness
language.
-/
noncomputable def canonicalWitnessFinset
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active) :
    Finset (Word α) := by
  classical
  exact
    (canonicalWitnessWords_finite
      H terminalRule binaryRule startRule epsilonStart Active C).toFinset

theorem mem_canonicalWitnessFinset_iff
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (word : Word α) :
    word ∈
        canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C ↔
      word ∈
        CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C := by
  classical
  simp [canonicalWitnessFinset]

/--
Containment of the explicit witness set in K supplies the entire abstract
CanonicalWitnessData interface used by the simulation theorem.
-/
noncomputable def canonicalWitnessData_of_subset
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (hWK :
      CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C ⊆
        (↑K : Set (Word α))) :
    CanonicalWitnessData
      H K terminalRule binaryRule startRule epsilonStart Active := by
  classical
  refine
    { omega := C.omega
      left := C.left
      right := C.right
      omega_ne := ?_
      omega_type := ?_
      anchor_mem := ?_
      terminal_mem := ?_
      binary_mem := ?_
      start_context := C.start_empty
      epsilon_mem := ?_ }
  · intro X hX
    exact reducedTypedDerives_nonempty
      H terminalRule binaryRule Active (C.omegaDerives X hX)
  · intro X hX
    exact reducedTypedDerives_yield_type
      H terminalRule binaryRule Active (C.omegaDerives X hX)
  · intro X hX
    exact hWK (anchor_mem_canonicalWitnessWords C X hX)
  · intro A a hterm hactive
    exact hWK
      (terminal_mem_canonicalWitnessWords C A a hterm hactive)
  · intro A B Cn μ ν hbin hA hB hC
    exact hWK
      (binary_mem_canonicalWitnessWords C A B Cn μ ν hbin hA hB hC)
  · intro heps
    exact hWK (epsilon_mem_canonicalWitnessWords C heps)

/--
Completeness stated directly from reducedness choices and inclusion of the
explicit witness set, with no separate CanonicalWitnessData hypothesis.
-/
theorem canonicalWitnessWords_completeness
    (H : FixedFiniteMonoidHom α M)
    (K : Finset (Word α))
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (hWK :
      CanonicalWitnessWords
          H terminalRule binaryRule startRule epsilonStart Active C ⊆
        (↑K : Set (Word α))) :
    ReducedTypedLanguage
        H terminalRule binaryRule startRule epsilonStart Active ⊆
      BatchLanguage H K := by
  exact canonical_witness_completeness
    H K terminalRule binaryRule startRule epsilonStart Active
    (canonicalWitnessData_of_subset
      H K terminalRule binaryRule startRule epsilonStart Active C hWK)

/--
The explicit canonical witness finset is itself a characteristic sample for
the reduced typed target, for any valid reduced witness choices.

Minimality of the choices is irrelevant to exact reconstruction; it is used
only for the quantitative Section 7 bounds.
-/
theorem exact_reconstruction_of_canonicalWitnessFinset
    [Fintype α] [Fintype N]
    (H : FixedFiniteMonoidHom α M)
    (terminalRule : N → α → Prop)
    (binaryRule : N → N → N → Prop)
    (startRule : N → Prop)
    (epsilonStart : Prop)
    (Active : N × M → Prop)
    (C :
      ReducedWitnessChoices
        H terminalRule binaryRule startRule epsilonStart Active)
    (hsub :
      FixedHSubstitutable H
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active)) :
    BatchLanguage H
        (canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C)
      =
    ReducedTypedLanguage
      H terminalRule binaryRule startRule epsilonStart Active := by
  classical
  apply Set.Subset.antisymm
  · apply
      batchLanguage_sound
        H
        (canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C)
        (ReducedTypedLanguage
          H terminalRule binaryRule startRule epsilonStart Active)
    · intro word hword
      apply
        canonicalWitnessWords_subset_target
          H terminalRule binaryRule startRule epsilonStart Active C
      exact
        (mem_canonicalWitnessFinset_iff
          H terminalRule binaryRule startRule epsilonStart Active C word).1
          hword
    · exact hsub
  · apply
      canonicalWitnessWords_completeness
        H
        (canonicalWitnessFinset
          H terminalRule binaryRule startRule epsilonStart Active C)
        terminalRule binaryRule startRule epsilonStart Active C
    intro word hword
    exact
      (mem_canonicalWitnessFinset_iff
        H terminalRule binaryRule startRule epsilonStart Active C word).2
        hword

end WitnessSetConstruction

end TCS1
end LeanCfgProject
