import LeanCfgProject.TCS1.RegularRecognition

/-!
# TCS #1 v158: the syntactic-morphism clause of `prop:regular-auto`

`prop:regular-auto`: "*A language is regular iff it has the form `h⁻¹(Acc)` for
some homomorphism `h : Σ* → M` into a finite monoid and some `Acc ⊆ M`.  For
regular `L`, `h` may be taken to be its syntactic morphism, whose kernel is
`≡_L`.*"

`regular_auto_proposition_package` proves the first sentence (through the
transition monoid of a DFA).  This file proves the syntactic-morphism sentence:
for regular `L`, the quotient of words by the syntactic congruence `≡_L` is a
finite monoid, the quotient map is a monoid homomorphism with kernel exactly
`≡_L`, and `L` is the preimage of a subset (`regular_syntacticMorphism`).
-/

namespace LeanCfgProject
namespace TCS1

universe u

variable {α : Type u}

/-- The syntactic congruence `u ≡_L v`. -/
def SyntacticEquiv (L : Set (Word α)) (u v : Word α) : Prop :=
  ∀ x y : Word α, x ++ u ++ y ∈ L ↔ x ++ v ++ y ∈ L

def syntacticSetoid (L : Set (Word α)) : Setoid (Word α) where
  r := SyntacticEquiv L
  iseqv :=
    ⟨fun _ _ _ => Iff.rfl, fun h x y => (h x y).symm, fun h₁ h₂ x y => (h₁ x y).trans (h₂ x y)⟩

/-- The syntactic monoid `Σ*/≡_L`. -/
abbrev SyntacticMonoid (L : Set (Word α)) := Quotient (syntacticSetoid L)

theorem syntacticEquiv_append {L : Set (Word α)} {u u' v v' : Word α}
    (hu : SyntacticEquiv L u u') (hv : SyntacticEquiv L v v') :
    SyntacticEquiv L (u ++ v) (u' ++ v') := by
  intro x y
  have e1 : x ++ (u ++ v) ++ y = x ++ u ++ (v ++ y) := by simp
  have e2 : x ++ u' ++ (v ++ y) = (x ++ u') ++ v ++ y := by simp
  have e3 : (x ++ u') ++ v' ++ y = x ++ (u' ++ v') ++ y := by simp
  rw [e1, hu x (v ++ y), e2, hv (x ++ u') y, e3]

instance syntacticMonoidInst (L : Set (Word α)) : Monoid (SyntacticMonoid L) where
  mul := Quotient.map₂ (· ++ ·) (fun _ _ h₁ _ _ h₂ => syntacticEquiv_append h₁ h₂)
  one := Quotient.mk _ []
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    exact congrArg (Quotient.mk _) (List.append_assoc a b c)
  one_mul := by
    rintro ⟨a⟩
    exact congrArg (Quotient.mk _) (List.nil_append a)
  mul_one := by
    rintro ⟨a⟩
    exact congrArg (Quotient.mk _) (List.append_nil a)

/-- The syntactic morphism `w ↦ [w]_{≡_L}`. -/
def syntacticHom (L : Set (Word α)) [Fintype (SyntacticMonoid L)] :
    FixedFiniteMonoidHom α (SyntacticMonoid L) where
  h w := Quotient.mk _ w
  map_nil := rfl
  map_append _ _ := rfl

/-- The kernel of the syntactic morphism is exactly `≡_L`. -/
theorem syntacticHom_kernel (L : Set (Word α)) [Fintype (SyntacticMonoid L)] (u v : Word α) :
    (syntacticHom L).h u = (syntacticHom L).h v ↔ SyntacticEquiv L u v :=
  Quotient.eq (r := syntacticSetoid L)

/-- `L` is a union of `≡_L`-classes. -/
theorem syntacticHom_preimage (L : Set (Word α)) [Fintype (SyntacticMonoid L)] :
    RecognizedPreimage (syntacticHom L) {m | ∃ w, w ∈ L ∧ (syntacticHom L).h w = m} = L := by
  ext w
  constructor
  · rintro ⟨w', hw', he⟩
    have := ((syntacticHom_kernel L w' w).mp he) [] []
    simp only [List.nil_append, List.append_nil] at this
    exact this.mp hw'
  · intro hw
    exact ⟨w, hw, rfl⟩

/-- For a regular language the syntactic monoid is finite. -/
theorem syntacticMonoid_finite (L : Language α) (hL : L.IsRegular) :
    Finite (SyntacticMonoid (L : Set (Word α))) := by
  obtain ⟨σ, _, D, hD⟩ := hL
  let t : Word α → σ → σ := fun u q => D.evalFrom q u
  have key : ∀ u v, t u = t v → SyntacticEquiv (L : Set (Word α)) u v := by
    intro u v huv x y
    have hu : D.evalFrom D.start (x ++ u ++ y) =
        D.evalFrom (t u (D.evalFrom D.start x)) y := by
      simp [t, DFA.evalFrom_of_append]
    have hv : D.evalFrom D.start (x ++ v ++ y) =
        D.evalFrom (t v (D.evalFrom D.start x)) y := by
      simp [t, DFA.evalFrom_of_append]
    rw [← hD]
    show D.evalFrom D.start (x ++ u ++ y) ∈ D.accept ↔ D.evalFrom D.start (x ++ v ++ y) ∈ D.accept
    rw [hu, hv, huv]
  let f : Set.range t → SyntacticMonoid (L : Set (Word α)) :=
    fun τ => Quotient.mk _ (Classical.choose τ.2)
  have hf : Function.Surjective f := by
    rintro ⟨u⟩
    refine ⟨⟨t u, u, rfl⟩, ?_⟩
    apply Quotient.sound
    exact key _ _ (Classical.choose_spec (⟨u, rfl⟩ : ∃ u', t u' = t u))
  exact Finite.of_surjective f hf

/--
**`prop:regular-auto`, syntactic-morphism clause.**  For a regular `L`, the
syntactic monoid is finite, and the syntactic morphism `h_L` recognizes `L`
(`L = h_L⁻¹(Acc)`) and has kernel exactly `≡_L`.
-/
theorem regular_syntacticMorphism (L : Language α) (hL : L.IsRegular) :
    ∃ _ : Fintype (SyntacticMonoid (L : Set (Word α))),
      ∃ Acc : Set (SyntacticMonoid (L : Set (Word α))),
        RecognizedPreimage (syntacticHom (L : Set (Word α))) Acc = L ∧
        ∀ u v : Word α,
          (syntacticHom (L : Set (Word α))).h u = (syntacticHom (L : Set (Word α))).h v ↔
            SyntacticEquiv (L : Set (Word α)) u v := by
  haveI := syntacticMonoid_finite L hL
  letI : Fintype (SyntacticMonoid (L : Set (Word α))) := Fintype.ofFinite _
  exact ⟨this, _, syntacticHom_preimage (L : Set (Word α)), syntacticHom_kernel _⟩

end TCS1
end LeanCfgProject
