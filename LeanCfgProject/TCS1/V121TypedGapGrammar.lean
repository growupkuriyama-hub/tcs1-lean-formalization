import LeanCfgProject.TCS1.V121TypedGapKernel
import LeanCfgProject.TCS1.ConcreteTypedTrimming

/-!
# TCS #1 v121: the actual finite G_n^c grammar and its exponential typed yield

The finite grammar is represented with nonterminals U, D and E_i for
0 ≤ i ≤ n; rules are precisely S₀ → U; U → a | c | U U | E_n D;
D → c; E₀ → a; E_i → E_(i-1) E_(i-1) | c for i > 0.

The proofs below connect its ordinary CFG semantics to the E_i exponential
yield kernel. They also show E_n at type one survives the **concrete**
productive/reachable typed trim by exhibiting the successful
S₀ → U → E_n D derivation.

Subsequent work is still needed to package all source symbols' reachability,
the exact linear grammar encoding budget and the complete quantitative
typed-thickness proposition.
-/

namespace LeanCfgProject
namespace TCS1
namespace TypedGap

/-- Exactly n+3 source non-start symbols. -/
inductive GapNT (n : Nat) where
  | u | d
  | e : Fin (n + 1) → GapNT n
  deriving DecidableEq, Fintype, Repr

/-- All and only the displayed one-terminal productions. -/
inductive GapTerm (n : Nat) : GapNT n → Letter → Prop where
  | u_a : GapTerm n .u .a
  | u_c : GapTerm n .u .c
  | d_c : GapTerm n .d .c
  | e0_a : GapTerm n (.e ⟨0, Nat.zero_lt_succ n⟩) .a
  | ei_c (i : Fin (n + 1)) (hi : 0 < i.val) :
      GapTerm n (.e i) .c

/-- All and only the displayed two-nonterminal productions. -/
inductive GapBin (n : Nat) :
    GapNT n → GapNT n → GapNT n → Prop where
  | u_concat : GapBin n .u .u .u
  | u_end : GapBin n .u (.e ⟨n, Nat.lt_succ_self n⟩) .d
  | ei_double (i j : Fin (n + 1)) (hij : i.val = j.val + 1) :
      GapBin n (.e i) (.e j) (.e j)

def GapStart (n : Nat) : GapNT n → Prop :=
  fun A => A = .u

/-- A full grammar derivation rooted at E_i obeys the standalone E_i grammar. -/
theorem gapE_derives_to_kernel
    (n : Nat)
    {A : GapNT n}
    {w : Word Letter}
    (d : UntypedDerives (GapTerm n) (GapBin n) A w) :
    ∀ (i : Fin (n + 1)), A = .e i → EDerives i.val w := by
  induction d with
  | @terminal A a ht =>
      intro i hAi
      cases ht with
      | u_a => cases hAi
      | u_c => cases hAi
      | d_c => cases hAi
      | e0_a =>
          cases hAi
          exact EDerives.base
      | ei_c j hj =>
          cases hAi
          cases heq : i.val with
          | zero =>
              omega
          | succ k =>
              simpa only [heq] using (EDerives.shortcut k)
  | @binary A B C wB wC hb _ _ ihB ihC =>
      intro i hAi
      cases hb with
      | u_concat => cases hAi
      | u_end => cases hAi
      | ei_double j k hjk =>
          cases hAi
          have dB : EDerives k.val wB := ihB k rfl
          have dC : EDerives k.val wC := ihC k rfl
          simpa only [hjk] using (EDerives.double k.val dB dC)

/-- The unshortened E_i expansion a^(2^i) exists in the displayed grammar. -/
theorem gapE_pure (n : Nat) :
    ∀ (i : Nat) (hi : i ≤ n),
      UntypedDerives (GapTerm n) (GapBin n)
        (.e ⟨i, Nat.lt_succ_of_le hi⟩)
        (pureE i) := by
  intro i
  induction i with
  | zero =>
      intro hi
      exact UntypedDerives.terminal GapTerm.e0_a
  | succ i ih =>
      intro hi
      have hi' : i ≤ n := by omega
      let j : Fin (n + 1) := ⟨i + 1, Nat.lt_succ_of_le hi⟩
      let k : Fin (n + 1) := ⟨i, Nat.lt_succ_of_le hi'⟩
      have db :
          UntypedDerives (GapTerm n) (GapBin n)
            (.e j) (pureE i ++ pureE i) :=
        UntypedDerives.binary (GapBin.ei_double j k (by rfl))
          (ih hi') (ih hi')
      simpa only [pureE] using db

/-- Every source non-start nonterminal has a length-one terminal yield.
Thus the source grammar's ordinary non-start thickness is exactly one. -/
theorem gap_source_has_unit_yield (n : Nat) (A : GapNT n) :
    ∃ a : Letter, UntypedDerives (GapTerm n) (GapBin n) A [a] := by
  cases A with
  | u =>
      exact ⟨.a, UntypedDerives.terminal GapTerm.u_a⟩
  | d =>
      exact ⟨.c, UntypedDerives.terminal GapTerm.d_c⟩
  | e i =>
      by_cases h0 : i.val = 0
      · have hieq : i = ⟨0, Nat.zero_lt_succ n⟩ :=
          Fin.ext h0
        subst i
        exact ⟨.a, UntypedDerives.terminal GapTerm.e0_a⟩
      · have hpos : 0 < i.val := Nat.pos_of_ne_zero h0
        exact ⟨.c, UntypedDerives.terminal
          (GapTerm.ei_c i hpos)⟩

/-- In the concrete trimmed yield-typed grammar, (E_n,one) is retained. -/
theorem gap_eTop_retained (n : Nat) :
    ConcreteTypedActive
      fixedTyping (GapTerm n) (GapBin n) (GapStart n)
      ((.e ⟨n, Nat.lt_succ_self n⟩), .one) := by
  have dE :
      UntypedDerives (GapTerm n) (GapBin n)
        (.e ⟨n, Nat.lt_succ_self n⟩) (pureE n) :=
    gapE_pure n n (Nat.le_refl n)
  have dTE :
      TypedDerives fixedTyping (GapTerm n) (GapBin n)
        ((.e ⟨n, Nat.lt_succ_self n⟩), .one) (pureE n) := by
    have d := untypedDerives_lift
      fixedTyping (GapTerm n) (GapBin n) dE
    change TypedDerives fixedTyping (GapTerm n) (GapBin n)
      ((.e ⟨n, Nat.lt_succ_self n⟩), wordType (pureE n))
      (pureE n) at d
    rw [pureE_type_one] at d
    exact d
  have dTD :
      TypedDerives fixedTyping (GapTerm n) (GapBin n)
        (.d, .zero) [.c] :=
    TypedDerives.terminal GapTerm.d_c
  have dTU :
      TypedDerives fixedTyping (GapTerm n) (GapBin n)
        (.u, .zero) (pureE n ++ [.c]) :=
    TypedDerives.binary GapBin.u_end dTE dTD
  have hparent :
      ConcreteTypedActive
        fixedTyping (GapTerm n) (GapBin n) (GapStart n)
        (.u, .zero) :=
    ProductiveTypedReachable.start rfl ⟨_, dTU⟩
  exact
    ProductiveTypedReachable.left hparent GapBin.u_end
      ⟨_, dTE⟩ ⟨_, dTD⟩

/-- Every yield of the **retained** E_n at type one has length exactly 2^n. -/
theorem gap_eTop_trimmed_length_exact
    (n : Nat)
    {w : Word Letter}
    (d :
      ReducedTypedDerives
        fixedTyping (GapTerm n) (GapBin n)
        (ConcreteTypedActive
          fixedTyping (GapTerm n) (GapBin n) (GapStart n))
        ((.e ⟨n, Nat.lt_succ_self n⟩), .one)
        w) :
    w.length = 2 ^ n := by
  have typed := reducedTypedDerives_to_typedDerives
    fixedTyping (GapTerm n) (GapBin n)
    (ConcreteTypedActive
      fixedTyping (GapTerm n) (GapBin n) (GapStart n)) d
  have untyped := typedDerives_erase
    fixedTyping (GapTerm n) (GapBin n) typed
  have kernel : EDerives n w :=
    gapE_derives_to_kernel n untyped
      ⟨n, Nat.lt_succ_self n⟩ rfl
  have htype : wordType w = .one := by
    have hyield := reducedTypedDerives_yield_type
      fixedTyping (GapTerm n) (GapBin n)
      (ConcreteTypedActive
        fixedTyping (GapTerm n) (GapBin n) (GapStart n)) d
    exact hyield
  exact EDerives_type_one_length kernel htype

/-- The witness survives trimming, so the exponential bound is nonvacuous. -/
theorem gap_eTop_trimmed_witness (n : Nat) :
    ∃ w : Word Letter,
      ReducedTypedDerives
        fixedTyping (GapTerm n) (GapBin n)
        (ConcreteTypedActive
          fixedTyping (GapTerm n) (GapBin n) (GapStart n))
        ((.e ⟨n, Nat.lt_succ_self n⟩), .one) w
      ∧ w.length = 2 ^ n := by
  have dE :
      UntypedDerives (GapTerm n) (GapBin n)
        (.e ⟨n, Nat.lt_succ_self n⟩) (pureE n) :=
    gapE_pure n n (Nat.le_refl n)
  have dTE :
      TypedDerives fixedTyping (GapTerm n) (GapBin n)
        ((.e ⟨n, Nat.lt_succ_self n⟩), .one) (pureE n) := by
    have dt := untypedDerives_lift
      fixedTyping (GapTerm n) (GapBin n) dE
    change TypedDerives fixedTyping (GapTerm n) (GapBin n)
      ((.e ⟨n, Nat.lt_succ_self n⟩), wordType (pureE n)) (pureE n) at dt
    rw [pureE_type_one] at dt
    exact dt
  have dr :=
    (concreteTypedActive_trimClosure
      fixedTyping (GapTerm n) (GapBin n) (GapStart n)).restrict
        (gap_eTop_retained n) dTE
  exact ⟨pureE n, dr, gap_eTop_trimmed_length_exact n dr⟩

end TypedGap
end TCS1
end LeanCfgProject
