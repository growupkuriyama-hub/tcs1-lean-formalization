import LeanCfgProject.TCS1.LinearSeparatorDistribution

/-!
# TCS #1 v78: context shape for center-containing separator factors

This module isolates the structural lemma used in the fixed-h proof for
L_{±,e}.  If a factor containing one of the center symbols c,d,e occurs
inside a word of L_{±,e}, then everything to its left is a pure a-power and
everything to its right is a pure b-power.

The proof is deliberately independent of balance/parity arithmetic.  A
generic prefix lemma strips the ambient a-prefix.  The suffix statement is
obtained by reversing the word and reusing the same lemma.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- The three center letters of the separator language. -/
def LpmCenterSymbol (z : LpmSymbol) : Prop :=
  z = c ∨ z = d ∨ z = e

theorem center_ne_a
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z) :
    z ≠ a := by
  rcases hz with rfl | rfl | rfl <;> decide

theorem center_ne_b
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z) :
    z ≠ b := by
  rcases hz with rfl | rfl | rfl <;> decide

/--
Generic left-shape lemma.

If a factor left^i z right^j, with z distinct from right, occurs in a word of
the form left^p z' right^q, then the context before that factor is a pure
left-power.
-/
theorem prefix_context_is_power
    (left right z z' : LpmSymbol)
    (hzright : z ≠ right)
    {i j p q : Nat}
    {u v : Word LpmSymbol}
    (h :
      u ++
          (List.replicate i left ++ [z] ++
            List.replicate j right) ++
          v =
        List.replicate p left ++ [z'] ++
          List.replicate q right) :
    ∃ m : Nat, u = List.replicate m left := by
  induction u generalizing p with
  | nil =>
      exact ⟨0, rfl⟩
  | cons t u ih =>
      cases p with
      | zero =>
          have hcons :
              t ::
                  (u ++
                    (List.replicate i left ++ [z] ++
                      List.replicate j right) ++
                    v) =
                z' :: List.replicate q right := by
            simpa [List.append_assoc] using h
          have htail :
              u ++
                  (List.replicate i left ++ [z] ++
                    List.replicate j right) ++
                  v =
                List.replicate q right :=
            (List.cons.inj hcons).2
          have hzmem :
              z ∈
                u ++
                  (List.replicate i left ++ [z] ++
                    List.replicate j right) ++
                  v := by
            simp
          rw [htail] at hzmem
          simp [List.mem_replicate, hzright] at hzmem
      | succ p =>
          have hcons :
              t ::
                  (u ++
                    (List.replicate i left ++ [z] ++
                      List.replicate j right) ++
                    v) =
                left ::
                  (List.replicate p left ++ [z'] ++
                    List.replicate q right) := by
            simpa [List.replicate_succ, List.append_assoc] using h
          have ht : t = left :=
            (List.cons.inj hcons).1
          have htail :
              u ++
                  (List.replicate i left ++ [z] ++
                    List.replicate j right) ++
                  v =
                List.replicate p left ++ [z'] ++
                  List.replicate q right :=
            (List.cons.inj hcons).2
          obtain ⟨m, hum⟩ := ih htail
          refine ⟨m + 1, ?_⟩
          subst t
          rw [hum]
          simp [List.replicate_succ, Nat.add_comm]

/--
Generic right-shape lemma, obtained by reversing the word and reusing
'prefix_context_is_power'.
-/
theorem suffix_context_is_power
    (left right z z' : LpmSymbol)
    (hzleft : z ≠ left)
    {i j p q : Nat}
    {u v : Word LpmSymbol}
    (h :
      u ++
          (List.replicate i left ++ [z] ++
            List.replicate j right) ++
          v =
        List.replicate p left ++ [z'] ++
          List.replicate q right) :
    ∃ n : Nat, v = List.replicate n right := by
  have hrev :
      v.reverse ++
          (List.replicate j right ++ [z] ++
            List.replicate i left) ++
          u.reverse =
        List.replicate q right ++ [z'] ++
          List.replicate p left := by
    have hr := congrArg List.reverse h
    simpa [List.reverse_append, List.append_assoc] using hr
  obtain ⟨n, hvrev⟩ :=
    prefix_context_is_power
      right left z z' hzleft
      (i := j) (j := i) (p := q) (q := p)
      (u := v.reverse) (v := u.reverse)
      hrev
  have hrv := congrArg List.reverse hvrev
  refine ⟨n, ?_⟩
  simpa using hrv

/-- Elementary list decomposition used by the factor-shape proof. -/
theorem exists_split_around_mem
    {z : LpmSymbol}
    {x : Word LpmSymbol}
    (hzx : z ∈ x) :
    ∃ l r : Word LpmSymbol, x = l ++ z :: r := by
  induction x with
  | nil =>
      simp at hzx
  | cons t x ih =>
      simp only [List.mem_cons] at hzx
      rcases hzx with rfl | hzx
      · exact ⟨[], x, rfl⟩
      · obtain ⟨l, r, hlr⟩ := ih hzx
        refine ⟨t :: l, r, ?_⟩
        simp [hlr]

/--
A center-containing factor inside an L_{±,e} word has a pure-a left context
and a pure-b right context.
-/
theorem lpm_center_context_shape
    {u v : Word LpmSymbol}
    {i j : Nat}
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hmem :
      u ++ lpmOneCenter i z j ++ v ∈
        LpmLanguage) :
    ∃ m n : Nat,
      u = List.replicate m a ∧
      v = List.replicate n b := by
  rcases hmem with ⟨N, z', hword, hacc⟩
  have hleft :
      ∃ m : Nat, u = List.replicate m a := by
    apply
      prefix_context_is_power
        a b z z' (center_ne_b hz)
        (i := i) (j := j) (p := N) (q := N)
        (u := u) (v := v)
    simpa [lpmOneCenter, lpmCore, List.append_assoc]
      using hword
  obtain ⟨m, hum⟩ := hleft

  have hrev :
      v.reverse ++
          (List.replicate j b ++ [z] ++
            List.replicate i a) ++
          u.reverse =
        List.replicate N b ++ [z'] ++
          List.replicate N a := by
    have hr := congrArg List.reverse hword
    simpa [lpmOneCenter, lpmCore, List.reverse_append,
      List.append_assoc] using hr

  have hrightRev :
      ∃ n : Nat, v.reverse = List.replicate n b := by
    exact
      prefix_context_is_power
        b a z z' (center_ne_a hz)
        (i := j) (j := i) (p := N) (q := N)
        (u := v.reverse) (v := u.reverse)
        hrev
  obtain ⟨n, hvrev⟩ := hrightRev
  have hvn : v = List.replicate n b := by
    have hrv := congrArg List.reverse hvrev
    simpa using hrv
  exact ⟨m, n, hum, hvn⟩

/-- Distribution-facing form of the context-shape lemma. -/
theorem lpm_distribution_context_shape
    {u v : Word LpmSymbol}
    {i j : Nat}
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hctx :
      (u, v) ∈
        Distribution LpmLanguage
          (lpmOneCenter i z j)) :
    ∃ m n : Nat,
      u = List.replicate m a ∧
      v = List.replicate n b := by
  exact
    lpm_center_context_shape hz hctx
/--
Any factor of an L_{±,e} word that contains a specified center symbol has
the canonical one-center shape a^i z b^j; the surrounding context is
simultaneously a pure a-prefix and pure b-suffix.
-/
theorem lpm_factor_shape_of_center_mem
    {u x v : Word LpmSymbol}
    {z : LpmSymbol}
    (hz : LpmCenterSymbol z)
    (hzx : z ∈ x)
    (hmem : u ++ x ++ v ∈ LpmLanguage) :
    ∃ m i j n : Nat,
      u = List.replicate m a ∧
      x = lpmOneCenter i z j ∧
      v = List.replicate n b := by
  obtain ⟨xL, xR, hxsplit⟩ :=
    exists_split_around_mem hzx
  subst x
  rcases hmem with ⟨N, z', hword, hacc⟩

  have hwhole :
      (u ++ xL) ++
          ([] ++ [z] ++ []) ++
          (xR ++ v) =
        List.replicate N a ++ [z'] ++
          List.replicate N b := by
    simpa [lpmCore, List.append_assoc] using hword

  obtain ⟨M, hprefix⟩ :=
    prefix_context_is_power
      a b z z' (center_ne_b hz)
      (i := 0) (j := 0) (p := N) (q := N)
      (u := u ++ xL) (v := xR ++ v)
      hwhole
  obtain ⟨K, hsuffix⟩ :=
    suffix_context_is_power
      a b z z' (center_ne_a hz)
      (i := 0) (j := 0) (p := N) (q := N)
      (u := u ++ xL) (v := xR ++ v)
      hwhole

  have hprefSub :
      u ++ xL ⊆ [a] := by
    rw [hprefix]
    exact List.replicate_subset_singleton M a
  have huSub : u ⊆ [a] := by
    intro t ht
    exact hprefSub (by simp [ht])
  have hxLSub : xL ⊆ [a] := by
    intro t ht
    exact hprefSub (by simp [ht])
  obtain ⟨m, hum⟩ :=
    List.subset_singleton_iff.mp huSub
  obtain ⟨i, hxLi⟩ :=
    List.subset_singleton_iff.mp hxLSub

  have hsufSub :
      xR ++ v ⊆ [b] := by
    rw [hsuffix]
    exact List.replicate_subset_singleton K b
  have hxRSub : xR ⊆ [b] := by
    intro t ht
    exact hsufSub (by simp [ht])
  have hvSub : v ⊆ [b] := by
    intro t ht
    exact hsufSub (by simp [ht])
  obtain ⟨j, hxRj⟩ :=
    List.subset_singleton_iff.mp hxRSub
  obtain ⟨n, hvn⟩ :=
    List.subset_singleton_iff.mp hvSub

  refine ⟨m, i, j, n, hum, ?_, hvn⟩
  simp [lpmOneCenter, hxLi, hxRj]


end TCS1
end LeanCfgProject
