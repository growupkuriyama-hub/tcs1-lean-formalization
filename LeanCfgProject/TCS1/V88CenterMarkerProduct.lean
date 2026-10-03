import LeanCfgProject.TCS1.V88CenterMarkerBase

/-!
# TCS #1 v88: substitutability of the center-marker product

This module formalizes the second new claim in the v88 Section 10.1
comparison paragraph.  With

  P = { a^n c b^n : n >= 0 }

and a fresh separator d, define

  L_x = P d P.

The manuscript argues that L_x is ordinarily substitutable.  The proof below
follows that argument literally: words of L_x have a unique d; factors which
avoid d reduce to the already-verified substitutability of P; factors which
contain d split into independent left and right P-factors.  Prefix/suffix
freeness of P handles the endpoint cases where one of these pieces is empty.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- The marked product L_x = P d P used in the v88 comparison paragraph. -/
def CenterMarkerProductLanguage : Set (Word LpmSymbol) :=
  { w |
      ∃ n m : Nat,
        w = lpmCore n c ++ [d] ++ lpmCore m c }

/-- The separator d never occurs in a P-word. -/
theorem centerMarker_not_mem_d
    {w : Word LpmSymbol}
    (hw : w ∈ CenterMarkerLanguage) :
    d ∉ w := by
  rcases hw with ⟨n, rfl⟩
  simp [lpmCore]

/-- Every marked-product word contains exactly one d. -/
theorem centerMarkerProduct_count_d_eq_one
    {w : Word LpmSymbol}
    (hw : w ∈ CenterMarkerProductLanguage) :
    w.count d = 1 := by
  rcases hw with ⟨n, m, rfl⟩
  simp [lpmCore, List.count_append, List.count_replicate]

/-- Assemble a marked-product word from two P-words. -/
theorem centerMarkerProduct_of_parts
    {left right : Word LpmSymbol}
    (hleft : left ∈ CenterMarkerLanguage)
    (hright : right ∈ CenterMarkerLanguage) :
    left ++ [d] ++ right ∈ CenterMarkerProductLanguage := by
  rcases hleft with ⟨n, rfl⟩
  rcases hright with ⟨m, rfl⟩
  exact ⟨n, m, rfl⟩

/--
Uniqueness of a distinguished separator in lists: if neither side contains
z, two decompositions around z have the same left and right pieces.
-/
theorem unique_singleton_split
    {z : LpmSymbol}
    {l r l' r' : Word LpmSymbol}
    (hzl : z ∉ l)
    (hzr : z ∉ r)
    (hzl' : z ∉ l')
    (hzr' : z ∉ r')
    (h :
      l ++ [z] ++ r =
        l' ++ [z] ++ r') :
    l = l' ∧ r = r' := by
  induction l generalizing l' with
  | nil =>
      cases l' with
      | nil =>
          simpa using h
      | cons t l' =>
          have hhead : z = t := by
            simpa using congrArg List.head? h
          subst t
          exact False.elim (hzl' (by simp))
  | cons t l ih =>
      cases l' with
      | nil =>
          have hhead : t = z := by
            simpa using congrArg List.head? h
          subst t
          exact False.elim (hzl (by simp))
      | cons t' l' =>
          have hcons :
              t :: (l ++ [z] ++ r) =
                t' :: (l' ++ [z] ++ r') := by
            simpa [List.append_assoc] using h
          have htt : t = t' := (List.cons.inj hcons).1
          have htail :
              l ++ [z] ++ r =
                l' ++ [z] ++ r' :=
            (List.cons.inj hcons).2
          have hzlTail : z ∉ l := by
            intro hz
            exact hzl (by simp [hz])
          have hzl'Tail : z ∉ l' := by
            intro hz
            exact hzl' (by simp [hz])
          obtain ⟨hl, hr⟩ :=
            ih hzlTail hzr hzl'Tail hzr' htail
          subst t'
          subst l'
          exact ⟨rfl, hr⟩

/--
Exact semantic split at the unique d of L_x, provided the displayed left and
right pieces themselves avoid d.
-/
theorem centerMarkerProduct_split_iff
    {left right : Word LpmSymbol}
    (hleftd : d ∉ left)
    (hrightd : d ∉ right) :
    left ++ [d] ++ right ∈ CenterMarkerProductLanguage ↔
      left ∈ CenterMarkerLanguage ∧
      right ∈ CenterMarkerLanguage := by
  constructor
  · rintro ⟨n, m, hword⟩
    have hcoreN : d ∉ lpmCore n c := by
      simp [lpmCore]
    have hcoreM : d ∉ lpmCore m c := by
      simp [lpmCore]
    obtain ⟨hl, hr⟩ :=
      unique_singleton_split
        hleftd hrightd hcoreN hcoreM hword
    subst left
    subst right
    exact ⟨centerMarker_core_mem n, centerMarker_core_mem m⟩
  · rintro ⟨hl, hr⟩
    exact centerMarkerProduct_of_parts hl hr

/--
If a marked-product word is displayed as left d right, the two outer pieces
cannot contain another d.
-/
theorem centerMarkerProduct_outer_d_free
    {w left right : Word LpmSymbol}
    (hw : w ∈ CenterMarkerProductLanguage)
    (hword : w = left ++ [d] ++ right) :
    d ∉ left ∧ d ∉ right := by
  have hcount := centerMarkerProduct_count_d_eq_one hw
  rw [hword] at hcount
  simp only [List.count_append, List.count_cons, List.count_nil,
    if_pos rfl, Nat.add_zero] at hcount
  constructor
  · intro hd
    have hpos : 0 < left.count d :=
      List.count_pos_iff.mpr hd
    omega
  · intro hd
    have hpos : 0 < right.count d :=
      List.count_pos_iff.mpr hd
    omega

/-- P is prefix-free. -/
theorem centerMarker_prefix_free
    {p q : Word LpmSymbol}
    (hp : p ∈ CenterMarkerLanguage)
    (hq : q ∈ CenterMarkerLanguage)
    (hpq : p <+: q) :
    p = q := by
  rcases hpq with ⟨rest, hqeq⟩
  have hp0 := centerMarkerBalance_mem_zero hp
  have hq0 := centerMarkerBalance_mem_zero hq
  rcases hp with ⟨n, hpShape⟩
  have hpRest :
      p ++ rest ∈ CenterMarkerLanguage := by
    rw [hqeq]
    exact hq
  have hctx :
      ([] : Word LpmSymbol) ++ lpmOneCenter n c n ++ rest ∈
        CenterMarkerLanguage := by
    rw [lpmOneCenter_balanced, ← hpShape]
    simpa using hpRest
  obtain ⟨_m, k, _hempty, hrest⟩ :=
    centerMarker_context_shape hctx
  have hrestBal :
      lpmBalance rest = 0 := by
    rw [← hqeq] at hq0
    simpa [lpmBalance_append, hp0] using hq0
  rw [hrest] at hrestBal
  simp at hrestBal
  have hk : k = 0 := by omega
  subst k
  simp at hrest
  subst rest
  simpa using hqeq

/-- P is suffix-free. -/
theorem centerMarker_suffix_free
    {p q : Word LpmSymbol}
    (hp : p ∈ CenterMarkerLanguage)
    (hq : q ∈ CenterMarkerLanguage)
    (hpq : p <:+ q) :
    p = q := by
  rcases hpq with ⟨left, hqeq⟩
  have hp0 := centerMarkerBalance_mem_zero hp
  have hq0 := centerMarkerBalance_mem_zero hq
  rcases hp with ⟨n, hpShape⟩
  have hleftP :
      left ++ p ∈ CenterMarkerLanguage := by
    rw [hqeq]
    exact hq
  have hctx :
      left ++ lpmOneCenter n c n ++ ([] : Word LpmSymbol) ∈
        CenterMarkerLanguage := by
    rw [lpmOneCenter_balanced, ← hpShape]
    simpa using hleftP
  obtain ⟨k, _m, hleft, _hempty⟩ :=
    centerMarker_context_shape hctx
  have hleftBal :
      lpmBalance left = 0 := by
    rw [← hqeq] at hq0
    simpa [lpmBalance_append, hp0] using hq0
  rw [hleft] at hleftBal
  simp at hleftBal
  have hk : k = 0 := by omega
  subst k
  simp at hleft
  subst left
  simpa using hqeq

/--
Substitutability of P can also be used when the compared factors might be
empty, provided shared-context information shows that they are empty
simultaneously.
-/
theorem centerMarker_distribution_eq_allow_empty
    {x y : Word LpmSymbol}
    (hempty : x = [] ↔ y = [])
    (hshared : HaveSharedContext CenterMarkerLanguage x y) :
    Distribution CenterMarkerLanguage x =
      Distribution CenterMarkerLanguage y := by
  by_cases hx : x = []
  · have hy : y = [] := hempty.mp hx
    subst x
    subst y
    rfl
  · have hy : y ≠ [] := by
      intro hy0
      exact hx (hempty.mpr hy0)
    exact centerMarker_clarkEyraud hx hy hshared

/--
When a shared L_x-factor avoids d, its common occurrence induces a shared
P-context on whichever side of the unique separator contains the factor.
-/
theorem centerMarkerProduct_avoiding_d_distribution_eq
    {x y : Word LpmSymbol}
    (hxne : x ≠ [])
    (hyne : y ≠ [])
    (hxd : d ∉ x)
    (hyd : d ∉ y)
    (hshared : HaveSharedContext CenterMarkerProductLanguage x y) :
    Distribution CenterMarkerProductLanguage x =
      Distribution CenterMarkerProductLanguage y := by
  rcases hshared with ⟨u, v, hxL, hyL⟩
  have hdwhole : d ∈ u ++ x ++ v := by
    have hc := centerMarkerProduct_count_d_eq_one hxL
    apply List.count_pos_iff.mp
    omega
  have hcases : (d ∈ u ∨ d ∈ x) ∨ d ∈ v := by
    simpa only [List.mem_append] using hdwhole

  have hdistP :
      Distribution CenterMarkerLanguage x =
        Distribution CenterMarkerLanguage y := by
    rcases hcases with (hdu | hdx) | hdv
    · obtain ⟨uL, uR, hu⟩ := exists_split_around_mem hdu
      have hxEq :
          u ++ x ++ v =
            uL ++ [d] ++ (uR ++ x ++ v) := by
        rw [hu]
        simp [List.append_assoc]
      have hyEq :
          u ++ y ++ v =
            uL ++ [d] ++ (uR ++ y ++ v) := by
        rw [hu]
        simp [List.append_assoc]
      have hxfree :=
        centerMarkerProduct_outer_d_free hxL hxEq
      have hyfree :=
        centerMarkerProduct_outer_d_free hyL hyEq
      have hxparts :=
        (centerMarkerProduct_split_iff hxfree.1 hxfree.2).1
          (by simpa [hxEq] using hxL)
      have hyparts :=
        (centerMarkerProduct_split_iff hyfree.1 hyfree.2).1
          (by simpa [hyEq] using hyL)
      exact
        centerMarker_clarkEyraud hxne hyne
          ⟨uR, v, hxparts.2, hyparts.2⟩
    · exact False.elim (hxd hdx)
    · obtain ⟨vL, vR, hv⟩ := exists_split_around_mem hdv
      have hxEq :
          u ++ x ++ v =
            (u ++ x ++ vL) ++ [d] ++ vR := by
        rw [hv]
        simp [List.append_assoc]
      have hyEq :
          u ++ y ++ v =
            (u ++ y ++ vL) ++ [d] ++ vR := by
        rw [hv]
        simp [List.append_assoc]
      have hxfree :=
        centerMarkerProduct_outer_d_free hxL hxEq
      have hyfree :=
        centerMarkerProduct_outer_d_free hyL hyEq
      have hxparts :=
        (centerMarkerProduct_split_iff hxfree.1 hxfree.2).1
          (by simpa [hxEq] using hxL)
      have hyparts :=
        (centerMarkerProduct_split_iff hyfree.1 hyfree.2).1
          (by simpa [hyEq] using hyL)
      exact
        centerMarker_clarkEyraud hxne hyne
          ⟨u, vL, hxparts.1, hyparts.1⟩

  apply Set.ext
  rintro ⟨p, q⟩
  change
    (p ++ x ++ q ∈ CenterMarkerProductLanguage) ↔
      (p ++ y ++ q ∈ CenterMarkerProductLanguage)
  constructor
  · intro hxctx
    have hdctx : d ∈ p ++ x ++ q := by
      have hc := centerMarkerProduct_count_d_eq_one hxctx
      apply List.count_pos_iff.mp
      omega
    have hctxCases : (d ∈ p ∨ d ∈ x) ∨ d ∈ q := by
      simpa only [List.mem_append] using hdctx
    rcases hctxCases with (hdp | hdx') | hdq
    · obtain ⟨pL, pR, hp⟩ := exists_split_around_mem hdp
      have hEq :
          p ++ x ++ q =
            pL ++ [d] ++ (pR ++ x ++ q) := by
        rw [hp]
        simp [List.append_assoc]
      have hfree :=
        centerMarkerProduct_outer_d_free hxctx hEq
      have hparts :=
        (centerMarkerProduct_split_iff hfree.1 hfree.2).1
          (by simpa [hEq] using hxctx)
      have hPx :
          (pR, q) ∈ Distribution CenterMarkerLanguage x := by
        simpa [Distribution, List.append_assoc] using hparts.2
      have hPy :
          (pR, q) ∈ Distribution CenterMarkerLanguage y := by
        rw [← hdistP]
        exact hPx
      have hrightY :
          pR ++ y ++ q ∈ CenterMarkerLanguage := by
        simpa [Distribution, List.append_assoc] using hPy
      have hout :=
        centerMarkerProduct_of_parts hparts.1 hrightY
      rw [hp]
      simpa [List.append_assoc] using hout
    · exact False.elim (hxd hdx')
    · obtain ⟨qL, qR, hq⟩ := exists_split_around_mem hdq
      have hEq :
          p ++ x ++ q =
            (p ++ x ++ qL) ++ [d] ++ qR := by
        rw [hq]
        simp [List.append_assoc]
      have hfree :=
        centerMarkerProduct_outer_d_free hxctx hEq
      have hparts :=
        (centerMarkerProduct_split_iff hfree.1 hfree.2).1
          (by simpa [hEq] using hxctx)
      have hPx :
          (p, qL) ∈ Distribution CenterMarkerLanguage x := by
        simpa [Distribution, List.append_assoc] using hparts.1
      have hPy :
          (p, qL) ∈ Distribution CenterMarkerLanguage y := by
        rw [← hdistP]
        exact hPx
      have hleftY :
          p ++ y ++ qL ∈ CenterMarkerLanguage := by
        simpa [Distribution, List.append_assoc] using hPy
      have hout :=
        centerMarkerProduct_of_parts hleftY hparts.2
      rw [hq]
      simpa [List.append_assoc] using hout
  · intro hyctx
    have hdistSym :
        Distribution CenterMarkerLanguage y =
          Distribution CenterMarkerLanguage x :=
      hdistP.symm
    have hdctx : d ∈ p ++ y ++ q := by
      have hc := centerMarkerProduct_count_d_eq_one hyctx
      apply List.count_pos_iff.mp
      omega
    have hctxCases : (d ∈ p ∨ d ∈ y) ∨ d ∈ q := by
      simpa only [List.mem_append] using hdctx
    rcases hctxCases with (hdp | hdy') | hdq
    · obtain ⟨pL, pR, hp⟩ := exists_split_around_mem hdp
      have hEq :
          p ++ y ++ q =
            pL ++ [d] ++ (pR ++ y ++ q) := by
        rw [hp]
        simp [List.append_assoc]
      have hfree :=
        centerMarkerProduct_outer_d_free hyctx hEq
      have hparts :=
        (centerMarkerProduct_split_iff hfree.1 hfree.2).1
          (by simpa [hEq] using hyctx)
      have hPy :
          (pR, q) ∈ Distribution CenterMarkerLanguage y := by
        simpa [Distribution, List.append_assoc] using hparts.2
      have hPx :
          (pR, q) ∈ Distribution CenterMarkerLanguage x := by
        rw [← hdistSym]
        exact hPy
      have hrightX :
          pR ++ x ++ q ∈ CenterMarkerLanguage := by
        simpa [Distribution, List.append_assoc] using hPx
      have hout :=
        centerMarkerProduct_of_parts hparts.1 hrightX
      rw [hp]
      simpa [List.append_assoc] using hout
    · exact False.elim (hyd hdy')
    · obtain ⟨qL, qR, hq⟩ := exists_split_around_mem hdq
      have hEq :
          p ++ y ++ q =
            (p ++ y ++ qL) ++ [d] ++ qR := by
        rw [hq]
        simp [List.append_assoc]
      have hfree :=
        centerMarkerProduct_outer_d_free hyctx hEq
      have hparts :=
        (centerMarkerProduct_split_iff hfree.1 hfree.2).1
          (by simpa [hEq] using hyctx)
      have hPy :
          (p, qL) ∈ Distribution CenterMarkerLanguage y := by
        simpa [Distribution, List.append_assoc] using hparts.1
      have hPx :
          (p, qL) ∈ Distribution CenterMarkerLanguage x := by
        rw [← hdistSym]
        exact hPy
      have hleftX :
          p ++ x ++ qL ∈ CenterMarkerLanguage := by
        simpa [Distribution, List.append_assoc] using hPx
      have hout :=
        centerMarkerProduct_of_parts hleftX hparts.2
      rw [hq]
      simpa [List.append_assoc] using hout

/--
When shared factors contain d, the pieces on each side of d have equal
P-distributions, including the possible empty endpoint cases.
-/
theorem centerMarkerProduct_containing_d_distribution_eq
    {x y : Word LpmSymbol}
    (hdx : d ∈ x)
    (hdy : d ∈ y)
    (hshared : HaveSharedContext CenterMarkerProductLanguage x y) :
    Distribution CenterMarkerProductLanguage x =
      Distribution CenterMarkerProductLanguage y := by
  obtain ⟨x1, x2, hxsplit⟩ := exists_split_around_mem hdx
  obtain ⟨y1, y2, hysplit⟩ := exists_split_around_mem hdy
  rcases hshared with ⟨u, v, hxL, hyL⟩

  have hxEq :
      u ++ x ++ v =
        (u ++ x1) ++ [d] ++ (x2 ++ v) := by
    rw [hxsplit]
    simp [List.append_assoc]
  have hyEq :
      u ++ y ++ v =
        (u ++ y1) ++ [d] ++ (y2 ++ v) := by
    rw [hysplit]
    simp [List.append_assoc]

  have hxfree :=
    centerMarkerProduct_outer_d_free hxL hxEq
  have hyfree :=
    centerMarkerProduct_outer_d_free hyL hyEq
  have hxparts :=
    (centerMarkerProduct_split_iff hxfree.1 hxfree.2).1
      (by simpa [hxEq] using hxL)
  have hyparts :=
    (centerMarkerProduct_split_iff hyfree.1 hyfree.2).1
      (by simpa [hyEq] using hyL)

  have hleftEmpty : x1 = [] ↔ y1 = [] := by
    constructor
    · intro hx1
      subst x1
      have hpref :
          u <+: u ++ y1 := ⟨y1, rfl⟩
      have heq :=
        centerMarker_prefix_free
          (by simpa using hxparts.1)
          hyparts.1 hpref
      have : y1 = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlen := congrArg List.length heq
        simp at hlen
        omega
      exact this
    · intro hy1
      subst y1
      have hpref :
          u <+: u ++ x1 := ⟨x1, rfl⟩
      have heq :=
        centerMarker_prefix_free
          (by simpa using hyparts.1)
          hxparts.1 hpref
      have : x1 = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlen := congrArg List.length heq
        simp at hlen
        omega
      exact this

  have hrightEmpty : x2 = [] ↔ y2 = [] := by
    constructor
    · intro hx2
      subst x2
      have hsuf :
          v <:+ y2 ++ v := ⟨y2, rfl⟩
      have heq :=
        centerMarker_suffix_free
          (by simpa using hxparts.2)
          hyparts.2 hsuf
      have : y2 = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlen := congrArg List.length heq
        simp at hlen
        omega
      exact this
    · intro hy2
      subst y2
      have hsuf :
          v <:+ x2 ++ v := ⟨x2, rfl⟩
      have heq :=
        centerMarker_suffix_free
          (by simpa using hyparts.2)
          hxparts.2 hsuf
      have : x2 = [] := by
        apply List.eq_nil_of_length_eq_zero
        have hlen := congrArg List.length heq
        simp at hlen
        omega
      exact this

  have hdistLeft :
      Distribution CenterMarkerLanguage x1 =
        Distribution CenterMarkerLanguage y1 :=
    centerMarker_distribution_eq_allow_empty
      hleftEmpty
      ⟨u, [], by simpa using hxparts.1, by simpa using hyparts.1⟩

  have hdistRight :
      Distribution CenterMarkerLanguage x2 =
        Distribution CenterMarkerLanguage y2 :=
    centerMarker_distribution_eq_allow_empty
      hrightEmpty
      ⟨[], v, by simpa using hxparts.2, by simpa using hyparts.2⟩

  apply Set.ext
  rintro ⟨p, q⟩
  change
    (p ++ x ++ q ∈ CenterMarkerProductLanguage) ↔
      (p ++ y ++ q ∈ CenterMarkerProductLanguage)
  constructor
  · intro hxctx
    have hEq :
        p ++ x ++ q =
          (p ++ x1) ++ [d] ++ (x2 ++ q) := by
      rw [hxsplit]
      simp [List.append_assoc]
    have hfree :=
      centerMarkerProduct_outer_d_free hxctx hEq
    have hparts :=
      (centerMarkerProduct_split_iff hfree.1 hfree.2).1
        (by simpa [hEq] using hxctx)
    have hleftX :
        (p, []) ∈ Distribution CenterMarkerLanguage x1 := by
      simpa [Distribution, List.append_assoc] using hparts.1
    have hleftY :
        (p, []) ∈ Distribution CenterMarkerLanguage y1 := by
      rw [← hdistLeft]
      exact hleftX
    have hrightX :
        ([], q) ∈ Distribution CenterMarkerLanguage x2 := by
      simpa [Distribution, List.append_assoc] using hparts.2
    have hrightY :
        ([], q) ∈ Distribution CenterMarkerLanguage y2 := by
      rw [← hdistRight]
      exact hrightX
    have hout :=
      centerMarkerProduct_of_parts
        (by simpa [Distribution, List.append_assoc] using hleftY)
        (by simpa [Distribution, List.append_assoc] using hrightY)
    rw [hysplit]
    simpa [List.append_assoc] using hout
  · intro hyctx
    have hEq :
        p ++ y ++ q =
          (p ++ y1) ++ [d] ++ (y2 ++ q) := by
      rw [hysplit]
      simp [List.append_assoc]
    have hfree :=
      centerMarkerProduct_outer_d_free hyctx hEq
    have hparts :=
      (centerMarkerProduct_split_iff hfree.1 hfree.2).1
        (by simpa [hEq] using hyctx)
    have hleftY :
        (p, []) ∈ Distribution CenterMarkerLanguage y1 := by
      simpa [Distribution, List.append_assoc] using hparts.1
    have hleftX :
        (p, []) ∈ Distribution CenterMarkerLanguage x1 := by
      rw [hdistLeft]
      exact hleftY
    have hrightY :
        ([], q) ∈ Distribution CenterMarkerLanguage y2 := by
      simpa [Distribution, List.append_assoc] using hparts.2
    have hrightX :
        ([], q) ∈ Distribution CenterMarkerLanguage x2 := by
      rw [hdistRight]
      exact hrightY
    have hout :=
      centerMarkerProduct_of_parts
        (by simpa [Distribution, List.append_assoc] using hleftX)
        (by simpa [Distribution, List.append_assoc] using hrightX)
    rw [hxsplit]
    simpa [List.append_assoc] using hout

/-- The v88 marked product L_x is ordinarily Clark--Eyraud substitutable. -/
theorem centerMarkerProduct_clarkEyraud :
    ClarkEyraudSubstitutableOn CenterMarkerProductLanguage := by
  intro x y hxne hyne hshared
  have hcount : x.count d = y.count d := by
    rcases hshared with ⟨u, v, hxL, hyL⟩
    have hcx := centerMarkerProduct_count_d_eq_one hxL
    have hcy := centerMarkerProduct_count_d_eq_one hyL
    simp only [List.count_append] at hcx hcy
    omega
  by_cases hdx : d ∈ x
  · have hdy : d ∈ y := by
      have hxpos : 0 < x.count d :=
        List.count_pos_iff.mpr hdx
      have hypos : 0 < y.count d := by
        rw [← hcount]
        exact hxpos
      exact List.count_pos_iff.mp hypos
    exact
      centerMarkerProduct_containing_d_distribution_eq
        hdx hdy hshared
  · have hdy : d ∉ y := by
      intro hdy
      have hypos : 0 < y.count d :=
        List.count_pos_iff.mpr hdy
      have hxpos : 0 < x.count d := by
        rw [hcount]
        exact hypos
      exact hdx (List.count_pos_iff.mp hxpos)
    exact
      centerMarkerProduct_avoiding_d_distribution_eq
        hxne hyne hdx hdy hshared

/-- Therefore L_x is in the concrete (0,0) fixed-window class. -/
theorem centerMarkerProduct_zeroWindow :
    FixedWindowSubstitutable 0 0 CenterMarkerProductLanguage := by
  rw [zeroWindowSubstitutable_iff_nonemptyFactorSubstitutable]
  exact centerMarkerProduct_clarkEyraud

end TCS1
end LeanCfgProject
