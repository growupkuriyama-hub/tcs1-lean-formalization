import LeanCfgProject.TCS1.V88CenterMarkerGrammar
import LeanCfgProject.TCS1.DeltaStarDoubleDeltaNonlinear
import LeanCfgProject.TCS1.RawLinearPumping

/-!
# TCS #1 v88: nonlinearity of the center-marker product

This module closes the final mathematical claim in the revised Section 10.1
comparison.  The manuscript observes that erasing c,d,e maps

  L_x = { a^n c b^n d a^m c b^m : n,m >= 0 }

onto Double-Delta.  We verify that erasing-image identity explicitly.

For the nonlinearity conclusion itself we also give a fully internal proof,
rather than leave homomorphic closure of linear languages as an external
background theorem.  The proof applies the already verified bounded pumping
property for arbitrary finite raw-linear presentations directly to L_x.
Pumping down a sufficiently long symmetric witness can change only the first
a-block and the final b-block; membership in L_x then forces both pumped
pieces to have length zero, contradicting the pumping lemma.
-/

namespace LeanCfgProject
namespace TCS1

open LpmSymbol

/-- The erasing homomorphism used in the manuscript comparison. -/
def centerMarkerEraseLetter :
    LpmSymbol -> Word DeltaStar.Symbol
  | .a => [DeltaStar.Symbol.a]
  | .b => [DeltaStar.Symbol.b]
  | .c => []
  | .d => []
  | .e => []

/-- Extension of the erasing homomorphism from letters to words. -/
def centerMarkerErase :
    Word LpmSymbol -> Word DeltaStar.Symbol
  | [] => []
  | x :: xs =>
      centerMarkerEraseLetter x ++ centerMarkerErase xs

@[simp] theorem centerMarkerErase_nil :
    centerMarkerErase ([] : Word LpmSymbol) = [] := by
  rfl

@[simp] theorem centerMarkerErase_cons
    (x : LpmSymbol)
    (xs : Word LpmSymbol) :
    centerMarkerErase (x :: xs) =
      centerMarkerEraseLetter x ++ centerMarkerErase xs := by
  rfl

@[simp] theorem centerMarkerErase_append
    (u v : Word LpmSymbol) :
    centerMarkerErase (u ++ v) =
      centerMarkerErase u ++ centerMarkerErase v := by
  induction u with
  | nil => rfl
  | cons x xs ih =>
      simp [centerMarkerErase, ih, List.append_assoc]

@[simp] theorem centerMarkerErase_replicate_a
    (n : Nat) :
    centerMarkerErase (List.replicate n LpmSymbol.a) =
      List.replicate n DeltaStar.Symbol.a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, centerMarkerEraseLetter, ih]

@[simp] theorem centerMarkerErase_replicate_b
    (n : Nat) :
    centerMarkerErase (List.replicate n LpmSymbol.b) =
      List.replicate n DeltaStar.Symbol.b := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [List.replicate_succ, centerMarkerEraseLetter, ih]

@[simp] theorem centerMarkerErase_lpmCore
    (n : Nat) :
    centerMarkerErase (lpmCore n LpmSymbol.c) =
      DeltaStar.balancedBlock n := by
  simp [lpmCore, DeltaStar.balancedBlock,
    centerMarkerErase, centerMarkerEraseLetter, List.append_assoc]

/-- The manuscript's erasing homomorphism maps L_x exactly onto Double-Delta. -/
theorem centerMarkerProduct_erase_image_eq_doubleDelta :
    { w : Word DeltaStar.Symbol |
        exists x : Word LpmSymbol,
          x ∈ CenterMarkerProductLanguage /\
          centerMarkerErase x = w } =
      DeltaStar.DoubleDeltaLanguage := by
  apply Set.ext
  intro w
  constructor
  · rintro ⟨x, ⟨n, m, rfl⟩, rfl⟩
    exact ⟨n, m, by
      simp [centerMarkerErase, centerMarkerEraseLetter,
        DeltaStar.balancedBlock, List.append_assoc]⟩
  · rintro ⟨n, m, rfl⟩
    refine
      ⟨lpmCore n LpmSymbol.c ++ [LpmSymbol.d] ++
          lpmCore m LpmSymbol.c,
        ⟨n, m, rfl⟩,
        ?_⟩
    simp [centerMarkerErase, centerMarkerEraseLetter,
      DeltaStar.balancedBlock, List.append_assoc]

/-- Symmetric long witness used in the direct pumping contradiction. -/
def centerMarkerProductWitness
    (N : Nat) :
    Word LpmSymbol :=
  lpmCore N LpmSymbol.c ++
    [LpmSymbol.d] ++
      lpmCore N LpmSymbol.c

theorem centerMarkerProductWitness_mem
    (N : Nat) :
    centerMarkerProductWitness N ∈
      CenterMarkerProductLanguage := by
  exact ⟨N, N, rfl⟩

/-- A short prefix of the witness lies entirely in its first a-block. -/
theorem centerMarkerProductWitness_take
    (N m : Nat)
    (hm : m ≤ N) :
    (centerMarkerProductWitness N).take m =
      List.replicate m LpmSymbol.a := by
  have hshape :
      centerMarkerProductWitness N =
        List.replicate N LpmSymbol.a ++
          ([LpmSymbol.c] ++
            List.replicate N LpmSymbol.b ++
              [LpmSymbol.d] ++
                List.replicate N LpmSymbol.a ++
                  [LpmSymbol.c] ++
                    List.replicate N LpmSymbol.b) := by
    simp [centerMarkerProductWitness, lpmCore,
      List.append_assoc]
  rw [hshape]
  rw [List.take_append_of_le_length]
  · rw [List.take_replicate]
    congr
    omega
  · simpa using hm

/-- A short reversed prefix lies entirely in the final b-block. -/
theorem centerMarkerProductWitness_reverse_take
    (N m : Nat)
    (hm : m ≤ N) :
    (centerMarkerProductWitness N).reverse.take m =
      List.replicate m LpmSymbol.b := by
  have hshape :
      (centerMarkerProductWitness N).reverse =
        List.replicate N LpmSymbol.b ++
          ([LpmSymbol.c] ++
            List.replicate N LpmSymbol.a ++
              [LpmSymbol.d] ++
                List.replicate N LpmSymbol.b ++
                  [LpmSymbol.c] ++
                    List.replicate N LpmSymbol.a) := by
    simp [centerMarkerProductWitness, lpmCore,
      List.reverse_append, List.append_assoc]
  rw [hshape]
  rw [List.take_append_of_le_length]
  · rw [List.take_replicate]
    congr
    omega
  · simpa using hm

/--
Pumping down a bounded decomposition of the symmetric witness changes only
the first a-block and the final b-block.
-/
theorem centerMarkerProduct_pumpDown_shape
    (N : Nat)
    {u v x y z : Word LpmSymbol}
    (hdecomp :
      centerMarkerProductWitness N =
        u ++ v ++ x ++ y ++ z)
    (houter :
      (u ++ v).length < N)
    (hinner :
      (y ++ z).length < N) :
    u ++ x ++ z =
      List.replicate (N - v.length) LpmSymbol.a ++
        [LpmSymbol.c] ++
          List.replicate N LpmSymbol.b ++
            [LpmSymbol.d] ++
              List.replicate N LpmSymbol.a ++
                [LpmSymbol.c] ++
                  List.replicate (N - y.length) LpmSymbol.b := by
  have hpre :
      u ++ v <+:
        centerMarkerProductWitness N :=
    ⟨x ++ y ++ z, by
      rw [hdecomp]
      simp [List.append_assoc]⟩
  have huv :
      u ++ v =
        List.replicate (u ++ v).length LpmSymbol.a :=
    (List.prefix_iff_eq_take.1 hpre).trans
      (centerMarkerProductWitness_take N
        (u ++ v).length
        (Nat.le_of_lt houter))

  have hsuf :
      y ++ z <:+
        centerMarkerProductWitness N :=
    ⟨u ++ v ++ x, by
      rw [hdecomp]
      simp [List.append_assoc]⟩
  have hpreRev :
      (y ++ z).reverse <+:
        (centerMarkerProductWitness N).reverse :=
    List.reverse_prefix.2 hsuf
  have hyzRev :
      (y ++ z).reverse =
        List.replicate (y ++ z).length LpmSymbol.b := by
    have h :=
      (List.prefix_iff_eq_take.1 hpreRev).trans
        (centerMarkerProductWitness_reverse_take N
          (y ++ z).reverse.length
          (by
            rw [List.length_reverse]
            exact Nat.le_of_lt hinner))
    simpa [List.length_append, Nat.add_comm] using h

  have hu_all :
      ∀ t ∈ u, t = LpmSymbol.a := by
    intro t ht
    exact
      List.eq_of_mem_replicate
        (huv ▸ List.mem_append_left v ht)
  have hv_all :
      ∀ t ∈ v, t = LpmSymbol.a := by
    intro t ht
    exact
      List.eq_of_mem_replicate
        (huv ▸ List.mem_append_right u ht)
  have hy_all :
      ∀ t ∈ y, t = LpmSymbol.b := by
    intro t ht
    have htRev :
        t ∈ (y ++ z).reverse :=
      List.mem_reverse.2
        (List.mem_append_left z ht)
    exact
      List.eq_of_mem_replicate
        (hyzRev ▸ htRev)
  have hz_all :
      ∀ t ∈ z, t = LpmSymbol.b := by
    intro t ht
    have htRev :
        t ∈ (y ++ z).reverse :=
      List.mem_reverse.2
        (List.mem_append_right y ht)
    exact
      List.eq_of_mem_replicate
        (hyzRev ▸ htRev)

  have hu :
      u = List.replicate u.length LpmSymbol.a :=
    (List.eq_replicate_length).2 hu_all
  have hv :
      v = List.replicate v.length LpmSymbol.a :=
    (List.eq_replicate_length).2 hv_all
  have hy :
      y = List.replicate y.length LpmSymbol.b :=
    (List.eq_replicate_length).2 hy_all
  have hz :
      z = List.replicate z.length LpmSymbol.b :=
    (List.eq_replicate_length).2 hz_all

  let ku := (u ++ v).length
  let kz := (y ++ z).length
  have hku : ku ≤ N := Nat.le_of_lt houter
  have hkz : kz ≤ N := Nat.le_of_lt hinner

  have hwshape :
      centerMarkerProductWitness N =
        List.replicate ku LpmSymbol.a ++
          ((List.replicate (N - ku) LpmSymbol.a ++
              [LpmSymbol.c] ++
                List.replicate N LpmSymbol.b ++
                  [LpmSymbol.d] ++
                    List.replicate N LpmSymbol.a ++
                      [LpmSymbol.c] ++
                        List.replicate (N - kz) LpmSymbol.b) ++
            List.replicate kz LpmSymbol.b) := by
    have hNku : ku + (N - ku) = N :=
      Nat.add_sub_of_le hku
    have hNkz : (N - kz) + kz = N :=
      Nat.sub_add_cancel hkz
    have haSplit :
        List.replicate N LpmSymbol.a =
          List.replicate ku LpmSymbol.a ++
            List.replicate (N - ku) LpmSymbol.a := by
      rw [← List.replicate_add, hNku]
    have hbSplit :
        List.replicate N LpmSymbol.b =
          List.replicate (N - kz) LpmSymbol.b ++
            List.replicate kz LpmSymbol.b := by
      rw [← List.replicate_add, hNkz]
    simp only [centerMarkerProductWitness, lpmCore,
      haSplit, hbSplit, List.append_assoc]

  have huv' :
      u ++ v = List.replicate ku LpmSymbol.a := by
    simpa [ku] using huv
  have hyz :
      y ++ z = List.replicate kz LpmSymbol.b := by
    rw [hy, hz]
    rw [← List.replicate_add]
    congr
    simp [kz]

  have hx :
      x =
        List.replicate (N - ku) LpmSymbol.a ++
          [LpmSymbol.c] ++
            List.replicate N LpmSymbol.b ++
              [LpmSymbol.d] ++
                List.replicate N LpmSymbol.a ++
                  [LpmSymbol.c] ++
                    List.replicate (N - kz) LpmSymbol.b := by
    have hEq :
        List.replicate ku LpmSymbol.a ++
            ((List.replicate (N - ku) LpmSymbol.a ++
                [LpmSymbol.c] ++
                  List.replicate N LpmSymbol.b ++
                    [LpmSymbol.d] ++
                      List.replicate N LpmSymbol.a ++
                        [LpmSymbol.c] ++
                          List.replicate (N - kz) LpmSymbol.b) ++
              List.replicate kz LpmSymbol.b)
          =
        List.replicate ku LpmSymbol.a ++
            (x ++ List.replicate kz LpmSymbol.b) := by
      calc
        _ = centerMarkerProductWitness N :=
          hwshape.symm
        _ = u ++ v ++ x ++ y ++ z :=
          hdecomp
        _ =
          List.replicate ku LpmSymbol.a ++
            (x ++ List.replicate kz LpmSymbol.b) := by
              rw [huv']
              simp only [List.append_assoc]
              rw [hyz]
    have hEq' :
        (List.replicate (N - ku) LpmSymbol.a ++
            [LpmSymbol.c] ++
              List.replicate N LpmSymbol.b ++
                [LpmSymbol.d] ++
                  List.replicate N LpmSymbol.a ++
                    [LpmSymbol.c] ++
                      List.replicate (N - kz) LpmSymbol.b) ++
          List.replicate kz LpmSymbol.b
        =
        x ++ List.replicate kz LpmSymbol.b :=
      List.append_cancel_left hEq
    exact List.append_cancel_right hEq'.symm

  rw [hu, hx, hz]
  have hkuEq :
      ku = u.length + v.length := by
    simp [ku]
  have hkzEq :
      kz = y.length + z.length := by
    simp [kz]
  have ha :
      u.length + (N - ku) =
        N - v.length := by
    rw [hkuEq]
    omega
  have hb :
      (N - kz) + z.length =
        N - y.length := by
    rw [hkzEq]
    omega
  simp only [List.append_assoc]
  rw [← List.replicate_add, ha]
  rw [← List.replicate_add, hb]

/--
A word already displayed in the six-block center-marker shape belongs to L_x
only if the two balance equations hold.
-/
theorem centerMarkerProduct_displayed_shape_forces_balance
    {p q r s : Nat}
    (hmem :
      List.replicate p LpmSymbol.a ++
          [LpmSymbol.c] ++
            List.replicate q LpmSymbol.b ++
              [LpmSymbol.d] ++
                List.replicate r LpmSymbol.a ++
                  [LpmSymbol.c] ++
                    List.replicate s LpmSymbol.b ∈
        CenterMarkerProductLanguage) :
    p = q ∧ r = s := by
  let left : Word LpmSymbol :=
    List.replicate p LpmSymbol.a ++
      [LpmSymbol.c] ++
        List.replicate q LpmSymbol.b
  let right : Word LpmSymbol :=
    List.replicate r LpmSymbol.a ++
      [LpmSymbol.c] ++
        List.replicate s LpmSymbol.b
  have hleftd : LpmSymbol.d ∉ left := by
    simp [left]
  have hrightd : LpmSymbol.d ∉ right := by
    simp [right]
  have hprod :
      left ++ [LpmSymbol.d] ++ right ∈
        CenterMarkerProductLanguage := by
    simpa [left, right, List.append_assoc] using hmem
  have hparts :=
    (centerMarkerProduct_split_iff hleftd hrightd).1 hprod
  constructor
  · have hleft :
        lpmOneCenter p LpmSymbol.c q ∈
          CenterMarkerLanguage := by
      simpa [left, lpmOneCenter, List.append_assoc] using hparts.1
    exact
      (centerMarker_oneCenter_mem_iff p q).1 hleft
  · have hright :
        lpmOneCenter r LpmSymbol.c s ∈
          CenterMarkerLanguage := by
      simpa [right, lpmOneCenter, List.append_assoc] using hparts.2
    exact
      (centerMarker_oneCenter_mem_iff r s).1 hright

/--
Fully internal nonlinearity result for the v88 witness.  No external
homomorphism-closure theorem is required.
-/
theorem centerMarkerProduct_not_rawLinearInitialRepresentable :
    ¬ RawLinearInitialRepresentable
      CenterMarkerProductLanguage := by
  intro hrep
  obtain ⟨p, hpump⟩ :=
    rawLinearInitialRepresentable_pumping hrep
  let N := p + 1
  let witness : Word LpmSymbol :=
    centerMarkerProductWitness N
  have hw :
      witness ∈ CenterMarkerProductLanguage := by
    exact centerMarkerProductWitness_mem N
  have hlong :
      p < witness.length := by
    simp [witness, centerMarkerProductWitness,
      lpmCore, N]
    omega
  obtain
    ⟨u, v, x, y, z,
      hdecomp, hpos, hbound, hpumped⟩ :=
    hpump witness hw hlong

  have hboundLen :
      u.length + v.length +
          y.length + z.length
        ≤ p := by
    simpa [List.length_append,
      Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hbound
  have huvShort :
      (u ++ v).length < N := by
    simp [List.length_append, N]
    omega
  have hyzShort :
      (y ++ z).length < N := by
    simp [List.length_append, N]
    omega

  have hdown :
      u ++ x ++ z ∈ CenterMarkerProductLanguage := by
    simpa [linearPumpLeft, linearPumpRight,
      List.append_assoc] using hpumped 0

  have hshape :
      u ++ x ++ z =
        List.replicate (N - v.length) LpmSymbol.a ++
          [LpmSymbol.c] ++
            List.replicate N LpmSymbol.b ++
              [LpmSymbol.d] ++
                List.replicate N LpmSymbol.a ++
                  [LpmSymbol.c] ++
                    List.replicate (N - y.length) LpmSymbol.b :=
    centerMarkerProduct_pumpDown_shape
      N
      (by simpa [witness] using hdecomp)
      huvShort hyzShort

  have hbalance :
      N - v.length = N /\
        N = N - y.length := by
    rw [hshape] at hdown
    exact
      centerMarkerProduct_displayed_shape_forces_balance hdown

  have hv0 : v.length = 0 := by
    omega
  have hy0 : y.length = 0 := by
    omega
  have hzero :
      (v ++ y).length = 0 := by
    simp [List.length_append, hv0, hy0]
  omega

end TCS1
end LeanCfgProject
