import LeanCfgProject.TCS1.RawLinearPumping
import LeanCfgProject.TCS1.DeltaStarNonlinearityBridge

/-!
# TCS #1 v79: internal proof that Double-Delta is not linear

This file discharges the final cited non-linearity input internally from the
bounded linear pumping theorem already proved in RawLinearPumping.
-/

namespace LeanCfgProject
namespace TCS1
namespace DeltaStar

open Symbol

universe u w

theorem doubleDeltaWitness_take
    (N m : Nat)
    (hm : m ≤ N) :
    (balancedBlock N ++ balancedBlock N).take m =
      List.replicate m a := by
  have hshape :
      balancedBlock N ++ balancedBlock N =
        List.replicate N a ++
          (List.replicate N b ++
            List.replicate N a ++
              List.replicate N b) := by
    simp [balancedBlock, List.append_assoc]
  rw [hshape]
  rw [List.take_append_of_le_length]
  · rw [List.take_replicate]
    congr
    omega
  · simpa using hm

theorem doubleDeltaWitness_reverse_take
    (N m : Nat)
    (hm : m ≤ N) :
    (balancedBlock N ++ balancedBlock N).reverse.take m =
      List.replicate m b := by
  have hshape :
      (balancedBlock N ++ balancedBlock N).reverse =
        List.replicate N b ++
          (List.replicate N a ++
            List.replicate N b ++
              List.replicate N a) := by
    simp [balancedBlock, List.reverse_append,
      List.append_assoc]
  rw [hshape]
  rw [List.take_append_of_le_length]
  · rw [List.take_replicate]
    congr
    omega
  · simpa using hm

theorem doubleDelta_pumpDown_shape
    (N : Nat)
    {u v x y z : Word Symbol}
    (hdecomp :
      balancedBlock N ++ balancedBlock N =
        u ++ v ++ x ++ y ++ z)
    (houter :
      (u ++ v).length < N)
    (hinner :
      (y ++ z).length < N) :
    u ++ x ++ z =
      List.replicate (N - v.length) a ++
        List.replicate N b ++
          List.replicate N a ++
            List.replicate (N - y.length) b := by
  have hpre :
      u ++ v <+:
        (balancedBlock N ++ balancedBlock N) :=
    ⟨x ++ y ++ z, by
      rw [hdecomp]
      simp [List.append_assoc]⟩
  have huv :
      u ++ v =
        List.replicate (u ++ v).length a :=
    (List.prefix_iff_eq_take.1 hpre).trans
      (doubleDeltaWitness_take N
        (u ++ v).length
        (Nat.le_of_lt houter))

  have hsuf :
      y ++ z <:+
        (balancedBlock N ++ balancedBlock N) :=
    ⟨u ++ v ++ x, by
      rw [hdecomp]
      simp [List.append_assoc]⟩
  have hpreRev :
      (y ++ z).reverse <+:
        (balancedBlock N ++ balancedBlock N).reverse :=
    List.reverse_prefix.2 hsuf
  have hyzRev :
      (y ++ z).reverse =
        List.replicate (y ++ z).length b := by
    have h :=
      (List.prefix_iff_eq_take.1 hpreRev).trans
        (doubleDeltaWitness_reverse_take N
          (y ++ z).reverse.length
          (by
            rw [List.length_reverse]
            exact Nat.le_of_lt hinner))
    simpa [List.length_append, Nat.add_comm] using h

  have hu_all :
      ∀ c ∈ u, c = a := by
    intro c hc
    exact
      List.eq_of_mem_replicate
        (huv ▸ List.mem_append_left v hc)
  have hv_all :
      ∀ c ∈ v, c = a := by
    intro c hc
    exact
      List.eq_of_mem_replicate
        (huv ▸ List.mem_append_right u hc)
  have hy_all :
      ∀ c ∈ y, c = b := by
    intro c hc
    have hcRev :
        c ∈ (y ++ z).reverse :=
      List.mem_reverse.2
        (List.mem_append_left z hc)
    exact
      List.eq_of_mem_replicate
        (hyzRev ▸ hcRev)
  have hz_all :
      ∀ c ∈ z, c = b := by
    intro c hc
    have hcRev :
        c ∈ (y ++ z).reverse :=
      List.mem_reverse.2
        (List.mem_append_right y hc)
    exact
      List.eq_of_mem_replicate
        (hyzRev ▸ hcRev)

  have hu :
      u = List.replicate u.length a :=
    (List.eq_replicate_length).2 hu_all
  have hv :
      v = List.replicate v.length a :=
    (List.eq_replicate_length).2 hv_all
  have hy :
      y = List.replicate y.length b :=
    (List.eq_replicate_length).2 hy_all
  have hz :
      z = List.replicate z.length b :=
    (List.eq_replicate_length).2 hz_all

  let ku := (u ++ v).length
  let kz := (y ++ z).length
  have hku : ku ≤ N := Nat.le_of_lt houter
  have hkz : kz ≤ N := Nat.le_of_lt hinner

  have hwshape :
      balancedBlock N ++ balancedBlock N =
        List.replicate ku a ++
          ((List.replicate (N - ku) a ++
              List.replicate N b ++
                List.replicate N a ++
                  List.replicate (N - kz) b) ++
            List.replicate kz b) := by
    have hNku : ku + (N - ku) = N :=
      Nat.add_sub_of_le hku
    have hNkz : (N - kz) + kz = N :=
      Nat.sub_add_cancel hkz
    have haSplit :
        List.replicate N a =
          List.replicate ku a ++
            List.replicate (N - ku) a := by
      rw [← List.replicate_add, hNku]
    have hbSplit :
        List.replicate N b =
          List.replicate (N - kz) b ++
            List.replicate kz b := by
      rw [← List.replicate_add, hNkz]
    simp only [balancedBlock, haSplit, hbSplit,
      List.append_assoc]

  have huv' :
      u ++ v = List.replicate ku a := by
    simpa [ku] using huv
  have hyz :
      y ++ z = List.replicate kz b := by
    rw [hy, hz]
    rw [← List.replicate_add]
    congr
    simp [kz]

  have hx :
      x =
        List.replicate (N - ku) a ++
          List.replicate N b ++
            List.replicate N a ++
              List.replicate (N - kz) b := by
    have hEq :
        List.replicate ku a ++
            ((List.replicate (N - ku) a ++
                List.replicate N b ++
                  List.replicate N a ++
                    List.replicate (N - kz) b) ++
              List.replicate kz b)
          =
        List.replicate ku a ++
            (x ++ List.replicate kz b) := by
      calc
        _ = balancedBlock N ++ balancedBlock N :=
          hwshape.symm
        _ = u ++ v ++ x ++ y ++ z :=
          hdecomp
        _ =
          List.replicate ku a ++
            (x ++ List.replicate kz b) := by
              rw [huv']
              simp only [List.append_assoc]
              rw [hyz]
    have hEq' :
        (List.replicate (N - ku) a ++
            List.replicate N b ++
              List.replicate N a ++
                List.replicate (N - kz) b) ++
          List.replicate kz b
        =
        x ++ List.replicate kz b :=
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
  calc
    List.replicate u.length a ++
        (List.replicate (N - ku) a ++
          List.replicate N b ++
            List.replicate N a ++
              List.replicate (N - kz) b) ++
      List.replicate z.length b
      =
    (List.replicate u.length a ++
        List.replicate (N - ku) a) ++
      (List.replicate N b ++
        List.replicate N a ++
          List.replicate (N - kz) b) ++
      List.replicate z.length b := by
        simp only [List.append_assoc]
    _ =
    List.replicate (u.length + (N - ku)) a ++
      (List.replicate N b ++
        List.replicate N a ++
          List.replicate (N - kz) b) ++
      List.replicate z.length b := by
        have haRep :=
          List.replicate_add
            u.length (N - ku) a
        rw [haRep]
    _ =
    List.replicate (N - v.length) a ++
      (List.replicate N b ++
        List.replicate N a ++
          List.replicate (N - kz) b) ++
      List.replicate z.length b := by
        rw [ha]
    _ =
    List.replicate (N - v.length) a ++
      List.replicate N b ++
        List.replicate N a ++
          (List.replicate (N - kz) b ++
            List.replicate z.length b) := by
        simp [List.append_assoc]
    _ =
    List.replicate (N - v.length) a ++
      List.replicate N b ++
        List.replicate N a ++
          List.replicate ((N - kz) + z.length) b := by
        have hbRep :=
          List.replicate_add
            (N - kz) z.length b
        rw [hbRep]
    _ =
    List.replicate (N - v.length) a ++
      List.replicate N b ++
        List.replicate N a ++
          List.replicate (N - y.length) b := by
        rw [hb]

theorem doubleDelta_not_rawLinearInitialRepresentable :
    ¬ RawLinearInitialRepresentable.{u, 0, w}
        DoubleDeltaLanguage := by
  intro hrep
  obtain ⟨p, hpump⟩ :=
    rawLinearInitialRepresentable_pumping hrep
  let N := p + 1
  let witness : Word Symbol :=
    balancedBlock N ++ balancedBlock N
  have hw :
      witness ∈ DoubleDeltaLanguage := by
    exact ⟨N, N, rfl⟩
  have hlong :
      p < witness.length := by
    simp [witness, balancedBlock, N]
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
      u ++ x ++ z ∈ DoubleDeltaLanguage := by
    simpa [linearPumpLeft, linearPumpRight,
      List.append_assoc] using hpumped 0

  have hshape :
      u ++ x ++ z =
        List.replicate (N - v.length) a ++
          List.replicate N b ++
            List.replicate N a ++
              List.replicate (N - y.length) b :=
    doubleDelta_pumpDown_shape
      N
      (by simpa [witness] using hdecomp)
      huvShort hyzShort

  have hlang :
      u ++ x ++ z ∈ Language :=
    (doubleDelta_subset_intersection hdown).1

  have hfirst :
      N - v.length = N := by
    rw [hshape] at hlang
    exact
      fourBlock_central_boundary_forces_balance
        (p := N - v.length)
        (q := N)
        (r := N)
        (s := N - y.length)
        (by simp [N])
        (by simp [N])
        hlang
  have hv0 : v.length = 0 := by
    omega

  have hbal :=
    balance_mem_zero hlang
  rw [hshape] at hbal
  simp only [balance_append,
    balance_replicate_a,
    balance_replicate_b] at hbal
  have hy0 : y.length = 0 := by
    omega

  have hzero :
      (v ++ y).length = 0 := by
    simp [List.length_append, hv0, hy0]
  omega

end DeltaStar
end TCS1
end LeanCfgProject
