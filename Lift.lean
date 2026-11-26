import Std

namespace DihedralCert

def diff (A B : List Int) := A.flatMap fun a => B.map fun b => a-b

/-- A pair of exponent lists meeting the squared size bound and covering both
    reflection and rotation exponents. Repetitions are allowed in the lists. -/
def Good (n : Nat) : Prop := ∃ A B : List Int,
  11*(A.length+B.length)^2 ≤ 64*n ∧
  (∀ x : Fin n, ∃ z ∈ diff A B, z % (n:Int) = (x.val:Int)) ∧
  (∀ x : Fin n, ∃ z ∈ diff A A ++ diff B B, z % (n:Int) = (x.val:Int))

private def sums (m : Int) (U S : List Int) :=
  U.flatMap fun u => S.map fun s => m*u+s

private theorem length_sums (m : Int) (U S : List Int) :
    (sums m U S).length = U.length * S.length := by
  induction U with
  | nil => simp [sums]
  | cons u U ih => simpa [sums, Nat.succ_mul, Nat.add_comm] using ih

private theorem combine {m h z : Int} {U V S : List Int}
    (hh : h ∈ diff U V) (hz : z ∈ diff S S) :
    m*h+z ∈ diff (sums m U S) (sums m V S) := by
  simp only [diff, List.mem_flatMap, List.mem_map] at hh hz ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ := hh
  obtain ⟨s, hs, t, ht, rfl⟩ := hz
  refine ⟨m*u+s, ?_, m*v+t, ?_, ?_⟩
  · exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨s, hs, rfl⟩⟩
  · exact List.mem_flatMap.mpr ⟨v, hv, List.mem_map.mpr ⟨t, ht, rfl⟩⟩
  · rw [Int.mul_sub]; omega

/-- The short representatives of each residue force the quotient into the
    indicated template interval. -/
private theorem decompose {m g : Nat} {S : List Int} (hm : 0 < m)
    (bounds : ∀ s ∈ S, 0 ≤ s ∧ s ≤ (m : Int)-1-g)
    (cyclic : ∀ x : Fin m, ∃ z ∈ diff S S, z % (m : Int) = (x.val : Int))
    {i j t : Int} (lo : m*i-g ≤ t) (hi : t ≤ m*j+g) :
    ∃ h z : Int, i ≤ h ∧ h ≤ j ∧ z ∈ diff S S ∧ (m:Int)*h+z = t := by
  have hp : (0:Int) < m := by omega
  have hn := Int.emod_nonneg t (Int.ne_of_gt hp)
  have hl := Int.emod_lt_of_pos t hp
  obtain ⟨z, hz, he⟩ := cyclic ⟨(t % m).toNat, by omega⟩
  have he' : t % m = z % m := by simp only at he; omega
  obtain ⟨a, ha, b, hb, hab⟩ := (show ∃ a ∈ S, ∃ b ∈ S, a-b=z from by
    simpa only [diff, List.mem_flatMap, List.mem_map] using hz)
  have := bounds a ha
  have := bounds b hb
  let h := (t-z)/(m:Int)
  have eq : (m:Int)*h=t-z :=
    Int.mul_ediv_cancel_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp he')
  refine ⟨h, z, ?_, ?_, hz, by omega⟩
  · apply Int.le_of_not_gt
    intro bad
    have p := Int.mul_le_mul_of_nonneg_left (show h ≤ i-1 by omega) (Int.le_of_lt hp)
    rw [Int.mul_sub, Int.mul_one] at p
    omega
  · apply Int.le_of_not_gt
    intro bad
    have p := Int.mul_le_mul_of_nonneg_left (show j+1 ≤ h by omega) (Int.le_of_lt hp)
    rw [Int.mul_add, Int.mul_one] at p
    omega

private theorem coverInterval {n : Nat} {lo hi : Int} {D : List Int}
    (size : (n:Int) ≤ hi-lo+1) (cover : ∀ t, lo ≤ t → t ≤ hi → t ∈ D)
    (x : Fin n) : ∃ z ∈ D, z % (n:Int) = (x.val:Int) := by
  have hp : (0:Int) < n := by have := x.isLt; omega
  have lower := Int.emod_nonneg ((x.val:Int)-lo) (Int.ne_of_gt hp)
  have upper := Int.emod_lt_of_pos ((x.val:Int)-lo) hp
  refine ⟨lo + ((x.val:Int)-lo) % n, cover _ (by omega) (by omega), ?_⟩
  rw [Int.add_emod_emod, show lo+((x.val:Int)-lo)=(x.val:Int) by omega]
  exact Int.emod_eq_of_lt (by omega) (by have := x.isLt; omega)

theorem liftGood {n m g r w : Nat} {U V S : List Int} (hm : 0 < m)
    (bounds : ∀ s ∈ S, 0 ≤ s ∧ s ≤ (m : Int)-1-g)
    (cyclic : ∀ x : Fin m, ∃ z ∈ diff S S, z % (m : Int) = (x.val : Int))
    (cross : ∀ x : Fin (w+1), (x.val : Int) ∈ diff U V)
    (mono : ∀ x : Fin (2*r+1), (x.val : Int)-(r : Int) ∈ diff U U ++ diff V V)
    (width : w ≤ 2*r) (hi : n ≤ w*m + 2*g + 1)
    (budget : 11*((U.length+V.length)*S.length)^2 ≤ 64*n) : Good n := by
  refine ⟨sums m U S, sums m V S, ?_, ?_, ?_⟩
  · simpa [length_sums, Nat.add_mul] using budget
  · apply coverInterval (lo := -(g:Int)) (hi := (m:Int)*w+g)
    · rw [Int.mul_comm]
      omega
    · intro t hlo hhi
      obtain ⟨h,z,l,u,hz,rfl⟩ := decompose hm bounds cyclic (i := 0)
        (by simpa using hlo) hhi
      apply combine _ hz
      simpa [Int.toNat_of_nonneg l] using cross ⟨h.toNat, by omega⟩
  · apply coverInterval (lo := (m:Int)*(-(r:Int))-g) (hi := (m:Int)*r+g)
    · have hw := Nat.mul_le_mul_right m width
      rw [Nat.mul_assoc] at hw
      rw [Int.mul_neg, Int.mul_comm]
      omega
    · intro t hlo hhi
      obtain ⟨h,z,l,u,hz,rfl⟩ := decompose hm bounds cyclic hlo hhi
      have mem := mono ⟨(h+r).toNat, by omega⟩
      have e : ((h+r).toNat:Int)-(r:Int) = h := by omega
      change ((h+r).toNat:Int)-(r:Int) ∈ _ at mem
      rw [e, List.mem_append] at mem
      exact List.mem_append.mpr (mem.imp (fun p => combine p hz) (fun p => combine p hz))

end DihedralCert
