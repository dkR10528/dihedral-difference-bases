import Lift

namespace DihedralCert

/-- The normal form (e,k) denotes the symmetry r^k s^e. -/
abbrev Element (n : Nat) := Bool × Fin n

def residue (n : Nat) (hn : 0 < n) (z : Int) : Fin n :=
  ⟨(z % (n : Int)).toNat, by
    have := Int.emod_nonneg z (show (n : Int) ≠ 0 by omega)
    have := Int.emod_lt_of_pos z (show (0 : Int) < n by omega)
    omega⟩

@[simp] theorem residue_val (z : Int) (hn : 0 < n) :
    ((residue n hn z).val : Int) = z % (n : Int) := by
  apply Int.toNat_of_nonneg
  exact Int.emod_nonneg _ (by omega)

private theorem residue_fin (k : Fin n) (hn : 0 < n) :
    residue n hn (k.val : Int) = k := by
  apply Fin.ext
  have hk := k.isLt
  simp [residue, Int.emod_eq_of_lt (show 0 ≤ (k.val : Int) by omega) (show (k.val : Int) < n by omega)]

/-- Multiplication of the affine normal forms, with s acting by inversion. -/
def mul (a b : Element n) : Element n :=
  (a.1 ^^ b.1, residue n (by have := a.2.isLt; omega)
    (if a.1 then (a.2.val : Int) - b.2.val else (a.2.val : Int) + b.2.val))

def inv (a : Element n) : Element n :=
  (a.1, if a.1 then a.2 else residue n (by have := a.2.isLt; omega) (-(a.2.val : Int)))

/-- The group difference x y⁻¹ in the coordinates (reflection flag, exponent). -/
def quotient (a b : Element n) : Element n :=
  (a.1 ^^ b.1, residue n (by have := a.2.isLt; omega)
    (if a.1 == b.1 then (a.2.val : Int) - b.2.val else (a.2.val : Int) + b.2.val))

def IsBasis (S : List (Element n)) : Prop :=
  ∀ g, ∃ a ∈ S, ∃ b ∈ S, quotient a b = g

private theorem res_equal {n : Nat} (hn : 0 < n) {x y : Int} (h : x % (n : Int) = y % n) :
    residue n hn x = residue n hn y := by
  exact Fin.ext (congrArg Int.toNat h)

theorem quotient_eq_mul_inv (a b : Element n) : quotient a b = mul a (inv b) := by
  rcases a with ⟨e,x⟩; rcases b with ⟨f,y⟩
  cases e <;> cases f <;> simp [quotient, mul, inv, residue_val, Prod.mk.injEq] <;>
    apply res_equal <;> simp [Int.sub_neg, ← Int.sub_eq_add_neg]

theorem mul_assoc (a b c : Element n) : mul (mul a b) c = mul a (mul b c) := by
  rcases a with ⟨e,x⟩; rcases b with ⟨f,y⟩; rcases c with ⟨g,z⟩
  cases e <;> cases f <;> cases g <;> simp [mul, residue_val] <;>
    apply res_equal <;> simp <;> congr 1 <;> omega

def identity (hn : 0 < n) : Element n := (false, ⟨0, hn⟩)

theorem identity_mul (hn : 0 < n) (a : Element n) : mul (identity hn) a = a := by
  rcases a with ⟨e,x⟩; cases e <;> simp [mul, identity, residue_fin]

theorem mul_identity (hn : 0 < n) (a : Element n) : mul a (identity hn) = a := by
  rcases a with ⟨e,x⟩; cases e <;> simp [mul, identity, residue_fin]

theorem mul_inv (hn : 0 < n) (a : Element n) : mul a (inv a) = identity hn := by
  rw [← quotient_eq_mul_inv]; rcases a with ⟨e,x⟩
  cases e <;> simp [quotient, identity, residue]

theorem inv_mul (hn : 0 < n) (a : Element n) : mul (inv a) a = identity hn := by
  rcases a with ⟨e,x⟩
  cases e <;> apply Prod.ext <;> first | rfl | skip
  all_goals apply Fin.ext <;> apply Int.ofNat_inj.mp <;>
    simp [mul, inv, identity, residue_val]
  rw [show -(x.val : Int) + x.val = 0 by omega, Int.zero_emod]







/-- The certificate's b encodes s r^b = r^(-b) s. -/
private def rot (hn : 0 < n) (a : Int) : Element n := (false, residue n hn a)
private def refl (hn : 0 < n) (b : Int) : Element n := (true, residue n hn (-b))

private theorem residue_eq_of_mod {hn : 0 < n} {k : Fin n} {z : Int}
    (hz : z % n = (k.val : Int)) : residue n hn z = k := by
  exact Fin.ext (by simp [residue, hz])

private theorem rot_rot (hn : 0 < n) (a b : Int) :
    quotient (rot hn a) (rot hn b) = rot hn (a-b) := by
  simp [quotient, rot, residue_val]; apply res_equal
  exact (Int.sub_emod ..).symm

private theorem refl_refl (hn : 0 < n) (a b : Int) :
    quotient (refl hn b) (refl hn a) = rot hn (a-b) := by
  simp [quotient, rot, refl, residue_val]; apply res_equal
  rw [← Int.sub_emod]; congr 1; omega

private theorem rot_refl (hn : 0 < n) (a b : Int) :
    quotient (rot hn a) (refl hn b) = (true, residue n hn (a-b)) := by
  simp [quotient, rot, refl, residue_val]; apply res_equal
  simp [Int.sub_eq_add_neg]

theorem good_to_basis {n : Nat} (hn : 0 < n) (h : Good n) :
    ∃ S : List (Element n), 11*S.length^2 ≤ 64*n ∧ IsBasis S := by
  obtain ⟨A, B, budget, cross, internal⟩ := h
  let S := A.map (rot hn) ++ B.map (refl hn)
  have ha {a} (h : a ∈ A) : rot hn a ∈ S :=
    List.mem_append_left _ (List.mem_map.mpr ⟨a, h, rfl⟩)
  have hb {b} (h : b ∈ B) : refl hn b ∈ S :=
    List.mem_append_right _ (List.mem_map.mpr ⟨b, h, rfl⟩)
  refine ⟨S, by simpa [S] using budget, ?_⟩
  rintro ⟨e,k⟩
  cases e with
  | false =>
    obtain ⟨z,hz,eq⟩ := internal k
    simp only [List.mem_append, diff, List.mem_flatMap, List.mem_map] at hz
    rcases hz with ⟨a,h₁,b,h₂,rfl⟩ | ⟨a,h₁,b,h₂,rfl⟩
    · exact ⟨_, ha h₁, _, ha h₂, (rot_rot ..).trans (Prod.ext rfl (residue_eq_of_mod (hn := hn) eq))⟩
    · exact ⟨_, hb h₂, _, hb h₁, (refl_refl ..).trans (Prod.ext rfl (residue_eq_of_mod (hn := hn) eq))⟩
  | true =>
    obtain ⟨z,hz,eq⟩ := cross k
    simp only [diff, List.mem_flatMap, List.mem_map] at hz
    obtain ⟨a,h₁,b,h₂,rfl⟩ := hz
    exact ⟨_, ha h₁, _, hb h₂, (rot_refl ..).trans (Prod.ext rfl (residue_eq_of_mod (hn := hn) eq))⟩




/-- All 2n normal forms, in rotation-then-reflection order. -/
def elements (n : Nat) : List (Element n) :=
  (List.finRange n).map (false, ·) ++ (List.finRange n).map (true, ·)

@[simp] theorem elements_length (n : Nat) : (elements n).length = 2*n := by
  simp [elements, Nat.two_mul]

@[simp] theorem mem_elements (a : Element n) : a ∈ elements n := by
  rcases a with ⟨e,k⟩
  cases e <;> simp [elements]

theorem elements_nodup (n : Nat) : (elements n).Nodup := by
  apply List.nodup_append.mpr
  have h (e : Bool) : ((List.finRange n).map (e, ·)).Nodup :=
    (List.nodup_finRange n).map _ (by intro a b h hab; exact h (congrArg Prod.snd hab))
  exact ⟨h false, h true, by simp⟩

/-- Removing repetitions turns the list bound into a bound on the number of
distinct group elements in a difference basis. -/
theorem good_to_nodup_basis {n : Nat} (hn : 0 < n) (h : Good n) :
    ∃ S : List (Element n), S.Nodup ∧ 11*S.length^2 ≤ 64*n ∧ IsBasis S := by
  obtain ⟨T, budget, covers⟩ := good_to_basis hn h
  let S := (elements n).filter (· ∈ T)
  have hmem (a : Element n) : a ∈ S ↔ a ∈ T := by simp [S]
  have hn' : S.Nodup := (elements_nodup n).filter _
  have hlen := hn'.length_le_of_subset (l₂ := T) (by intro a ha; exact (hmem a).mp ha)
  refine ⟨S, hn', Nat.le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlen _)) budget, ?_⟩
  intro g
  obtain ⟨a,ha,b,hb,e⟩ := covers g
  exact ⟨a,(hmem _).mpr ha,b,(hmem _).mpr hb,e⟩

end DihedralCert

