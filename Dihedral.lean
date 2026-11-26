import Finite
import Sharp

namespace DihedralCert

/-- The integer form of the normalized upper bound for a group of order 2n. -/
def UpperBound (n : Nat) : Prop :=
  ∃ S : List (Element n), S.Nodup ∧ 11 * S.length^2 ≤ 64*n ∧ IsBasis S

/-- All cases left open by Proposition 11, proved from explicit finite data. -/
theorem finite_bound {n : Nat} (positive : 0 < n) (small : n < 1212464) :
    UpperBound n := good_to_nodup_basis positive (finiteGood positive small)

/-- Eight is the exact minimum number of elements in a basis of D₂₂. -/
theorem exact_eight :
    (∃ S : List (Element 11), S.Nodup ∧ S.length = 8 ∧ IsBasis S) ∧
    (∀ S : List (Element 11), IsBasis S → 8 ≤ S.length) := by
  obtain ⟨s, distinct, bound, basis⟩ := finite_bound (n := 11) (by decide) (by decide)
  have lower := sharp_lower basis
  have upper : s.length ≤ 8 := by
    apply Classical.byContradiction
    intro h
    have sq := Nat.pow_le_pow_left (show 9 ≤ s.length by omega) 2
    omega
  exact ⟨⟨s, distinct, by omega, basis⟩, fun _ h => sharp_lower h⟩

/-- Banakh and Gavrylkiv (2019), Proposition 11, in squared integer form.
    This is an explicit hypothesis of the global result. -/
def PublishedTail : Prop := ∀ n : Nat, 1212464 ≤ n → UpperBound n

/-- The maximum is attained at n = 11, conditional on the published tail.
    Positivity makes the squared inequality equivalent to the real-valued bound. -/
theorem sharp_bound (tail : PublishedTail) :
    (∀ n : Nat, 0 < n → UpperBound n) ∧
    (∃ S : List (Element 11), S.Nodup ∧ S.length = 8 ∧ IsBasis S) ∧
    (∀ S : List (Element 11), IsBasis S → 8 ≤ S.length) := by
  refine ⟨?_, exact_eight⟩
  intro n positive
  by_cases small : n < 1212464
  · exact finite_bound positive small
  · exact tail n (by omega)

#print axioms finite_bound
#print axioms exact_eight
#print axioms sharp_bound

end DihedralCert
