import Lift
import Dihedral.Blocks
import Std.Data.HashSet.Lemmas

namespace DihedralCert

/-- Compute the residue set once, then look up all requested residues. -/
private def covers (m : Nat) (D : List Int) : Bool :=
  let residues := Std.HashSet.ofList (D.map fun z => z % (m : Int))
  (List.range m).all fun i => residues.contains (i : Int)

private theorem covers_sound {m : Nat} {D : List Int} (h : covers m D) :
    ∀ x : Fin m, ∃ z ∈ D, z % (m : Int) = (x.val : Int) := by
  intro x
  have hx := List.all_eq_true.mp h x.val (List.mem_range.mpr x.isLt)
  simpa using hx

private def Block.last (lo : Nat) : Block → Nat
  | .direct _ _ => lo
  | .lift hi .. => hi

private def Block.valid (lo : Nat) : Block → Bool
  | .direct A B =>
      decide (11*(A.length+B.length)^2 ≤ 64*lo) &&
      covers lo (diff A B) && covers lo (diff A A ++ diff B B)
  | .lift hi m g r w U V S =>
      decide (0 < m) &&
      decide (∀ s ∈ S, 0 ≤ s ∧ s ≤ (m : Int)-1-g) &&
      covers m (diff S S) &&
      decide (∀ x : Fin (w+1), (x.val : Int) ∈ diff U V) &&
      decide (∀ x : Fin (2*r+1), (x.val : Int)-(r : Int) ∈ diff U U ++ diff V V) &&
      decide (w ≤ 2*r) && decide (hi ≤ w*m + 2*g + 1) &&
      decide (11*((U.length+V.length)*S.length)^2 ≤ 64*lo)

private theorem block_sound {b : Block} {lo n : Nat}
    (h : b.valid lo) (hl : lo ≤ n) (hr : n ≤ b.last lo) : Good n := by
  cases b with
  | direct A B =>
    change n ≤ lo at hr
    have he := Nat.le_antisymm hl hr
    subst n
    simp only [Block.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨A, B, h.1.1, covers_sound h.1.2, covers_sound h.2⟩
  | lift hi m g r w U V S =>
    change n ≤ hi at hr
    simp only [Block.valid, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hm, bounds⟩, cyclic⟩, cross⟩, mono⟩, width⟩, high⟩, budget⟩ := h
    exact liftGood hm bounds (covers_sound cyclic) cross mono width
      (Nat.le_trans hr high) (Nat.le_trans budget (Nat.mul_le_mul_left 64 hl))

/-- Each block starts at the first integer following the previous block.
    The final test records the exclusive end of the complete chain. -/
private def chain (stop lo : Nat) : List Block → Bool
  | [] => decide (stop ≤ lo)
  | b :: bs => b.valid lo && chain stop (b.last lo + 1) bs

private theorem chain_sound {stop lo n : Nat} {bs : List Block}
    (h : chain stop lo bs) (hl : lo ≤ n) (hr : n < stop) : Good n := by
  induction bs generalizing lo with
  | nil =>
    simp only [chain, decide_eq_true_eq] at h
    omega
  | cons b bs ih =>
    simp only [chain, Bool.and_eq_true] at h
    by_cases inside : n ≤ b.last lo
    · exact block_sound h.1 hl inside
    · exact ih h.2 (by omega)

private theorem verifiedChain : chain 1212464 1 certificateBlocks := by native_decide

/-- The finite part of the bound, including all cyclic witnesses. -/
theorem finiteGood {n : Nat} (hpos : 1 ≤ n) (hr : n < 1212464) : Good n :=
  chain_sound verifiedChain hpos hr

end DihedralCert
