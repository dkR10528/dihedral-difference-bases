import GroupModel

namespace DihedralCert

/-- Subsequences of a fixed universe with a length cap. -/
private def choices {α : Type} : List α → Nat → List (List α)
  | [], _ => [[]]
  | _ :: _, 0 => [[]]
  | x :: tail, k+1 => choices tail (k+1) ++ (choices tail k).map (x :: ·)

private theorem filter_mem_choices {α : Type} (p : α → Bool) (u : List α)
    (k : Nat) (h : (u.filter p).length ≤ k) : u.filter p ∈ choices u k := by
  induction u generalizing k with
  | nil => simp [choices]
  | cons x xs ih =>
    cases k with
    | zero =>
      have e : (x :: xs).filter p = [] := List.length_eq_zero_iff.mp (by omega)
      simp [e, choices]
    | succ k =>
      by_cases hx : p x = true
      · simp [hx] at h ⊢
        exact List.mem_append_right _ (List.mem_map.mpr ⟨_, ih k (by omega), rfl⟩)
      · simp [hx] at h ⊢
        exact List.mem_append_left _ (ih (k+1) h)

private def universe11 : List (Element 11) :=
  [false, true].flatMap fun tag => (List.finRange 11).map fun i => (tag,i)

private theorem universe11_complete : ∀ x : Element 11, x ∈ universe11 := by
  rintro ⟨tag,i⟩
  cases tag <;> simp [universe11]
private theorem universe11_nodup : universe11.Nodup := by decide

private def covers11 (s : List (Element 11)) : Bool :=
  universe11.all fun g => s.any fun a => s.any fun b => quotient a b == g

private theorem exhaustive11 : (choices universe11 7).all (fun s => !covers11 s) = true := by
  native_decide

/-- Every list giving a difference basis of the order-22 group has at least eight entries. -/
theorem sharp_lower {s : List (Element 11)} (hs : IsBasis s) : 8 ≤ s.length := by
  apply Classical.byContradiction
  intro h
  let t := universe11.filter (fun x => decide (x ∈ s))
  have ht : ∀ x, x ∈ t ↔ x ∈ s := by
    intro x
    simp [t, universe11_complete]
  have nd : t.Nodup := List.filter_sublist.nodup universe11_nodup
  have len : t.length ≤ s.length := nd.length_le_of_subset (fun x hx => (ht x).mp hx)
  have member : t ∈ choices universe11 7 := filter_mem_choices _ _ _ (by change t.length ≤ 7; omega)
  have impossible := List.all_eq_true.mp exhaustive11 t member
  have cov : covers11 t = true := by
    apply List.all_eq_true.mpr
    intro g _
    obtain ⟨a, ha, b, hb, eq⟩ := hs g
    exact List.any_eq_true.mpr ⟨a, (ht a).mpr ha, List.any_eq_true.mpr ⟨b, (ht b).mpr hb, by simpa using eq⟩⟩
  simp [cov] at impossible

end DihedralCert
