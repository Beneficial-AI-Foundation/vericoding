/-
# NumPy Min Specification

Port of np_min.dfy to Lean 4
-/

namespace DafnySpecs.NpMin

/- LLM HELPER -/
def min_of_two (a b : Int) : Int := if a ≤ b then a else b

/- LLM HELPER -/
lemma min_of_two_le_left (a b : Int) : min_of_two a b ≤ a := by
  simp [min_of_two]
  by_cases h : a ≤ b
  · simp [h]
  · simp [h]

/- LLM HELPER -/
lemma min_of_two_le_right (a b : Int) : min_of_two a b ≤ b := by
  simp [min_of_two]
  by_cases h : a ≤ b
  · simp [h]; exact h
  · simp [h]

/- LLM HELPER -/
lemma min_of_two_eq_left_or_right (a b : Int) : min_of_two a b = a ∨ min_of_two a b = b := by
  simp [min_of_two]
  by_cases h : a ≤ b
  · simp [h]; left; rfl
  · simp [h]; right; rfl

/-- Find the minimum element in a non-empty vector -/
def min {n : Nat} (h : n > 0) (a : Vector Int n) : Int := 
  List.foldl min_of_two (a.get ⟨0, h⟩) a.toList

/- LLM HELPER -/
lemma vector_foldl_min_le {n : Nat} (h : n > 0) (a : Vector Int n) (i : Fin n) :
  List.foldl min_of_two (a.get ⟨0, h⟩) a.toList ≤ a.get i := by
  have h_mem : a.get i ∈ a.toList := by
    simp [Vector.mem_toList]
    use i
  induction' a.toList generalizing i with x xs ih
  · simp at h_mem
  · simp [List.foldl]
    cases' xs with y ys
    · simp [List.foldl]
      have : [x] = a.toList := by simp at h_mem; exact h_mem.symm
      have : a.toList.length = 1 := by simp [this]
      have : n = 1 := by simp [Vector.length_toList] at this; exact this
      have : i = ⟨0, h⟩ := by
        apply Fin.ext
        simp [Fin.val_eq_zero]
        have : i.val < 1 := by rw [←this]; exact i.is_lt
        exact Nat.eq_zero_of_lt_one this
      rw [this]
      simp
    · have h_in_tail : a.get i = x ∨ a.get i ∈ (y :: ys) := by
        cases' h_mem with h_eq h_in
        · left; exact h_eq
        · right; exact h_in
      cases' h_in_tail with h_x h_tail
      · rw [h_x]
        exact min_of_two_le_left x (List.foldl min_of_two y ys)
      · have : min_of_two x (List.foldl min_of_two y ys) ≤ List.foldl min_of_two y ys :=
          min_of_two_le_right x (List.foldl min_of_two y ys)
        apply le_trans this
        have : List.foldl min_of_two y ys ≤ a.get i := by
          induction' ys generalizing y with z zs ih_inner
          · simp [List.foldl]
            cases' h_tail with h_y h_empty
            · exact h_y ▸ le_refl y
            · exact False.elim h_empty
          · simp [List.foldl]
            cases' h_tail with h_y h_rest
            · rw [h_y]
              exact min_of_two_le_left y (List.foldl min_of_two z zs)
            · have : min_of_two y (List.foldl min_of_two z zs) ≤ List.foldl min_of_two z zs :=
                min_of_two_le_right y (List.foldl min_of_two z zs)
              apply le_trans this
              exact ih_inner h_rest
        exact this

/- LLM HELPER -/
lemma vector_foldl_min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, List.foldl min_of_two (a.get ⟨0, h⟩) a.toList = a.get i := by
  induction' a.toList with x xs ih
  · simp at h
    have : n = 0 := by simp [Vector.length_toList] at h; exact h
    rw [this] at h
    exact False.elim (Nat.not_lt_zero 0 h)
  · cases' xs with y ys
    · use ⟨0, h⟩
      simp [List.foldl]
    · simp [List.foldl]
      by_cases h_case : x ≤ List.foldl min_of_two y ys
      · use ⟨0, h⟩
        simp [min_of_two, h_case]
        have : x = a.get ⟨0, h⟩ := by
          simp [Vector.get_zero]
          have : a.toList.head? = some x := by simp
          have : a.toList.length > 0 := by simp [Vector.length_toList]; exact h
          simp [Vector.get_zero_eq_head] at this
          exact this.symm
        exact this
      · have h_min_eq : min_of_two x (List.foldl min_of_two y ys) = List.foldl min_of_two y ys := by
          simp [min_of_two, h_case]
        rw [h_min_eq]
        have : ∃ j, List.foldl min_of_two y ys = a.get j := by
          have y_in : y ∈ a.toList := by simp
          have : ∃ j, y = a.get j := by
            simp [Vector.mem_toList] at y_in
            exact y_in
          obtain ⟨j, hj⟩ := this
          use j
          induction' ys with z zs ih_inner
          · simp [List.foldl]
            exact hj
          · simp [List.foldl]
            by_cases h_inner : y ≤ List.foldl min_of_two z zs
            · simp [min_of_two, h_inner]
              exact hj
            · simp [min_of_two, h_inner]
              have z_in : z ∈ a.toList := by simp
              have : ∃ k, z = a.get k := by
                simp [Vector.mem_toList] at z_in
                exact z_in
              obtain ⟨k, hk⟩ := this
              use k
              exact hk.symm
        exact this

/-- Specification: The minimum exists in the vector -/
theorem min_exists {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∃ i : Fin n, min h a = a.get i :=
  vector_foldl_min_exists h a

/-- Specification: The minimum is less than or equal to all elements -/
theorem min_spec {n : Nat} (h : n > 0) (a : Vector Int n) :
  ∀ i : Fin n, min h a ≤ a.get i := fun i =>
  vector_foldl_min_le h a i

end DafnySpecs.NpMin