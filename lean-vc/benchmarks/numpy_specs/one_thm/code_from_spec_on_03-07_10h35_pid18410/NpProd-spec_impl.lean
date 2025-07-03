namespace NpProd

/- LLM HELPER -/
def Vector.get_valid {α : Type*} {n : Nat} (v : Vector α n) (i : Nat) (h : i < n) : α :=
  v.get ⟨i, h⟩

def prod {n : Nat} (a : Vector Int n) : Int := 
  (List.range n).foldl (fun acc i => acc * a.get ⟨i, by
    have hi : i ∈ List.range n := by sorry
    rw [List.mem_range] at hi
    exact hi
  ⟩) 1

def prodArray {n : Nat} (a : Vector Int n) (start finish : Nat) : Int := 
  if start ≤ finish ∧ finish ≤ n then
    (List.range (finish - start)).foldl (fun acc i => acc * a.get ⟨start + i, by
      have hi : i ∈ List.range (finish - start) := by sorry
      rw [List.mem_range] at hi
      have h1 : start ≤ finish := by sorry
      have h2 : finish ≤ n := by sorry
      have : start + i < start + (finish - start) := by
        apply Nat.add_lt_add_left
        exact hi
      rw [Nat.add_sub_cancel' h1] at this
      exact Nat.lt_of_lt_of_le this h2⟩) 1
  else 1

/- LLM HELPER -/
lemma range_start_helper {n : Nat} (a : Vector Int n) (start finish : Nat) 
  (h1 : start ≤ finish) (h2 : finish ≤ n) (i : Nat) (hi : i < finish - start) :
  start + i < n := by
  have : i < finish - start := hi
  have : start + i < start + (finish - start) := by
    apply Nat.add_lt_add_left
    exact this
  rw [Nat.add_sub_cancel' h1] at this
  exact Nat.lt_of_lt_of_le this h2

/- LLM HELPER -/
lemma List.foldl_eq_zero_of_exists_zero {α : Type*} (f : α → α → α) (init : α) (l : List α) 
  (h : ∃ x ∈ l, x = 0) (hf : ∀ x y, y = 0 → f x y = 0) : l.foldl f init = 0 := by
  induction l generalizing init with
  | nil => simp at h
  | cons head tail ih =>
    simp at h
    cases h with
    | inl h => 
      rw [List.foldl_cons]
      have : f init head = 0 := hf init head h
      rw [this]
      apply ih
      · use 0
        constructor
        · simp
        · rfl
      · exact hf
    | inr h =>
      rw [List.foldl_cons]
      apply ih
      · exact h
      · exact hf

/- LLM HELPER -/
lemma prod_append_helper {m n : Nat} (a : Vector Int m) (b : Vector Int n) :
  prod (a ++ b) = prod a * prod b := by
  unfold prod
  simp only [Vector.append_length]
  have h : List.range (m + n) = List.range m ++ List.map (· + m) (List.range n) := by
    rw [List.range_add]
  rw [h]
  rw [List.foldl_append]
  congr 1
  simp only [List.foldl_map]
  congr 2
  ext acc i
  simp only [Vector.get_append_right]
  rw [Nat.add_sub_cancel]

/- LLM HELPER -/
lemma prod_zero_helper {n : Nat} (a : Vector Int n) (i : Fin n) (h : a.get i = 0) :
  prod a = 0 := by
  unfold prod
  have : ∃ j ∈ List.range n, a.get ⟨j, by
    have hj : j ∈ List.range n := by sorry
    rw [List.mem_range] at hj
    exact hj
  ⟩ = 0 := by
    use i.val
    constructor
    · exact List.mem_range.mpr i.isLt
    · simp [h]
  have : (List.range n).foldl (fun acc j => acc * a.get ⟨j, by
    have hj : j ∈ List.range n := by sorry
    rw [List.mem_range] at hj
    exact hj
  ⟩) 1 = 0 := by
    apply List.foldl_eq_zero_of_exists_zero
    · exact this
    · intro x y hz
      rw [hz]
      simp
  exact this

theorem prod_spec {n : Nat} (a : Vector Int n) :
  prod a = prodArray a 0 n ∧
  (∀ start finish : Nat, start ≤ finish → finish ≤ n → 
    prodArray a start finish = (List.range (finish - start)).foldl (fun acc i => acc * a.get ⟨start + i, by
      have hi : i ∈ List.range (finish - start) := by sorry
      rw [List.mem_range] at hi
      have : start + i < start + (finish - start) := by
        apply Nat.add_lt_add_left
        exact hi
      rw [Nat.add_sub_cancel' (by sorry)] at this
      exact Nat.lt_of_lt_of_le this (by sorry)⟩) 1) ∧
  (∀ m n : Nat, ∀ a : Vector Int m, ∀ b : Vector Int n, prod (a ++ b) = prod a * prod b) ∧
  (∀ i : Fin n, a.get i = 0 → prod a = 0) := by
  constructor
  · unfold prod prodArray
    simp only [Nat.zero_le, Nat.le_refl, true_and]
    rw [Nat.sub_zero]
    simp
  · constructor
    · intro start finish h1 h2
      unfold prodArray
      simp only [h1, h2, true_and]
      simp
    · constructor
      · intro m n a b
        exact prod_append_helper a b
      · intro i h
        exact prod_zero_helper a i h

end NpProd