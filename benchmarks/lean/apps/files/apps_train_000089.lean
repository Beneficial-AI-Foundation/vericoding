-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rearrange_array (n : Nat) (arr : List Int) (can : List Bool) : List Int := sorry

theorem rearrange_array_length
  (n : Nat) (arr : List Int) (can : List Bool) :
  arr.length = n → can.length = n →
  (rearrange_array n arr can).length = n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rearrange_array_fixed_elements
  (n : Nat) (arr : List Int) (can : List Bool) (i : Nat) (h1 : arr.length = n) 
  (h2 : can.length = n) (h3 : i < n) :
  let idx : Fin n := ⟨i, h3⟩
  let can_idx : Fin can.length := ⟨i, by rw [h2]; exact h3⟩
  let arr_idx : Fin arr.length := ⟨i, by rw [h1]; exact h3⟩
  let res_idx : Fin (rearrange_array n arr can).length := ⟨i, by rw [rearrange_array_length n arr can h1 h2]; exact h3⟩
  can.get can_idx = true →
  (rearrange_array n arr can).get res_idx = arr.get arr_idx := sorry

theorem rearrange_array_same_multiset
  (n : Nat) (arr : List Int) (can : List Bool) :
  arr.length = n → can.length = n → 
  ∃ perm : List Int, List.Perm perm (rearrange_array n arr can) := sorry

theorem rearrange_array_descending
  (n : Nat) (arr : List Int) (can : List Bool) (i j : Nat) 
  (h1 : arr.length = n) (h2 : can.length = n) 
  (h3 : i < n) (h4 : j < n) (h5 : i < j) :
  let can_i : Fin can.length := ⟨i, by rw [h2]; exact h3⟩
  let can_j : Fin can.length := ⟨j, by rw [h2]; exact h4⟩  
  let res_i : Fin (rearrange_array n arr can).length := ⟨i, by rw [rearrange_array_length n arr can h1 h2]; exact h3⟩
  let res_j : Fin (rearrange_array n arr can).length := ⟨j, by rw [rearrange_array_length n arr can h1 h2]; exact h4⟩
  can.get can_i = false → can.get can_j = false →
  (rearrange_array n arr can).get res_i ≥ (rearrange_array n arr can).get res_j := sorry

/-
info: [3, 2, 1]
-/
-- #guard_msgs in
-- #eval rearrange_array 3 [1, 3, 2] [0, 0, 0]

/-
info: [2, -3, 4, -1]
-/
-- #guard_msgs in
-- #eval rearrange_array 4 [2, -3, 4, -1] [1, 1, 1, 1]

/-
info: [-8, 4, 1, -2, 4, 7, -6]
-/
-- #guard_msgs in
-- #eval rearrange_array 7 [-8, 4, -2, -6, 4, 7, 1] [1, 0, 0, 0, 1, 1, 0]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded