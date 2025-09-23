-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_circle_num (M : Matrix) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem isolated_students {n : Nat} (h : n > 0) :
  let M : Matrix := { 
    data := List.replicate n (List.replicate n 0)
    all_rows_same_length := sorry
    entries_zero_or_one := sorry
    symmetric := sorry
    diagonal_ones := sorry
  }
  find_circle_num M = n :=
  sorry

theorem fully_connected {n : Nat} (h : n > 0) :
  let M : Matrix := { 
    data := List.replicate n (List.replicate n 1)
    all_rows_same_length := sorry
    entries_zero_or_one := sorry
    symmetric := sorry
    diagonal_ones := sorry
  }
  find_circle_num M = 1 :=
  sorry

theorem circles_bound (M : Matrix) (h : M.data.length = 3) :
  1 ≤ find_circle_num M ∧ find_circle_num M ≤ M.data.length :=
  sorry

theorem two_by_two_circles (M : Matrix) (h : M.data.length = 2) :
  find_circle_num M = 1 ∨ find_circle_num M = 2 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_circle_num [[1, 1, 0], [1, 1, 0], [0, 0, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_circle_num [[1, 1, 0], [1, 1, 1], [0, 1, 1]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_circle_num [[1, 0, 0], [0, 1, 0], [0, 0, 1]]
-- </vc-theorems>