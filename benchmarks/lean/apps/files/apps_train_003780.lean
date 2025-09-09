def find_even_index (arr : List Int) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum_list (arr : List Int) : Int :=
  sorry

theorem find_even_index_centered {n : Nat} :
  let arr := List.replicate n 1 ++ [0] ++ List.replicate n 1
  find_even_index arr = n
  := sorry

theorem find_even_index_single_element :
  find_even_index [0] = 0 := sorry

theorem find_even_index_single_nonzero :
  find_even_index [1] = 0 := sorry

theorem find_even_index_all_zeros :
  find_even_index [0, 0, 0] = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_even_index [1, 2, 3, 4, 3, 2, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_even_index [1, 100, 50, -51, 1, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_even_index [20, 10, -80, 10, 10, 15, 35]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible