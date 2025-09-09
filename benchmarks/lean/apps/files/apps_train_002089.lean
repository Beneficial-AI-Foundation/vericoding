-- <vc-helpers>
-- </vc-helpers>

def find_min_changes (arr : List Nat) : Nat :=
sorry

theorem output_bounds {arr : List Nat} : 
  0 ≤ find_min_changes arr ∧ find_min_changes arr ≤ arr.length :=
sorry

theorem identical_elements {n : Nat} {arr : List Nat} : 
  arr = List.replicate arr.length n → find_min_changes arr = 0 :=
sorry 

theorem increasing_sequence {arr : List Nat} :
  let sorted_unique := arr.eraseDups
  find_min_changes sorted_unique ≤ sorted_unique.length - 1 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_min_changes [3, 7, 3, 7, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_min_changes [1, 2, 1, 2, 3, 1, 1, 1, 50, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min_changes [6, 6, 3, 3, 4, 4]

-- Apps difficulty: competition
-- Assurance level: unguarded