-- <vc-helpers>
-- </vc-helpers>

def find_max_dish_type (n : Nat) (dishes : List Nat) : Nat :=
  sorry

theorem n_parameter_irrelevant (n : Nat) (dishes : List Nat) 
    (h : dishes ≠ []) : 
    find_max_dish_type n dishes = find_max_dish_type dishes.length dishes :=
  sorry

theorem preserves_input (dishes : List Nat) (h : dishes ≠ []) : 
    let original := dishes;
    let _ := find_max_dish_type dishes.length dishes;
    dishes = original :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_dish_type 5 [1, 2, 2, 1, 2]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_max_dish_type 6 [1, 1, 1, 1, 1, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_max_dish_type 8 [1, 2, 2, 2, 3, 4, 2, 1]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible