-- <vc-helpers>
-- </vc-helpers>

def delete_nth (lst: List Int) (max_e: Nat) : List Int := sorry

theorem delete_nth_length {lst: List Int} {max_e: Nat} :
  List.length (delete_nth lst max_e) ≤ List.length lst := sorry

theorem delete_nth_max_occurrences {lst: List Int} {max_e: Nat} {x: Int} :
  x ∈ delete_nth lst max_e → List.count x (delete_nth lst max_e) ≤ max_e := sorry

theorem delete_nth_elements_from_original {lst: List Int} {max_e: Nat} {x: Int} :
  x ∈ delete_nth lst max_e → x ∈ lst := sorry 

theorem delete_nth_zero {lst: List Int} :
  delete_nth lst 0 = [] := sorry

theorem delete_nth_empty {lst: List Int} {max_e: Nat} :
  lst = [] → delete_nth lst max_e = [] := sorry

theorem delete_nth_preserves_first {lst: List Int} {max_e: Nat} :
  max_e > 0 → ∀ x, x ∈ lst → x ∈ delete_nth lst max_e := sorry

/-
info: [20, 37, 21]
-/
-- #guard_msgs in
-- #eval delete_nth [20, 37, 20, 21] 1

/-
info: [1, 1, 3, 3, 7, 2, 2, 2]
-/
-- #guard_msgs in
-- #eval delete_nth [1, 1, 3, 3, 7, 2, 2, 2, 2] 3

/-
info: []
-/
-- #guard_msgs in
-- #eval delete_nth [] 5

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible