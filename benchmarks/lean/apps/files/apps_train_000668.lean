-- <vc-helpers>
-- </vc-helpers>

def is_good_permutation (n : Nat) (arr : List Nat) : Bool := sorry

theorem single_element_permutation_valid (n : Nat) :
  n = 1 → is_good_permutation n [1] = true := sorry

theorem basic_properties_sorted (n : Nat) (arr : List Nat) :
  arr = List.range' 1 n → is_good_permutation n arr = true := sorry

theorem small_permutations_valid (n : Nat) (arr : List Nat) :
  n ≤ 2 → arr = List.range' 1 n → is_good_permutation n arr = true := sorry 

theorem decreasing_sequence_invalid (n : Nat) :
  n ≥ 3 → 
  let arr := List.reverse (List.range' 1 n)
  is_good_permutation n arr = false := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_good_permutation 1 [1]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_good_permutation 2 [2, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_good_permutation 3 [3, 2, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_good_permutation 4 [1, 3, 2, 4]

-- Apps difficulty: interview
-- Assurance level: unguarded