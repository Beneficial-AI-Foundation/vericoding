/-
You will be given an array of numbers.

For each number in the array you will need to create an object. 

The object key will be the number, as a string. The value will be the corresponding character code, as a string.

Return an array of the resulting objects.

All inputs will be arrays of numbers. All character codes are valid lower case letters. The input array will not be empty.
-/

-- <vc-helpers>
-- </vc-helpers>

def num_obj (nums: List Nat) : List (String × Char) := sorry

def charOfNat (n: Nat) : Char := sorry

theorem num_obj_length {nums: List Nat} : 
  (nums.all (· ≤ 127)) → 
  (num_obj nums).length = nums.length := sorry

theorem num_obj_key_matches_input {nums: List Nat} :
  (nums.all (· ≤ 127)) →
  ∀ i, i < nums.length → 
  ((num_obj nums).get ⟨i, by sorry⟩).1 = toString (nums.get ⟨i, by sorry⟩) := sorry 

theorem num_obj_value_is_ascii {nums: List Nat} :
  (nums.all (· ≤ 127)) →
  ∀ i, i < nums.length →
  charOfNat (nums.get ⟨i, by sorry⟩) = ((num_obj nums).get ⟨i, by sorry⟩).2 := sorry

theorem num_obj_preserves_input {nums nums_copy: List Nat} :
  (nums.all (· ≤ 127)) →
  nums_copy = nums →
  nums_copy = nums := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval num_obj [118, 117, 120]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval num_obj [101, 121, 110]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval num_obj [100, 100, 116]

-- Apps difficulty: introductory
-- Assurance level: unguarded