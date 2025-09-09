/-
### Unfinished Loop - Bug Fixing #1

Oh no, Timmy's created an infinite loop! Help Timmy find and fix the bug in his unfinished for loop!
-/

-- <vc-helpers>
-- </vc-helpers>

def create_array (n : Nat) : Array Nat := sorry

theorem create_array_length (n : Nat) :
  (create_array n).size = n := sorry

theorem create_array_sequential (n : Nat) (i : Nat) (h : i < n) : 
  have h' : i < (create_array n).size := by rw [create_array_length]; exact h
  (create_array n)[i]'h' = i + 1 := sorry

theorem create_array_increasing (n : Nat) (i j : Nat) 
  (hi : i < n) (hj : j < n) (h_order : i < j) :
  have hi' : i < (create_array n).size := by rw [create_array_length]; exact hi
  have hj' : j < (create_array n).size := by rw [create_array_length]; exact hj
  (create_array n)[i]'hi' < (create_array n)[j]'hj' := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval create_array 1

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval create_array 3

/-
info: [1, 2, 3, 4, 5]
-/
-- #guard_msgs in
-- #eval create_array 5

-- Apps difficulty: introductory
-- Assurance level: guarded