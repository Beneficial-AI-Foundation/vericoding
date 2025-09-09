-- <vc-helpers>
-- </vc-helpers>

def solve_beautiful_permutation (nums : List Nat) : List Nat := sorry

theorem solve_first_pos_beautiful (nums : List Nat) 
  (h : nums.length = 5) 
  (h2 : nums.Perm [1,2,3,4,5]) : 
  (solve_beautiful_permutation nums).get! 0 = 1 := sorry

theorem solve_preserves_length (nums : List Nat)  
  (h : nums.length = 5)
  (h2 : nums.Perm [1,2,3,4,5]) :
  (solve_beautiful_permutation nums).length = nums.length := sorry 

theorem solve_returns_binary (nums : List Nat)
  (h : nums.length = 5)
  (h2 : nums.Perm [1,2,3,4,5]) :
  ∀ x ∈ solve_beautiful_permutation nums, x = 0 ∨ x = 1 := sorry

/-
info: '101011'
-/
-- #guard_msgs in
-- #eval solve_beautiful_permutation [4, 5, 1, 3, 2, 6]

/-
info: '11111'
-/
-- #guard_msgs in
-- #eval solve_beautiful_permutation [5, 3, 1, 2, 4]

/-
info: '1001'
-/
-- #guard_msgs in
-- #eval solve_beautiful_permutation [1, 4, 3, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded