-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_beautiful_permutation (nums : List Nat) : List Nat := sorry

theorem solve_first_pos_beautiful (nums : List Nat) 
  (h : nums.length = 5) 
  (h2 : nums.Perm [1,2,3,4,5]) : 
  (solve_beautiful_permutation nums).get! 0 = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_preserves_length (nums : List Nat)  
  (h : nums.length = 5)
  (h2 : nums.Perm [1,2,3,4,5]) :
  (solve_beautiful_permutation nums).length = nums.length := sorry 

theorem solve_returns_binary (nums : List Nat)
  (h : nums.length = 5)
  (h2 : nums.Perm [1,2,3,4,5]) :
  ∀ x ∈ solve_beautiful_permutation nums, x = 0 ∨ x = 1 := sorry
-- </vc-theorems>