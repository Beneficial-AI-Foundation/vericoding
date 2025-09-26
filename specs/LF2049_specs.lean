-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_rooted_tree (n : Nat) (parents_and_counts : List (Nat × Nat)) : 
  String × List Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem minimal_single_node_case (n : Nat) (parents_and_counts : List (Nat × Nat)) :
  n = 1 → parents_and_counts = [(0,0)] → 
  solve_rooted_tree n parents_and_counts = ("YES", [1]) := sorry

theorem invalid_counts_yields_no (n : Nat) (parents_and_counts : List (Nat × Nat)) :
  n = 3 → parents_and_counts = [(2,3), (3,3), (0,3)] →
  solve_rooted_tree n parents_and_counts = ("NO", []) := sorry

theorem valid_tree_properties (n : Nat) (parents_and_counts : List (Nat × Nat)) 
  (result : String) (nums : List Nat) :
  n = 3 → parents_and_counts = [(2,0), (0,2), (2,0)] →
  solve_rooted_tree n parents_and_counts = (result, nums) →
  result = "YES" ∧ 
  nums.length = n ∧
  (∀ x ∈ nums, x ∈ [1,2,3]) := sorry

theorem output_properties (n : Nat) (parents_and_counts : List (Nat × Nat)) 
  (result : String) (nums : List Nat) :
  n = 5 → parents_and_counts = [(0,1), (1,3), (2,1), (3,0), (2,0)] →
  solve_rooted_tree n parents_and_counts = (result, nums) →
  (result = "YES" ∨ result = "NO") ∧
  (result = "YES" → 
    nums.length = n ∧
    (∀ x ∈ nums, 1 ≤ x ∧ x ≤ n) ∧
    (∀ x ∈ nums, ∀ y ∈ nums, x ≠ y → nums.indexOf x ≠ nums.indexOf y)) := sorry

/-
info: n
-/
-- #guard_msgs in
-- #eval len nums

/-
info: n
-/
-- #guard_msgs in
-- #eval len nums
-- </vc-theorems>