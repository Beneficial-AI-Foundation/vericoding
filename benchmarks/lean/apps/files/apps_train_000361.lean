-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest_component_size (nums : List Nat) : Nat := sorry

theorem largest_component_size_bounds {nums : List Nat} (h : nums ≠ []) : 
  let result := largest_component_size nums
  0 < result ∧ result ≤ nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem largest_component_size_idempotent {nums : List Nat} :
  largest_component_size nums = largest_component_size nums := sorry

theorem all_evens_max_component {nums : List Nat} (h : nums.all (fun n => n % 2 = 0)) :
  largest_component_size nums = nums.length := sorry

theorem single_prime_component_one (p : Nat) :
  largest_component_size [p] = 1 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval largest_component_size [4, 6, 15, 35]

/-
info: 2
-/
-- #guard_msgs in
-- #eval largest_component_size [20, 50, 9, 63]

/-
info: 8
-/
-- #guard_msgs in
-- #eval largest_component_size [2, 3, 6, 7, 4, 12, 21, 39]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded