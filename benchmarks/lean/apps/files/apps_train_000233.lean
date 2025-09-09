-- <vc-helpers>
-- </vc-helpers>

def num_subarrays_with_sum (nums : List Nat) (target : Nat) : Nat :=
  sorry

theorem binary_array_properties_nonneg {nums : List Nat} (h : ∀ x ∈ nums, x ≤ 1) :
  num_subarrays_with_sum nums 0 ≥ 0 :=
  sorry

theorem binary_array_properties_beyond_sum {nums : List Nat} (h : ∀ x ∈ nums, x ≤ 1) :
  num_subarrays_with_sum nums ((List.sum nums) + 1) = 0 :=
  sorry

theorem binary_array_properties_total {nums : List Nat} (h : ∀ x ∈ nums, x ≤ 1) (total : Nat)
  (h_total : total = List.sum nums) (h_pos : total > 0) :
  num_subarrays_with_sum nums total ≥ 1 :=
  sorry

theorem consecutive_zeros {nums : List Nat} (h : nums ≠ []) (h_zeros : ∀ x ∈ nums, x = 0) :
  num_subarrays_with_sum nums 0 = (nums.length * (nums.length + 1)) / 2 :=
  sorry

theorem single_element_subarrays {nums : List Nat} (h : nums ≠ []) (h_bin : ∀ x ∈ nums, x ≤ 1)
  (ones_count : Nat) (h_ones : ones_count = List.sum nums) (h_pos : ones_count > 0) :
  num_subarrays_with_sum nums 1 ≥ ones_count :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval num_subarrays_with_sum [1, 0, 1, 0, 1] 2

/-
info: 15
-/
-- #guard_msgs in
-- #eval num_subarrays_with_sum [0, 0, 0, 0, 0] 0

-- Apps difficulty: interview
-- Assurance level: unguarded