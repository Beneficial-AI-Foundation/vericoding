-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def productArray (nums : List Int) : List Int := sorry

theorem product_array_length 
  (nums : List Int) 
  (h : nums.length ≥ 2) :
  (productArray nums).length = nums.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem product_array_element_is_product_of_others
  (nums : List Int)
  (h : nums.length ≥ 2)
  (i : Nat)
  (hi : i < nums.length) :
  let result := productArray nums
  have h_valid : i < result.length := by rw [product_array_length nums h]; exact hi
  result[i]'h_valid = 
    ((List.range nums.length).filter (· ≠ i)).foldl 
      (fun acc j => have h_j : j < nums.length := sorry; acc * nums[j]'h_j) 1 := sorry

theorem product_array_symmetry
  (nums : List Int)
  (h : nums.length ≥ 2)
  (i : Nat)
  (hi : i < nums.length) :
  let result := productArray nums
  have h_valid : i < result.length := by rw [product_array_length nums h]; exact hi
  have h_valid_0 : 0 < result.length := by rw [product_array_length nums h]; exact Nat.zero_lt_of_lt hi
  result[i]'h_valid * nums[i]'hi = result[0]'h_valid_0 * nums[0]'(Nat.zero_lt_of_lt hi) := sorry

/-
info: [20, 12]
-/
-- #guard_msgs in
-- #eval product_array #[12, 20]

/-
info: [216, 24, 162, 324]
-/
-- #guard_msgs in
-- #eval product_array #[3, 27, 4, 2]

/-
info: [900, 1170, 2340, 5850, 1300]
-/
-- #guard_msgs in
-- #eval product_array #[13, 10, 5, 2, 9]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded