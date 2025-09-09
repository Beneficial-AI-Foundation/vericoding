-- <vc-helpers>
-- </vc-helpers>

def number_of_subarrays (nums: List Int) (k: Int) : Int := sorry

theorem non_negative_output {nums: List Int} {k: Int} 
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100) (h2: 1 ≤ k ∧ k ≤ 100) : 
  number_of_subarrays nums k ≥ 0 := sorry

theorem zero_when_k_too_large {nums: List Int} {k: Int}
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100) (h2: 1 ≤ k ∧ k ≤ 100)
  (h3: k > nums.length) :
  number_of_subarrays nums k = 0 := sorry

theorem k_zero_or_negative_fails {nums: List Int} {k: Int}
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100) (h2: k ≤ 0) :
  ¬ ∃ result, number_of_subarrays nums k = result := sorry

theorem result_invariant_under_even_multiplication {nums: List Int} {k: Int}
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100) (h2: 1 ≤ k ∧ k ≤ 100) :
  number_of_subarrays nums k = number_of_subarrays (nums.map (λ x => if x % 2 = 0 then x * 2 else x)) k := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval number_of_subarrays [1, 1, 2, 1, 1] 3

/-
info: 0
-/
-- #guard_msgs in
-- #eval number_of_subarrays [2, 4, 6] 1

/-
info: 16
-/
-- #guard_msgs in
-- #eval number_of_subarrays [2, 2, 2, 1, 2, 2, 1, 2, 2, 2] 2

-- Apps difficulty: interview
-- Assurance level: guarded