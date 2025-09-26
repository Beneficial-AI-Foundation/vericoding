-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_of_subarrays (nums: List Int) (k: Int) : Int := sorry

theorem non_negative_output {nums: List Int} {k: Int} 
  (h1: ∀ x ∈ nums, 1 ≤ x ∧ x ≤ 100) (h2: 1 ≤ k ∧ k ≤ 100) : 
  number_of_subarrays nums k ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>