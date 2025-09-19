-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_subarray_sum (nums : List Int) (k : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem short_arrays {nums : List Int} {k : Int} (h1 : k ≠ 0) (h2 : nums.length ≤ 1) :
  check_subarray_sum nums k = false :=
  sorry

theorem properties_abs_k {nums : List Int} {k : Int} (h : k ≠ 0) :
  check_subarray_sum nums k = check_subarray_sum nums k.natAbs :=
  sorry

theorem properties_short {nums : List Int} {k : Int} (h : nums.length < 2) :
  check_subarray_sum nums k = false :=
  sorry

theorem zero_k {nums : List Int} (h : ∀ n ∈ nums, n ≥ 0) :
  check_subarray_sum nums 0 = 
    (∃ i, i + 1 < nums.length ∧ nums[i]! = 0 ∧ nums[i+1]! = 0) :=
  sorry

theorem k_one {nums : List Int} (h : nums.length ≥ 2) :
  check_subarray_sum nums 1 = true :=
  sorry

theorem multiples {nums : List Int} {k : Int} 
  (h1 : ∀ n ∈ nums, 0 ≤ n ∧ n ≤ 100)
  (h2 : 1 ≤ k ∧ k ≤ 100)
  (h3 : nums.length ≥ 2) :
  check_subarray_sum (nums.map (· * k)) k = true :=
  sorry
-- </vc-theorems>