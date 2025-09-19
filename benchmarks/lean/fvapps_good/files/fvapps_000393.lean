-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_increasing_triplet (nums : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem has_increasing_triplet_matches_bruteforce (nums : List Int) (h : nums.length ≥ 3) :
  has_increasing_triplet nums = 
    (∃ i j k, i < j ∧ j < k ∧ k < nums.length ∧
     nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!) :=
  sorry

theorem monotonic_decreasing_has_no_triplet (nums : List Int) (h : nums.length ≥ 3) :
  (∀ i j, i < j → j < nums.length → nums[j]! ≤ nums[i]!) →
  ¬(has_increasing_triplet nums) :=
  sorry

theorem monotonic_increasing_has_triplet (nums : List Int) 
  (h1 : nums.length ≥ 3)
  (h2 : ∀ i j, i < j → j < nums.length → nums[i]! ≤ nums[j]!)
  (h3 : ∀ x, (nums.countP (fun y => y = x)) ≤ 2) :
  has_increasing_triplet nums :=
  sorry

theorem short_lists_have_no_triplet (nums : List Int) (h : nums.length < 3) :
  ¬(has_increasing_triplet nums) :=
  sorry
-- </vc-theorems>