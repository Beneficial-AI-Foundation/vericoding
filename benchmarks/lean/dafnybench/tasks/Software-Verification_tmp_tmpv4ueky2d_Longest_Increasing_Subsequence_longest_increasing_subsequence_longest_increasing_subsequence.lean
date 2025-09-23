-- <vc-preamble>
def find_max (x y : Int) : Int :=
if x > y then x else y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_increasing_subsequence (nums : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem longest_increasing_subsequence_spec (nums : Array Int) :
(1 ≤ nums.size ∧ nums.size ≤ 2500) →
(∀ i, 0 ≤ i ∧ i < nums.size → -10000 ≤ nums[i]! ∧ nums[i]! ≤ 10000) →
longest_increasing_subsequence nums ≥ 1 :=
sorry
-- </vc-theorems>