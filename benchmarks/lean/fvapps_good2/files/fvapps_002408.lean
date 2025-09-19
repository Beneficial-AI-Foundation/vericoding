-- <vc-preamble>
def is_strictly_increasing (nums : List Int) (i : Nat) : Bool :=
  i > 0 && i < nums.length && nums[i]! > nums[i-1]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_length_of_lcis (nums : List Int) : Nat :=
sorry

def count_max_increasing (nums : List Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem lcis_length_properties (nums : List Int) :
  let result := find_length_of_lcis nums
  result ≥ 0 ∧
  result ≤ nums.length ∧
  (nums.length = 0 → result = 0) ∧
  (nums.length > 0 → result ≥ 1) :=
sorry
-- </vc-theorems>