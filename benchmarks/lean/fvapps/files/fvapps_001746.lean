-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pick (nums : List Int) (target : Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pick_returns_valid_index
  (nums : List Int) (target : Int) (h : nums ≠ []) (h2 : target ∈ nums) :
  let idx := pick nums target
  idx < nums.length ∧ nums[idx]! = target := by
  sorry
-- </vc-theorems>