-- <vc-helpers>
-- </vc-helpers>

def pick (nums : List Int) (target : Int) : Nat :=
  sorry

theorem pick_returns_valid_index
  (nums : List Int) (target : Int) (h : nums ≠ []) (h2 : target ∈ nums) :
  let idx := pick nums target
  idx < nums.length ∧ nums[idx]! = target := by
  sorry

-- Apps difficulty: interview
-- Assurance level: guarded