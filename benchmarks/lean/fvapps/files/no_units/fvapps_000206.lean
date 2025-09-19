-- <vc-preamble>
def abs (i : Int) : Int :=
  if i ≥ 0 then i else -i
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def containsNearbyAlmostDuplicate (nums : List Int) (k : Int) (t : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem invalid_inputs_property (nums : List Int) (k : Int) (t : Int) :
  k ≤ 0 → t < 0 → ¬containsNearbyAlmostDuplicate nums k t :=
  sorry

theorem sliding_window_symmetry (nums : List Int) (k : Int) (t : Int) :
  k > 0 → t ≥ 0 → nums.length ≥ 2 → nums.length ≤ 100 →
  containsNearbyAlmostDuplicate nums k t = containsNearbyAlmostDuplicate nums.reverse k t :=
  sorry

theorem zero_threshold_property (nums : List Int) (k : Int) :
  k > 0 → nums.length ≥ 2 → nums.length ≤ 100 →
  containsNearbyAlmostDuplicate nums k 0 = 
    (∃ i j, 0 ≤ i ∧ i < nums.length ∧ 
            0 ≤ j ∧ j < nums.length ∧
            i ≠ j ∧ abs (i - j) ≤ k ∧
            nums[i]! = nums[j]!) :=
  sorry

theorem scaling_invariance (nums : List Int) (k t scale : Int) :
  k > 0 → t ≥ 0 → scale > 0 → nums.length ≥ 2 → nums.length ≤ 100 →
  containsNearbyAlmostDuplicate nums k t = 
  containsNearbyAlmostDuplicate (nums.map (· * scale)) k (t * scale) :=
  sorry
-- </vc-theorems>