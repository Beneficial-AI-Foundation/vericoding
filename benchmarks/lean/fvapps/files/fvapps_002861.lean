-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Int) : Int := sorry 

def pairs (nums : List Int) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pairs_consecutive_property {nums : List Int} (h : nums.length ≥ 2) :
  pairs nums = (List.filter (fun i => 
    (abs (nums.get! (2*i) - nums.get! (2*i + 1))) = 1) (List.range ((nums.length - 1)/2))).length := sorry

theorem pairs_modification_invariant {nums : List Int} (h : nums.length ≥ 2) 
  (modified : List Int) (h_mod : modified.length = nums.length)
  (h_even : ∀ i, i % 2 = 0 → i < nums.length → modified.get! i = nums.get! i) :
  pairs nums = pairs modified ∨ 
  ∃ i, i < nums.length - 1 ∧ (abs (modified.get! i - modified.get! (i+1))) = 1 := sorry

theorem pairs_bounded {nums : List Int} (h : nums.length ≥ 2)
  (h_bounds : ∀ x ∈ nums, -1000 ≤ x ∧ x ≤ 1000) :
  0 ≤ pairs nums ∧ pairs nums ≤ nums.length / 2 := sorry
-- </vc-theorems>