-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numIdenticalPairs (nums : List Int) : Nat := sorry

theorem num_identical_pairs_non_negative (nums : List Int) :
  numIdenticalPairs nums ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_or_single_is_zero (nums : List Int) :
  nums.length ≤ 1 → numIdenticalPairs nums = 0 := sorry

theorem all_same_values (nums : List Int) (n : Nat) (x : Int) :
  nums = List.replicate n x → n ≥ 2 →
  numIdenticalPairs nums = n * (n-1) / 2 := sorry
-- </vc-theorems>