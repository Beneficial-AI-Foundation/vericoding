-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def getMaxLen (nums : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem getMaxLen_nonnegative (nums : List Int) : 
  getMaxLen nums ≥ 0 := sorry

theorem getMaxLen_upper_bound (nums : List Int) :
  getMaxLen nums ≤ nums.length := sorry

theorem getMaxLen_all_zeros {nums : List Int} (h : ∀ x ∈ nums, x = 0) : 
  getMaxLen nums = 0 := sorry

theorem getMaxLen_zeros_only (n : Nat) : 
  getMaxLen (List.replicate n 0) = 0 := sorry
-- </vc-theorems>