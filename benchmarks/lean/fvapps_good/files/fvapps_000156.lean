-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def constrained_max_subset_sum (nums : List Int) (k : Nat) : Int := sorry

theorem constrained_max_subset_sum_ge_max_single (nums : List Int) (k : Nat) 
    (h : nums ≠ []) (hk : k > 0) :
    ∀ x ∈ nums, constrained_max_subset_sum nums k ≥ x := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem constrained_max_subset_sum_all_negative (nums : List Int) (k : Nat)
    (h : nums ≠ []) (hk : k > 0) (h_neg : ∀ x ∈ nums, x < 0) :
    ∃ x ∈ nums, constrained_max_subset_sum nums k = x := sorry

theorem constrained_max_subset_sum_independence (nums : List Int) (k : Nat)
    (h : nums.length > k + 1) (hk : k > 0) :
    let nums_modified := (nums.take (k+1)).append (List.replicate (nums.length - k - 1) (-1000))
    constrained_max_subset_sum (nums.take (k+1)) k = constrained_max_subset_sum nums_modified k := sorry
-- </vc-theorems>