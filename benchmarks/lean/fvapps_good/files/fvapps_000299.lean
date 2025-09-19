-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def combination_sum4 (nums : List Int) (target : Int) : Int := sorry

theorem combination_sum4_non_negative (nums : List Int) (target : Int) 
    (h1 : ∀ n ∈ nums, n > 0) (h2 : target > 0) :
  combination_sum4 nums target ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem combination_sum4_matches_single 
    (nums : List Int) (target : Int)
    (h1 : target ∈ nums) (h2 : ∀ n ∈ nums, n > 0) (h3 : target > 0) :
  combination_sum4 nums target ≥ 1 := sorry

theorem combination_sum4_all_greater
    (nums : List Int) (target : Int)
    (h1 : ∀ n ∈ nums, n > target) (h2 : target > 0) :
  combination_sum4 nums target = 0 := sorry

theorem combination_sum4_less_than_min
    (nums : List Int) (target : Int)
    (h1 : ∀ n ∈ nums, n > 0) 
    (h2 : target > 0)
    (h3 : ∀ n ∈ nums, target < n) :
  combination_sum4 nums target = 0 := sorry

theorem combination_sum4_order_independent
    (nums₁ nums₂ : List Int) (target : Int)
    (h1 : ∀ n ∈ nums₁, n > 0) 
    (h2 : target > 0)
    (h3 : ∀ n, n ∈ nums₁ ↔ n ∈ nums₂) :
  combination_sum4 nums₁ target = combination_sum4 nums₂ target := sorry
-- </vc-theorems>