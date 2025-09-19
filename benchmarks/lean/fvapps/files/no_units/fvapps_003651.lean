-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def product (nums : List Int) : Option Int := sorry

theorem product_empty (nums : List Int) : 
  nums = [] → product nums = none
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem product_nonempty (nums : List Int) : 
  nums ≠ [] → product nums = some (nums.foldl (·*·) 1)
  := sorry

theorem product_positive (nums : List Int) (h : ∀ x ∈ nums, x > 0) :
  product nums = some (nums.foldl (·*·) 1) → nums.foldl (·*·) 1 > 0
  := sorry

theorem product_negative_parity (nums : List Int) (h : ∀ x ∈ nums, x < 0) :
  product nums = some (nums.foldl (·*·) 1) → 
    (nums.foldl (·*·) 1 > 0) = (nums.length % 2 = 0)
  := sorry

theorem product_commutative (nums : List Int) (h : nums.length ≥ 2) :
  product nums = product nums.reverse
  := sorry
-- </vc-theorems>