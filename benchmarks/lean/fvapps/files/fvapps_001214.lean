-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def factorial_lookup (nums : List String) : List String := sorry

def String.toNat (s : String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem factorial_lookup_length (nums : List String) (h : nums.length > 0) :
  (factorial_lookup nums).length = nums.length - 1 := sorry

theorem factorial_lookup_output_type (nums : List String) (h : nums.length > 0) : 
  ∀ r ∈ factorial_lookup nums, (∀ c ∈ r.data, c.isDigit) := sorry

theorem factorial_lookup_monotonic (nums : List String) (h : nums.length > 0) :
  ∀ i < (factorial_lookup nums).length - 1,
    String.toNat (nums[i+1]!) < String.toNat (nums[i+2]!) → 
    String.toNat ((factorial_lookup nums)[i]!) < String.toNat ((factorial_lookup nums)[i+1]!) := sorry

theorem factorial_lookup_zero (nums : List String) 
  (h₁ : nums.length > 0)
  (h₂ : ∀ n ∈ nums, n = "0") :
  ∀ r ∈ factorial_lookup nums, r = "1" := sorry

theorem factorial_lookup_one (nums : List String)
  (h₁ : nums.length > 0) 
  (h₂ : ∀ n ∈ nums, n = "1") :
  ∀ r ∈ factorial_lookup nums, r = "1" := sorry
-- </vc-theorems>