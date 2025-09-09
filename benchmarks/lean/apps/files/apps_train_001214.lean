-- <vc-helpers>
-- </vc-helpers>

def factorial_lookup (nums : List String) : List String := sorry

def String.toNat (s : String) : Nat := sorry

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

/-
info: ['120', '24', '720']
-/
-- #guard_msgs in
-- #eval factorial_lookup ["3", "5", "4", "6"]

/-
info: ['6', '24']
-/
-- #guard_msgs in
-- #eval factorial_lookup ["2", "3", "4"]

/-
info: ['120']
-/
-- #guard_msgs in
-- #eval factorial_lookup ["1", "5"]

-- Apps difficulty: interview
-- Assurance level: unguarded