-- <vc-preamble>
def list_max : List Nat → Nat
| [] => 0
| (x::xs) => max x (list_max xs)

def list_min : List Nat → Nat
| [] => 0
| (x::xs) => min x (list_min xs)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def gcd : Nat → Nat → Nat
| a, b =>
sorry

def max_gcd_sum : List Nat → Nat
| xs =>
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matches_reference (nums : List Nat) (h : ∀ x ∈ nums, x > 0) :
  ∃ result, max_gcd_sum nums = result := by
  sorry

theorem output_larger_than_input (nums : List Nat) (h : ∀ x ∈ nums, x > 0) :
  max_gcd_sum nums ≥ list_max nums ∧ max_gcd_sum nums ≥ list_min nums := by
  sorry

theorem duplicate_handling (nums : List Nat) (dupes : List Nat)
  (h : ∀ x ∈ nums, x > 0) (h2 : ∀ x ∈ dupes, x ∈ nums) :
  max_gcd_sum nums = max_gcd_sum (nums ++ dupes) := by
  sorry

theorem single_element (x : Nat) (h : x > 0) :
  max_gcd_sum [x] = 2 * x := by
  sorry
-- </vc-theorems>