-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_expected_sum (num_pages : Nat) (unprinted : List Nat) (num_torn : Nat) : Float := sorry

theorem identity_property_one :
  calculate_expected_sum 1 [] 0 = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identity_property_two :
  calculate_expected_sum 2 [] 0 = 3 := sorry

theorem result_non_negative (num_pages : Nat) (unprinted : List Nat) (num_torn : Nat)
  (h1 : ∀ p ∈ unprinted, p ≤ num_pages)
  (h2 : num_torn ≤ (num_pages + 1) / 2) :
  calculate_expected_sum num_pages unprinted num_torn ≥ 0 := sorry

theorem result_upper_bound (num_pages : Nat) (unprinted : List Nat) (num_torn : Nat)
  (h1 : ∀ p ∈ unprinted, p ≤ num_pages)
  (h2 : num_torn ≤ (num_pages + 1) / 2) :
  calculate_expected_sum num_pages unprinted num_torn ≤ Float.ofNat (num_pages * (num_pages + 1) / 2) := sorry

theorem no_modifications (num_pages : Nat) :
  Float.abs (calculate_expected_sum num_pages [] 0 - Float.ofNat (num_pages * (num_pages + 1) / 2)) < 0.0001 := sorry

theorem unprinted_reduces_sum (num_pages : Nat) (unprinted : List Nat)
  (h1 : ∀ p ∈ unprinted, p ≤ num_pages)
  (h2 : unprinted ≠ []) :
  calculate_expected_sum num_pages unprinted 0 ≤ calculate_expected_sum num_pages [] 0 := sorry
-- </vc-theorems>