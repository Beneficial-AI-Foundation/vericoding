-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute_expected_sweetness (n : Nat) (candies : List Nat) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem expected_sweetness_non_negative
    (n : Nat)
    (candies : List Nat)
    (h1 : n > 0)
    (h2 : n ≤ 10)
    (h3 : ∀ x ∈ candies, x ≤ 100) :
    compute_expected_sweetness n candies ≥ 0 := sorry

theorem expected_sweetness_bounded
    (n : Nat)
    (candies : List Nat)
    (h1 : n > 0)
    (h2 : n ≤ 10)
    (h3 : ∀ x ∈ candies, x ≤ 100) :
    ∃ (bound : Float), compute_expected_sweetness n candies ≤ bound := sorry

theorem expected_sweetness_max_bound
    (n : Nat)
    (candies : List Nat)
    (h1 : n > 0)
    (h2 : n ≤ 10)
    (h3 : ∀ x ∈ candies, x ≤ 100)
    (max : Nat)
    (h4 : ∀ x ∈ candies, x ≤ max) :
    compute_expected_sweetness n candies ≤ Float.ofNat (max * n) := sorry

theorem expected_sweetness_order_invariant
    (n : Nat)
    (candies : List Nat)
    (h1 : n > 0)
    (h2 : n ≤ 10)
    (h3 : ∀ x ∈ candies, x ≤ 100)
    (ε : Float)
    (h4 : ε = 0.000001) :
    compute_expected_sweetness n candies - compute_expected_sweetness n candies.reverse < ε ∧
    compute_expected_sweetness n candies.reverse - compute_expected_sweetness n candies < ε := sorry
-- </vc-theorems>