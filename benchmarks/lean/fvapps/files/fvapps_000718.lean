-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_prime (n : Nat) : Bool :=
  sorry

def check_land_split (x y : Nat) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_prime_properties (n : Nat) (h : n ≤ 1000) :
  (n < 2 → is_prime n = false) ∧
  (is_prime n = true → n ≥ 2) ∧
  (is_prime n = true → ∀ i : Nat, 2 ≤ i → i ≤ 100 → ¬(n % i = 0)) :=
sorry

theorem check_land_split_properties (x y : Nat) (h₁ : x ≤ 100) (h₂ : y ≤ 100) (h₃ : y ≤ x) :
  (check_land_split x y = "YES" ∨ check_land_split x y = "NO") ∧
  (check_land_split x y = "NO" ↔ is_prime (x*x - y*y)) :=
sorry

theorem check_land_split_equal_sides (x : Nat) (h : x ≤ 100) :
  check_land_split x x = "YES" :=
sorry

theorem check_land_split_zero_inner (x : Nat) (h : x ≤ 100) :
  check_land_split x 0 = "NO" ↔ is_prime (x*x) :=
sorry
-- </vc-theorems>