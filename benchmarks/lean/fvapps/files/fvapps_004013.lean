-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isPrime (n : Nat) : Bool :=
  sorry

def goldbach (n : Nat) : List (List Nat) :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem goldbach_valid_sums {n : Nat} (h : n ≥ 4) (h2 : n % 2 = 0) :
  let result := goldbach n
  (∀ x ∈ result, x.length = 2) ∧
  (∀ x ∈ result, x[0]! + x[1]! = n) ∧
  (∀ x ∈ result, x[0]! ≤ x[1]!) :=
sorry

theorem goldbach_small_inputs {n : Nat} (h : n ≤ 3) :
  goldbach n = [] :=
sorry

theorem goldbach_four :
  goldbach 4 = [[2, 2]] :=
sorry
-- </vc-theorems>