-- <vc-preamble>
def isPerfectSquare (n : Nat) : Prop :=
  ∃ k : Nat, k * k = n
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_squared (m n : Nat) : List (Nat × Nat) :=
sorry

def sumOfSquaredDivisors (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem list_squared_result_valid (m n : Nat) (h : 0 < m) (h2 : 0 < n) :
  let result := list_squared m n
  ∀ pair ∈ result,
    ∃ (a b : Nat), pair = (a, b) ∧
    m ≤ a ∧ a ≤ n :=
sorry

theorem list_squared_divisors_sum (m n : Nat) (h : 0 < m) (h2 : 0 < n) :
  let result := list_squared m n
  ∀ pair ∈ result, pair.2 = sumOfSquaredDivisors pair.1 :=
sorry

theorem list_squared_is_sorted (m n : Nat) (h : 0 < m) (h2 : 0 < n) :
  let result := list_squared m n
  ∀ i, i + 1 < result.length →
    (result[i]'sorry).1 < (result[i+1]'sorry).1 :=
sorry

theorem list_squared_perfect_squares (m n : Nat) (h : 0 < m) (h2 : 0 < n) :
  let result := list_squared m n
  ∀ pair ∈ result, isPerfectSquare pair.2 :=
sorry

theorem list_squared_single_point (n : Nat) (h : 0 < n) :
  let result := list_squared n n
  result = [] ∨ result = [(n, sumOfSquaredDivisors n)] :=
sorry

theorem list_squared_empty (m n : Nat) :
  m > n → list_squared m n = [] :=
sorry
-- </vc-theorems>