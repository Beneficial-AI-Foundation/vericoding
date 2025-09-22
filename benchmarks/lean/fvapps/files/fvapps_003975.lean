-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_dig_cubic (a b : Int) : List Int :=
  sorry

def hasAllOddDigits (n : Int) : Bool :=
  sorry

def isPerfectCube (n : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_dig_cubic_sorted (a b : Int) :
  let result := odd_dig_cubic a b
  ∀ i, i + 1 < result.length → result[i]! ≤ result[i+1]! :=
sorry

theorem odd_dig_cubic_all_cubes (a b : Int) :
  let result := odd_dig_cubic a b
  ∀ n ∈ result, isPerfectCube n :=
sorry

theorem odd_dig_cubic_all_odd_digits (a b : Int) :
  let result := odd_dig_cubic a b
  ∀ n ∈ result, hasAllOddDigits n :=
sorry

theorem odd_dig_cubic_in_range (a b : Int) :
  let result := odd_dig_cubic a b
  ∀ n ∈ result, min a b ≤ n ∧ n ≤ max a b :=
sorry

theorem odd_dig_cubic_zero : odd_dig_cubic 0 0 = [] :=
sorry

theorem odd_dig_cubic_one : odd_dig_cubic 1 1 = [1] :=
sorry

theorem odd_dig_cubic_neg_one : odd_dig_cubic (-1) (-1) = [-1] :=
sorry

theorem odd_dig_cubic_single_point (n : Int) :
  let result := odd_dig_cubic n n
  result ≠ [] → result.length = 1 ∧ result[0]! = n :=
sorry
-- </vc-theorems>