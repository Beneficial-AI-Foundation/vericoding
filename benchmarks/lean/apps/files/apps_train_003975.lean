-- <vc-preamble>
def odd_dig_cubic (a b : Int) : List Int :=
  sorry

-- Helper function to check if a number's digits are all odd

def hasAllOddDigits (n : Int) : Bool :=
  sorry

-- Helper function to check if a number is a perfect cube
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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

/-
info: [-3375, -1331, -1, 1, 1331, 3375]
-/
-- #guard_msgs in
-- #eval odd_dig_cubic -5000 5000

/-
info: [1, 1331, 3375]
-/
-- #guard_msgs in
-- #eval odd_dig_cubic 0 5000

/-
info: [-3375, -1331]
-/
-- #guard_msgs in
-- #eval odd_dig_cubic -5000 -2
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded