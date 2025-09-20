-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numberProperty (n : Int) : List Bool := sorry
def isPrime (n : Int) : Bool := sorry

/- The number_property function always returns a list of exactly 3 booleans -/
-- </vc-definitions>

-- <vc-theorems>
theorem numberProperty_returns_three_bools (n : Int) : 
  let result := numberProperty n
  result.length = 3 ∧ result.all (λ x => x = true ∨ x = false) := sorry

/- The second element of number_property indicates if the number is even -/

theorem even_property_matches_modulo (n : Int) :
  (numberProperty n).get! 1 = (n % 2 = 0) := sorry

/- The third element of number_property indicates if the number is divisible by 10 -/

theorem multiple_of_ten_property (n : Int) :
  (numberProperty n).get! 2 = (n % 10 = 0) := sorry

/- For positive numbers, the first element indicates primality -/

theorem prime_property_positive (n : Int) :
  0 ≤ n → n ≤ 100 →
  (if n ≤ 1 
   then (numberProperty n).get! 0 = false
   else (numberProperty n).get! 0 = isPrime n) := sorry

/- Negative numbers are never marked as prime -/

theorem negative_numbers_not_prime (n : Int) :
  n < 0 → (numberProperty n).get! 0 = false := sorry

/- Multiples of 10 are always marked as even -/

theorem multiples_of_ten_are_even (n : Int) :
  (numberProperty n).get! 2 = true → 
  (numberProperty n).get! 1 = true := sorry
-- </vc-theorems>