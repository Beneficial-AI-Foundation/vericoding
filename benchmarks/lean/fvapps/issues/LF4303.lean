-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def prime_or_composite (n : Int) : Result :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem even_numbers_are_composite {n : Int} 
  (h1 : n ≥ 4) (h2 : n % 2 = 0) : 
  prime_or_composite n = Result.Composite :=
sorry

theorem two_and_three_are_prime {n : Int}
  (h : n = 2 ∨ n = 3) :
  prime_or_composite n = Result.ProbablePrime := 
sorry

theorem numbers_less_than_2_are_probable_prime {n : Int}
  (h : n ≤ 1) :
  prime_or_composite n = Result.ProbablePrime :=
sorry

theorem perfect_squares_are_composite {n : Int}
  (h1 : n > 1) :
  prime_or_composite (n * n) = Result.Composite :=
sorry

theorem product_greater_than_one_is_composite {a b : Int}
  (h1 : a > 1) (h2 : b > 1) :
  prime_or_composite (a * b) = Result.Composite :=
sorry

/-
info: 'Probable Prime'
-/
-- #guard_msgs in
-- #eval prime_or_composite 2

/-
info: 'Probable Prime'
-/
-- #guard_msgs in
-- #eval prime_or_composite 3

/-
info: 'Composite'
-/
-- #guard_msgs in
-- #eval prime_or_composite 9

/-
info: 'Composite'
-/
-- #guard_msgs in
-- #eval prime_or_composite 12
-- </vc-theorems>