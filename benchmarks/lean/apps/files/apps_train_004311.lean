-- <vc-helpers>
-- </vc-helpers>

def SumEvenFibonacci (n : Int) : Int :=
  sorry

-- Properties for any non-negative input

theorem sum_even_fibonacci_non_negative (n : Int) : 
  n ≥ 0 → SumEvenFibonacci n ≥ 0 :=
  sorry

-- Base cases

theorem sum_even_fibonacci_zero :
  SumEvenFibonacci 0 = 0 :=
  sorry

theorem sum_even_fibonacci_one :
  SumEvenFibonacci 1 = 0 :=
  sorry

theorem sum_even_fibonacci_two :
  SumEvenFibonacci 2 = 2 :=
  sorry

-- Property for negative inputs

theorem sum_even_fibonacci_negative (n : Int) :
  n < 0 → SumEvenFibonacci n = 0 :=
  sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval SumEvenFibonacci 8

/-
info: 60696
-/
-- #guard_msgs in
-- #eval SumEvenFibonacci 111111

/-
info: 82790070
-/
-- #guard_msgs in
-- #eval SumEvenFibonacci 144100000

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible