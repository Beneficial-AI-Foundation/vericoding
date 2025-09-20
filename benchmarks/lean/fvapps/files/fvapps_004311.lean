-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SumEvenFibonacci (n : Int) : Int :=
  sorry

-- Properties for any non-negative input
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>