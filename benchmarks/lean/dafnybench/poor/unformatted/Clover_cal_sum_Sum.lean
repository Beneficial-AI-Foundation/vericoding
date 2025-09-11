


/-!
{
"name": "Clover_cal_sum_Sum",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_cal_sum_Sum",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Computes the Sum of first N natural numbers.
Translated from Dafny method Sum.

@param N The upper bound for summation
@return The Sum of numbers from 1 to N
-/
def SumPrime (N : Int) : Int := sorry

/--
Specification for SumPrime method:
- Requires N to be non-negative
- Ensures result equals N * (N + 1) / 2
-/
theorem Sum_spec (N : Int) :
N ≥ 0 → SumPrime N = N * (N + 1) / 2 := sorry