import Mathlib


/-!
{
"name": "Clover_avg_ComputeAvg",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_avg_ComputeAvg",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
ComputeAvg computes the average of two integers.

@param a First integer input
@param b Second integer input
@return The average of a and b, computed as (a+b)/2
-/
def ComputeAvg (a b : Int) : Int := sorry

/--
Specification for ComputeAvg ensuring the result is (a+b)/2
-/
theorem ComputeAvg_spec (a b : Int) :
ComputeAvg a b = (a + b) / 2 := sorry