

/-!
{
"name": "dafny-synthesis_task_id_555_DifferenceSumCubesAndSumNumbers",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_555_DifferenceSumCubesAndSumNumbers",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Computes the difference between the sum of cubes and sum of numbers up to n.
Input: A non-negative integer n
Output: The difference between sum of cubes and sum of numbers
-/
def DifferenceSumCubesAndSumNumbers (n : Int) : Int := sorry

/--
Specification for DifferenceSumCubesAndSumNumbers:
- Requires n to be non-negative
- Ensures the result is (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
-/
theorem DifferenceSumCubesAndSumNumbers_spec (n : Int) :
n ≥ 0 →
DifferenceSumCubesAndSumNumbers n = (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2 := sorry
