

/-!
{
"name": "Dafny_tmp_tmp0wu8wmfr_tests_InsertionSortSeq_InsertionSort",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Dafny_tmp_tmp0wu8wmfr_tests_InsertionSortSeq_InsertionSort",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Predicate indicating if an array is sorted in ascending order -/
def IsSorted (s : Array Int) : Prop :=
∀ p q, 0 ≤ p → p < q → q < s.size → s[p]! ≤ s[q]!

/-- InsertionSort function that sorts an array of integers
Returns a sorted array containing the same elements as the input -/
def InsertionSort (s : Array Int) : Array Int := sorry

/-- Specification for InsertionSort:
1. Output array contains same elements as input (preserves array)
2. Output array is sorted -/
theorem InsertionSort_spec (s : Array Int) :
let r := InsertionSort s
(r = s) ∧ IsSorted r := sorry
