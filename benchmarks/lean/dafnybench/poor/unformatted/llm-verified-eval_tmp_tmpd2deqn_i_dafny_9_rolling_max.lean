

/-!
{
"name": "llm-verified-eval_tmp_tmpd2deqn_i_dafny_9_rolling_max",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: llm-verified-eval_tmp_tmpd2deqn_i_dafny_9_rolling_max",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if m is the maximum value in the given array of numbers.
Translated from Dafny function isMax.
-/
def isMax (m : Int) (numbers : Array Int) : Prop :=
numbers.contains m ∧
∀ i, 0 ≤ i ∧ i < numbers.size → numbers[i]! ≤ m

/--
Returns an array containing the rolling maximum values.
Each element i contains the maximum value from index 0 to i.
Translated from Dafny method rolling_max.
-/
def rolling_max (numbers : Array Int) : Array Int :=
sorry

/--
Specification for rolling_max method.
Ensures:
1. Output array has same size as input
2. Each element is the maximum of all previous elements up to that index
-/
theorem rolling_max_spec (numbers : Array Int) :
numbers.size > 0 →
let result := rolling_max numbers
result.size = numbers.size ∧
∀ i, 0 < i ∧ i < result.size →
isMax (result[i]!) (numbers.extract 0 (i + 1)) := sorry
