

/-!
{
"name": "llm-verified-eval_tmp_tmpd2deqn_i_dafny_0_has_close_elements",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: llm-verified-eval_tmp_tmpd2deqn_i_dafny_0_has_close_elements",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/-- Absolute value function for real numbers -/
def abs (x : Float) : Float :=
if x < 0 then -x else x

/--
Checks if array has two different elements within threshold distance.
Returns true if there exist two different elements whose difference is less than threshold.
-/
def has_close_elements (numbers : Array Float) (threshold : Float) : Bool :=
sorry

/--
Main specification theorem for has_close_elements:
1. Result is true iff there exist two different indices with elements within threshold
2. If result is true then array must have more than 1 element
-/
theorem has_close_elements_spec (numbers : Array Float) (threshold : Float) :
let result := has_close_elements numbers threshold
result ↔ (∃ i j : Nat,
i < numbers.size ∧
j < numbers.size ∧
i ≠ j ∧
abs (numbers[i]! - numbers[j]!) < threshold) ∧
(result → numbers.size > 1) := sorry
