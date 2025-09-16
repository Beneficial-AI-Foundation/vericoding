

/-!
{
"name": "dafny-synthesis_task_id_623_PowerOfListElements",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_623_PowerOfListElements",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Computes base raised to the given non-negative exponent.
Translated from Dafny's Power function.
-/
partial def Power (base : Int) (exponent : Int) : Int :=
if exponent == 0 then 1
else base * Power base (exponent - 1)

/--
Specification for Power function requiring non-negative exponent
-/
theorem Power_spec (base : Int) (exponent : Int) :
exponent ≥ 0 → Power base exponent ≥ 0 := sorry

/--
Takes an array of integers and returns a new array where each element
is raised to the power n. Translated from Dafny's PowerOfListElements method.
-/
def PowerOfListElements (l : Array Int) (n : Int) : Array Int := sorry

/--
Specification for PowerOfListElements ensuring:
1. The output array has same size as input
2. Each element is the corresponding input raised to power n
-/
theorem PowerOfListElements_spec (l : Array Int) (n : Int) :
n ≥ 0 →
let result := PowerOfListElements l n
result.size = l.size ∧
∀ i, 0 ≤ i ∧ i < l.size → result[i]! = Power l[i]! n := sorry
