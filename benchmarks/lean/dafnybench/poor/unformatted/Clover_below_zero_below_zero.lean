


/-!
{
"name": "Clover_below_zero_below_zero",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_below_zero_below_zero",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translates the Dafny below_zero method which checks if a sequence of operations
results in a negative value at any point.

@param operations The input sequence of operations
@return A tuple containing the resulting array and a boolean indicating if a negative value was found
-/
def below_zero (operations : Array Int) : Array Int × Bool := sorry

/--
Specification for the below_zero method ensuring:
1. Output array length is input length + 1
2. First element is 0
3. Each element is sum of previous plus operation
4. Result true means some element was negative
5. Result false means all elements non-negative
-/
theorem below_zero_spec (operations : Array Int) :
let (s, result) := below_zero operations
s.size = operations.size + 1 ∧
s[0]! = 0 ∧
(∀ i, 0 ≤ i ∧ i < s.size - 1 → s[i+1]! = s[i]! + operations[i]!) ∧
(result = true → ∃ i, 1 ≤ i ∧ i ≤ operations.size ∧ s[i]! < 0) ∧
(result = false → ∀ i, 0 ≤ i ∧ i < s.size → s[i]! ≥ 0) := sorry
