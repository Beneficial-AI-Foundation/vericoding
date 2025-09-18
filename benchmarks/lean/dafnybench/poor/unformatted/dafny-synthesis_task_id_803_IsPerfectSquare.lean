

/-!
{
"name": "dafny-synthesis_task_id_803_IsPerfectSquare",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_803_IsPerfectSquare",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if a number is a perfect square.
Translated from Dafny method IsPerfectSquare.

@param n The input number to check
@return Whether n is a perfect square
-/
def IsPerfectSquare (n : Int) : Bool := sorry

/--
Specification for IsPerfectSquare method.
Ensures:
- If result is true, there exists an i between 0 and n where i*i = n
- If result is false, for all a where 0 < a*a < n, a*a ≠ n
-/
theorem IsPerfectSquare_spec (n : Int) :
n ≥ 0 →
let result := IsPerfectSquare n
(result = true → ∃ i : Int, 0 ≤ i ∧ i ≤ n ∧ i * i = n) ∧
(result = false → ∀ a : Int, (0 < a*a ∧ a*a < n) → a*a ≠ n) := sorry
