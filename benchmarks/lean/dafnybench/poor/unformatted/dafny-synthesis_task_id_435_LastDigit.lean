

/-!
{
"name": "dafny-synthesis_task_id_435_LastDigit",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_435_LastDigit",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
LastDigit takes a non-negative integer n and returns its last digit d.
The last digit must be between 0 and 9 inclusive and equal to n mod 10.
-/
def LastDigit (n : Int) : Int := sorry

/--
Specification for LastDigit:
- Requires n to be non-negative
- Ensures result d is between 0 and 9
- Ensures d equals n mod 10
-/
theorem LastDigit_spec (n : Int) :
n ≥ 0 →
let d := LastDigit n
0 ≤ d ∧ d < 10 ∧ n % 10 = d := sorry
