

/-!
{
"name": "dafny-synthesis_task_id_598_IsArmstrong",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_598_IsArmstrong",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Checks if a number is an Armstrong number.
An Armstrong number is a number that equals the sum of its digits each raised to the power of 3.
Input must be between 100 and 999 inclusive.

@param n The number to check
@return True if n is an Armstrong number, false otherwise
-/
def IsArmstrong (n : Int) : Bool := sorry

/--
Specification for IsArmstrong:
- Requires n to be between 100 and 999
- Ensures result is true if and only if n equals the sum of its digits cubed
-/
theorem IsArmstrong_spec (n : Int) :
100 ≤ n ∧ n < 1000 →
IsArmstrong n = (n = ((n / 100) * (n / 100) * (n / 100) +
((n / 10) % 10) * ((n / 10) % 10) * ((n / 10) % 10) +
(n % 10) * (n % 10) * (n % 10))) := sorry
