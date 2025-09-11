


/-!
{
"name": "Clover_min_of_two_Min",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_min_of_two_Min",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Translates the Dafny Min method which returns the minimum of two integers.
The specification ensures that:
- If x ≤ y then z = x
- If x > y then z = y
-/
def MinPrime (x y : Int) : Int := sorry

/--
Specification for MinPrime method ensuring it returns the minimum of two integers
-/
theorem Min_spec (x y z : Int) :
z = MinPrime x y →
((x ≤ y → z = x) ∧
(x > y → z = y)) := sorry