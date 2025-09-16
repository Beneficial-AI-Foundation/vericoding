

/-!
{
"name": "Clover_return_seven_M",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_return_seven_M",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Method M that takes an integer x and returns seven.
Ensures the return value is exactly 7.
-/
def M (x : Int) : Int := sorry

/--
Specification for method M stating that it always returns 7
regardless of input.
-/
theorem M_spec (x : Int) : M x = 7 := sorry
