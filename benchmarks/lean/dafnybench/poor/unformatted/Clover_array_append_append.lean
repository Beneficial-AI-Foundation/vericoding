


/-!
{
"name": "Clover_array_append_append",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: Clover_array_append_append",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Appends an integer to an array.

@param a The input array
@param b The integer to append
@return The resulting array with b appended
-/
def append (a : Array Int) (b : Int) : Array Int := sorry

/--
Specification for append method:
The resulting array should be equal to the input array with b appended
-/
theorem append_spec (a : Array Int) (b : Int) :
append a b = a.push b := sorry