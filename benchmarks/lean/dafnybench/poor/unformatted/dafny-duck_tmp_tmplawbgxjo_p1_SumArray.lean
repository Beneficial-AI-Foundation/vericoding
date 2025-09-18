

/-!
{
"name": "dafny-duck_tmp_tmplawbgxjo_p1_SumArray",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-duck_tmp_tmplawbgxjo_p1_SumArray",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Recursively computes the sum of elements in an array.
Given an array of integers, returns their sum.
Example:  -> 9
-/
partial def Sum_ (xs : Array Int) : Int :=
if xs.size = 0 then
0
else
Sum_ (xs.extract 0 (xs.size - 1)) + xs[xs.size - 1]!

/--
Takes an array of integers and returns their sum.
Ensures the result equals Sum applied to the input array.
-/
def SumArray (xs : Array Int) : Int := sorry

/--
Specification for SumArray ensuring it returns the correct sum
-/
theorem SumArray_spec (xs : Array Int) (s : Int) :
s = SumArray xs → s = Sum_ xs := sorry
