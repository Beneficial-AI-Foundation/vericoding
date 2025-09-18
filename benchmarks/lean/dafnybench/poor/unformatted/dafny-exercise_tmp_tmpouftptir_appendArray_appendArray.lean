

/-!
{
"name": "dafny-exercise_tmp_tmpouftptir_appendArray_appendArray",
"category": "Dafny Translation",
"description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_appendArray_appendArray",
"source": "Dafny",
"translation_date": "2024",
"functions": ,
"methods":
}
-/


/--
Appends two arrays of integers into a new array.
The resulting array contains all elements from the first array followed by all elements from the second array.

@param a First input array
@param b Second input array
@return c Concatenated array containing elements from a followed by elements from b
-/
def appendArray (a : Array Int) (b : Array Int) : Array Int := sorry

/--
Specification for appendArray method ensuring:
1. The length of output array equals sum of input array lengths
2. First part of output matches first input array
3. Second part of output matches second input array
-/
theorem appendArray_spec (a b c : Array Int) :
c = appendArray a b →
(c.size = a.size + b.size) ∧
(∀ i, 0 ≤ i ∧ i < a.size → a[i]! = c[i]!) ∧
(∀ i, 0 ≤ i ∧ i < b.size → b[i]! = c[a.size + i]!) := sorry
