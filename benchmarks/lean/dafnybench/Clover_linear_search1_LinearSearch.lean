import Std


open Std.Do

/-!
{
  "name": "Clover_linear_search1_LinearSearch",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_linear_search1_LinearSearch",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
LinearSearch method that finds the first occurrence of element e in array a.
Returns index n where element is found or array length if not found.

@param a The input array to search
@param e The element to search for
@return n The index where element is found or array length if not found
-/
def LinearSearch (a : Array Int) (e : Int) : Int := sorry

/--
Specification for LinearSearch method ensuring:
1. Return value n is within array bounds
2. Either n is array length or element at index n equals e
3. All elements before index n are not equal to e
-/
theorem LinearSearch_spec (a : Array Int) (e : Int) :
  let n := LinearSearch a e
  0 ≤ n ∧ n ≤ a.size ∧
  (n = a.size ∨ a[n.toNat]! = e) ∧
  (∀ i, 0 ≤ i ∧ i < n → e ≠ a[i.toNat]!) := sorry

end DafnyBenchmarks
