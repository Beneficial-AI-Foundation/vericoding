/* 
* Formal verification of a simple algorithm to find the maximum value in an array.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Finds the maximum value in a non-empty array.
// SPEC 

// Finds the maximum value in a non-empty array.
method findMax(a: array<real>) returns (max: real)
  requires a.Length > 0
  ensures exists k :: 0 <= k < a.Length && max == a[k]
  ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{
}



// Test cases checked statically.
//ATOM_PLACEHOLDER_testFindMax





