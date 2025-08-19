// IMPL

// Question 2 (5 points)
//
// Fill in requires clause(s) that enable(s) Dafny to verify the array bounds
// in method Swap (which swaps elements i and j in array a).

method Swap (a : array?<int>, i : int, j : int)
  requires a != null && 0 <= i < a.Length && 0 <= j < a.Length// TODO
  modifies a // Dafny requires listing of objects modified in a method
{
  var temp := a[i];
  a[i] := a[j];
  a[j] := temp;
}