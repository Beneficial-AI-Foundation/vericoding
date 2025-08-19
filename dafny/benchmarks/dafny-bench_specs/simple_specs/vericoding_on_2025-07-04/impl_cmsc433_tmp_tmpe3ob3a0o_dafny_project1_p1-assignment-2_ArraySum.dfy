//IMPL 

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
  requires a.Length == b.Length
  ensures c.Length == a.Length && 
    forall i : int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i]
{
  c := new int[a.Length];
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall j : int :: 0 <= j < i ==> c[j] == a[j] + b[j]
  {
    c[i] := a[i] + b[i];
    i := i + 1;
  }
}