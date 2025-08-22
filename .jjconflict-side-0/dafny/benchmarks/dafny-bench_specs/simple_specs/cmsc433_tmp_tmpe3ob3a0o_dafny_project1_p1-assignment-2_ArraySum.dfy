// SPEC

// Question 4 (5 points)
//
// Give ensures clause(s) asserting that the return value has the same
// length as array a and contains as its elements the sum of the
// corresponding elements in arrays a and b.

method ArraySum (a : array<int>, b : array<int>) returns (c : array<int>)
  requires a.Length == b.Length
  ensures c.Length == a.Length && 
    forall i : int :: 0 <= i < c.Length ==> c[i] == a[i] + b[i] // TODO
{
}
