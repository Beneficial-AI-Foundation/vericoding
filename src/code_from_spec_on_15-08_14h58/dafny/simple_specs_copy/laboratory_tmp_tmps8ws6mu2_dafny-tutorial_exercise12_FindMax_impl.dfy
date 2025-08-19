//IMPL
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires 0 < a.Length
  ensures 0 <= i < a.Length
  ensures forall k: int :: 0 <= k < a.Length ==> a[k] <= a[i]
{
  i := 0;
  var j := 1;
  
  while j < a.Length
    invariant 0 <= i < a.Length
    invariant 1 <= j <= a.Length
    invariant forall k: int :: 0 <= k < j ==> a[k] <= a[i]
  {
    if a[j] > a[i] {
      i := j;
    }
    j := j + 1;
  }
}