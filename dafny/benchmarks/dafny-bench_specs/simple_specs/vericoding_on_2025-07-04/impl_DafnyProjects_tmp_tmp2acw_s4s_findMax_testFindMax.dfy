//ATOM

// Finds the maximum value in a non-empty array.
method findMax(a: array<real>) returns (max: real)
 requires a.Length > 0
 ensures exists k :: 0 <= k < a.Length && max == a[k]
 ensures forall k :: 0 <= k < a.Length ==> max >= a[k]
{
  /* code modified by LLM (iteration 1): Fixed syntax error in assume statement and implemented proper max finding logic */
  max := a[0];
  var i := 1;
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant exists k :: 0 <= k < i && max == a[k]
    invariant forall k :: 0 <= k < i ==> max >= a[k]
  {
    if a[i] > max {
      max := a[i];
    }
    i := i + 1;
  }
}


// SPEC


// Test cases checked statically.
method testFindMax() {
}