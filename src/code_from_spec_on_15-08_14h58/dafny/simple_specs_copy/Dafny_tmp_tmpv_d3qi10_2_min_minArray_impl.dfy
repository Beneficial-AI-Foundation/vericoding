//IMPL 

// Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
  /* code modified by LLM (iteration 1): removed null check since array<int> is non-null type */
  requires a.Length > 0 

  ensures forall k | 0 <= k < a.Length :: m <= a[k]
  ensures exists k | 0 <= k < a.Length :: m == a[k]
{
  m := a[0];
  var i := 1;
  
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall k | 0 <= k < i :: m <= a[k]
    invariant exists k | 0 <= k < i :: m == a[k]
  {
    if a[i] < m {
      m := a[i];
    }
    i := i + 1;
  }
}