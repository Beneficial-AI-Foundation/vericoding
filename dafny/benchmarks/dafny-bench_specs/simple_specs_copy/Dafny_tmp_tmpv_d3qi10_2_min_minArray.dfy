// SPEC


// Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
  requires a!= null && a.Length > 0 

  ensures forall k | 0 <= k < a.Length :: m <= a[k]
  ensures exists k | 0 <= k < a.Length :: m == a[k]
{
}
