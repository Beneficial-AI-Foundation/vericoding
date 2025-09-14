

// <vc-helpers>
lemma MaxLemma(a: array<int>, lo: int, hi: int, m: int)
  requires 0 <= lo <= hi <= a.Length
  requires lo <= m < hi
  requires forall k :: lo <= k < hi ==> a[k] <= a[m]
  ensures forall k :: lo <= k < hi ==> a[k] <= a[m]
{
}
// </vc-helpers>

// <vc-spec>
method FindMax(a: array<int>) returns (i: int)
  // Annotate this method with pre- and postconditions
  // that ensure it behaves as described.
  requires a.Length > 0
  ensures 0<= i < a.Length
  ensures forall k :: 0 <= k < a.Length ==> a[k] <= a[i]
// </vc-spec>
// <vc-code>
{
  i := 0;
  var j: int := 1;
  
  while j < a.Length
    invariant 0 <= i < a.Length
    invariant 1 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] <= a[i]
  {
    if a[j] > a[i] {
      i := j;
    }
    j := j + 1;
  }
}
// </vc-code>

