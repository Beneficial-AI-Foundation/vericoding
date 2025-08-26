method arrayUpToN(n: int) returns (a: array<int>)
    requires n >= 0
    ensures a.Length == n
    ensures forall j :: 0 < j < n ==> a[j] >= 0
    ensures forall j, k : int :: 0 <= j <= k < n ==> a[j] <= a[k]
// </vc-spec>
// <vc-code>
{
  a := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 < j < i ==> a[j] >= 0
    invariant forall j, k :: 0 <= j <= k < i ==> a[j] <= a[k]
    invariant forall j :: 0 <= j < i ==> a[j] == j
  {
    a[i] := i;
    assert forall j :: 0 <= j <= i ==> a[j] == j;
    i := i + 1;
    // The key insight: after setting a[i-1] := i-1, we need to show that
    // for all j, k with 0 <= j <= k < i, we have a[j] <= a[k]
    // Since a[j] = j and a[k] = k, and j <= k, we have a[j] <= a[k]
  }
}
// </vc-code>