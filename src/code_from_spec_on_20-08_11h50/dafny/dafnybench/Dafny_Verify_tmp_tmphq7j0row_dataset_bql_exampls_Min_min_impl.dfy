// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method min(a: array<int>, n : int) returns (min : int)
    requires 0 < n <= a.Length;
    ensures (exists i : int :: 0 <= i && i < n && a[i] == min);
    ensures (forall i : int :: 0 <= i && i < n ==> a[i] >= min);
// </vc-spec>
// <vc-code>
{
  min := a[0];
  var j := 1;
  
  while j < n
    invariant 1 <= j <= n;
    invariant (exists i : int :: 0 <= i && i < j && a[i] == min);
    invariant (forall i : int :: 0 <= i && i < j ==> a[i] >= min);
  {
    if a[j] < min {
      min := a[j];
    }
    j := j + 1;
  }
}
// </vc-code>